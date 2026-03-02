/-
This is a project for AI for Formal Proof Winter Camp, Qiuzhen College, 2026.
This file formalizes binary Golay code.
Author: Tiancheng Chu (Group 4)
-/
import Mathlib

/-!
# Binary Golay code

We work over `GF(2) = ZMod 2` and model length-24 binary words as `Fin 24 → ZMod 2`.
Following the definition: a binary (12,24)-code is called a (binary) Golay code
if it is doubly even, self-dual, and has minimal weight 8.

This file provides:
* a Hamming weight for vectors;
* the standard bilinear form `<x,y> = ∑ i, x i * y i`;
* a predicate `IsExtendedBinaryGolayCode` on submodules of `V = (Fin 24 → ZMod 2)`.
-/

namespace Golay

section Definitions

/-- The binary field `GF(2)` as `ZMod 2`. -/
abbrev 𝔽₂ : Type := ZMod 2

/-- Length-24 binary words as functions `Fin 24 → 𝔽₂`. -/
abbrev V24 : Type := Fin 24 → 𝔽₂

/-- Message space (12-bit). -/
abbrev Msg : Type := Fin 12 → 𝔽₂

/-- Hamming weight: the number of nonzero coordinates. -/
def weight (v : V24) : Nat :=
  (Finset.univ.filter (fun i : Fin 24 => v i ≠ 0)).card

@[simp] lemma weight_zero : weight (0 : V24) = 0 := by simp [weight]

/-- The support as a finset of coordinates. -/
def support (v : V24) : Finset (Fin 24) :=
  Finset.univ.filter (fun i : Fin 24 => v i ≠ 0)

@[simp] lemma support_def (v : V24) :
    support v = Finset.univ.filter (fun i : Fin 24 => v i ≠ 0) := rfl

@[simp] lemma weight_eq_card_support (v : V24) : weight v = (support v).card := rfl

end Definitions

section Bilin

/--
The standard bilinear form on `V24`: `b x y = ∑ i, x i * y i` over `𝔽₂`.
This matches the "orthonormal basis" bilinear form with respect to the standard coordinate basis.
-/
def stdBilin : LinearMap.BilinForm 𝔽₂ V24 := by
  -- `BilinForm R M := M →ₗ[R] M →ₗ[R] R`
  refine
    LinearMap.mk₂ (R := 𝔽₂) (M := V24)
      (fun x y => ∑ i : Fin 24, x i * y i)
      ?map_add_left ?map_smul_left ?map_add_right ?map_smul_right
  · intro x₁ x₂ y
    have h :
        (fun i : Fin 24 => (x₁ i + x₂ i) * y i)
          = (fun i : Fin 24 => x₁ i * y i + x₂ i * y i) := by
      funext i
      simp only [add_mul]
    simp only [h, Finset.sum_add_distrib, Pi.add_apply]
  · intro a x y
    have h :
        (fun i : Fin 24 => (a • x) i * y i) = (fun i : Fin 24 => a * (x i * y i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, mul_comm]
    calc
      (∑ i : Fin 24, (a • x) i * y i)
          = ∑ i : Fin 24, a * (x i * y i) := by
          simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      _   = a * ∑ i : Fin 24, (x i * y i) := by
            simp [Finset.mul_sum]
  · intro x y₁ y₂
    have h :
        (fun i : Fin 24 => x i * (y₁ i + y₂ i))
          = (fun i : Fin 24 => x i * y₁ i + x i * y₂ i) := by
      funext i
      simp [mul_add]
    simp [h, Finset.sum_add_distrib]
  · intro a x y
    have h :
        (fun i : Fin 24 => x i * (a • y) i) = (fun i : Fin 24 => a * (x i * y i)) := by
      funext i
      simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    calc
      (∑ i : Fin 24, x i * (a • y) i)
          = ∑ i : Fin 24, a * (x i * y i) := by simp [mul_left_comm]
      _   = a * ∑ i : Fin 24, (x i * y i) := by
            simp only [Finset.mul_sum]

/-- Orthogonal complement of a submodule w.r.t. `stdBilin`. -/
abbrev orth (C : Submodule 𝔽₂ V24) : Submodule 𝔽₂ V24 :=
  stdBilin.orthogonal C

end Bilin

section Predicates

/-- "Even code": all codewords have even Hamming weight. -/
def IsEven (C : Submodule 𝔽₂ V24) : Prop :=
  ∀ c : V24, c ∈ C → weight c % 2 = 0

/-- "Doubly even code": all codewords have Hamming weight divisible by 4. -/
def IsDoublyEven (C : Submodule 𝔽₂ V24) : Prop :=
  ∀ c : V24, c ∈ C → weight c % 4 = 0

lemma doublyEven_implies_even {C : Submodule 𝔽₂ V24} (h : IsDoublyEven C) : IsEven C := by
  intro c hc
  have hmod : weight c % 4 = 0 := h c hc
  have h4 : 4 ∣ weight c := Nat.dvd_of_mod_eq_zero hmod
  have h2 : 2 ∣ weight c := dvd_trans (by decide : 2 ∣ 4) h4
  exact Nat.mod_eq_zero_of_dvd h2

/--
Lower-bound version of "minimal weight is `d`":
every nonzero codeword has weight at least `d`.
-/
def MinWeightAtLeast (C : Submodule 𝔽₂ V24) (d : Nat) : Prop :=
  ∀ c : V24, c ∈ C → c ≠ 0 → d ≤ weight c

/-- Self-duality with respect to the standard bilinear form. -/
def IsSelfDual (C : Submodule 𝔽₂ V24) : Prop :=
  C = orth C

/--
Specification of the extended binary Golay code:
a binary (12,24)-code which is doubly even, self-dual, and has minimal weight 8.
-/
structure IsExtendedBinaryGolayCode (C : Submodule 𝔽₂ V24) : Prop where
  finrank_eq : Module.finrank 𝔽₂ C = 12
  self_dual : IsSelfDual C
  doubly_even : IsDoublyEven C
  min_weight : MinWeightAtLeast C 8

/-- A bundled "some submodule together with a proof it is an extended binary Golay code". -/
def ExtendedBinaryGolayCode : Type :=
  { C : Submodule 𝔽₂ V24 // IsExtendedBinaryGolayCode C }

end Predicates

section Consequences

/-- If `C` is an extended binary Golay code, then it is even. -/
lemma golay_even {C : Submodule 𝔽₂ V24} (h : IsExtendedBinaryGolayCode C) : IsEven C :=
  doublyEven_implies_even h.doubly_even

/-- Under `IsExtendedBinaryGolayCode`, nonzero codewords have weight at least 8. -/
lemma golay_weight_ge_eight {C : Submodule 𝔽₂ V24} (h : IsExtendedBinaryGolayCode C)
    {c : V24} (hc : c ∈ C) (hne : c ≠ 0) : 8 ≤ weight c :=
  h.min_weight c hc hne

end Consequences

/-
We store the 12×24 binary matrix as a `List (List Nat)` and index into it,
then coerce entries `0/1` into `𝔽₂` via `(n : 𝔽₂)`.
-/
section GeneratorMatrix

/-- The 12×24 generator matrix data (as `0/1` naturals). -/
def GList : List (List Nat) :=
[
  [1,0,0,0,0,0,0,0,0,0,0,0,  1,0,0,1,1,1,1,1,0,0,0,1],
  [0,1,0,0,0,0,0,0,0,0,0,0,  0,1,0,0,1,1,1,1,1,0,1,0],
  [0,0,1,0,0,0,0,0,0,0,0,0,  0,0,1,0,0,1,1,1,1,1,0,1],
  [0,0,0,1,0,0,0,0,0,0,0,0,  1,0,0,1,0,0,1,1,1,1,1,0],
  [0,0,0,0,1,0,0,0,0,0,0,0,  1,1,0,0,1,0,0,1,1,1,0,1],
  [0,0,0,0,0,1,0,0,0,0,0,0,  1,1,1,0,0,1,0,0,1,1,1,0],
  [0,0,0,0,0,0,1,0,0,0,0,0,  1,1,1,1,0,0,1,0,0,1,0,1],
  [0,0,0,0,0,0,0,1,0,0,0,0,  1,1,1,1,1,0,0,1,0,0,1,0],
  [0,0,0,0,0,0,0,0,1,0,0,0,  0,1,1,1,1,1,0,0,1,0,0,1],
  [0,0,0,0,0,0,0,0,0,1,0,0,  0,0,1,1,1,1,1,0,0,1,1,0],
  [0,0,0,0,0,0,0,0,0,0,1,0,  0,1,0,1,0,1,0,1,0,1,1,1],
  [0,0,0,0,0,0,0,0,0,0,0,1,  1,0,1,0,1,0,1,0,1,0,1,1]
]

/-- Sanity check: `GList` has 12 rows. -/
lemma GList_length : GList.length = 12 := by decide

/-- All rows in `GList` have length 24. -/
lemma GList_all_rows_length :
    ∀ row ∈ GList, row.length = 24 := by decide

lemma GList_row_length (i : Fin 12) :
    (GList.get ⟨i.1, by simp [GList_length]⟩).length = 24 := by
  have hmem :
      (GList.get ⟨i.1, by simp [GList_length]⟩) ∈ GList :=
    List.get_mem GList ⟨i.1, by simp [GList_length]⟩
  exact GList_all_rows_length _ hmem

/-- Access the `(i,j)`-entry of the raw Nat matrix (`0/1`). -/
def GEntryNat (i : Fin 12) (j : Fin 24) : Nat :=
  let row := GList.get ⟨i.1, by simp [GList_length]⟩
  have hlen : row.length = 24 := by
    simpa [row] using (GList_row_length i)
  row.get ⟨j.1, by simp [hlen]⟩

/-- The generator matrix over `𝔽₂`. -/
def G : Matrix (Fin 12) (Fin 24) 𝔽₂ :=
  fun i j => (GEntryNat i j : 𝔽₂)

end GeneratorMatrix

/-! Define the encoder `enc` and the code `C = range(enc)`. -/
section Encoding

/-- Linear encoder from 12-bit messages to 24-bit codewords via the generator matrix. -/
def enc : Msg →ₗ[𝔽₂] V24 := by
  refine
    { toFun := fun m => fun j => ∑ i : Fin 12, m i * G i j
      map_add' := ?_
      map_smul' := ?_ }
  · intro m₁ m₂
    funext j
    simp [Finset.sum_add_distrib, add_mul]
  · intro a m
    funext j
    simp [Finset.mul_sum, mul_left_comm, mul_comm]

/-- The code as the range of `enc`. -/
def C : Submodule 𝔽₂ V24 := LinearMap.range enc

/-- Convenient membership characterization. -/
lemma mem_C_iff {c : V24} : c ∈ C ↔ ∃ m : Msg, enc m = c := Iff.rfl

end Encoding

/-!
Properties to prove:
1) Prove `finrank C = 12` by proving `enc` is injective and some computation.
2) Prove `self_dual` using
  (a) self-orthogonality: `C ≤ orth C` (often from `G * Gᵀ = 0`)
  (b) dimension count: `finrank C = 12` and `finrank (orth C) = 24 - finrank C`.
3) Prove `doubly_even` and `min_weight` by finite enumeration on `Msg` (4096 cases),
-/

section Proofs

/-! (1) `finrank = 12` -/

/-- Embed `Fin 12` into `Fin 24` as the first 12 coordinates. -/
def j12 (k : Fin 12) : Fin 24 :=
  ⟨k.1, lt_trans k.2 (by decide : (12 : Nat) < 24)⟩

/--
The left 12×12 block of `G` is the identity:
`G i (j12 k) = if i = k then 1 else 0`.
-/
lemma G_leftBlock_is_id (i k : Fin 12) :
    G i (j12 k) = (if i = k then (1 : 𝔽₂) else 0) := by
  fin_cases i <;> fin_cases k <;> decide

/-- On the first 12 coordinates, the encoder returns the message bits. -/
lemma enc_coord_left (m : Msg) (k : Fin 12) :
    (enc m) (j12 k) = m k := by
  have hcoord :
      (enc m) (j12 k) = ∑ i : Fin 12, m i * G i (j12 k) := by
    simp [enc]
  calc
    (enc m) (j12 k)
        = ∑ i : Fin 12, m i * G i (j12 k) := hcoord
    _   = ∑ i : Fin 12, (if i = k then m k else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases h : i = k
          · subst h
            simp [G_leftBlock_is_id]
          · simp [G_leftBlock_is_id, h]
    _   = m k := by simp

/-- The encoder is injective (because the left block is `I₁₂`). -/
lemma enc_injective : Function.Injective enc := by
  intro m₁ m₂ h
  funext k
  have hk : (enc m₁) (j12 k) = (enc m₂) (j12 k) :=
    congrArg (fun v => v (j12 k)) h
  simpa [enc_coord_left] using hk

/-- `finrank` of the code is 12. -/
lemma finrank_C : Module.finrank 𝔽₂ C = 12 := by
  have hker : LinearMap.ker enc = ⊥ :=
    LinearMap.ker_eq_bot_of_injective enc_injective
  have hker0 : Module.finrank 𝔽₂ (LinearMap.ker enc) = 0 := by
    simp [hker]
  have hmsg : Module.finrank 𝔽₂ Msg = 12 := by
    simp [Msg]
  have h :=
    LinearMap.finrank_range_add_finrank_ker enc
  have : Module.finrank 𝔽₂ (LinearMap.range enc) + 0 = 12 := by
    simpa [hker0, hmsg] using h
  have hrange : Module.finrank 𝔽₂ (LinearMap.range enc) = 12 := by
    simpa [Nat.add_zero] using this
  simpa [C] using hrange

/-! (2) Self-dual
Strategy:
* Prove `C ≤ orth C` (self-orthogonal),
* then compare `finrank` to get equality.
-/

/-- Self-orthogonality: `C ≤ orth C`. -/
lemma C_le_orth : C ≤ orth C := by
  let row : Fin 12 → V24 := fun i => fun j => G i j
  have row_orth : ∀ i k : Fin 12, stdBilin (row i) (row k) = 0 := by
    intro i k
    fin_cases i <;> fin_cases k <;> decide
  have enc_eq_sum_rows : ∀ m : Msg, enc m = ∑ i : Fin 12, m i • row i := by
    intro m
    ext j
    simp [enc, row, Pi.smul_apply, smul_eq_mul]
  have enc_orth : ∀ m₁ m₂ : Msg, stdBilin (enc m₁) (enc m₂) = 0 := by
    intro m₁ m₂
    simp [enc_eq_sum_rows, row_orth]
  -- Conclude `C ≤ orth C`.
  intro c hc
  rcases (mem_C_iff.mp hc) with ⟨m, rfl⟩
  simp only [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rcases (mem_C_iff.mp hy) with ⟨m', rfl⟩
  exact enc_orth m' m

/-- Self-duality: `C = orth C`. -/
lemma self_dual_C : IsSelfDual C := by
  sorry

/-!
(3) Doubly even and (4) minimal weight ≥ 8 via finite enumeration
Reduce `c ∈ C` to `c = enc m`, then use `native_decide` over finite types.
-/

/-- Doubly even on the range: `∀ m, weight (enc m) % 4 = 0`. -/
lemma doubly_even_C : IsDoublyEven C := by
  have hall : ∀ m : Msg, weight (enc m) % 4 = 0 := by
    native_decide
  intro c hc
  rcases (mem_C_iff.mp hc) with ⟨m, rfl⟩
  exact hall m

/-- Minimal weight ≥ 8: all nonzero codewords have weight at least 8. -/
lemma min_weight_C : MinWeightAtLeast C 8 := by
  intro c hc hne
  rcases (mem_C_iff.mp hc) with ⟨m, rfl⟩
  -- Now: `8 ≤ weight (enc m)` from `enc m ≠ 0`.
  -- TODO: set up `hall : ∀ m, enc m ≠ 0 → 8 ≤ weight (enc m)` via `native_decide`.
  sorry

/-- Bundle everything: the concrete code `C` is an extended binary Golay code. -/
theorem C_is_extended_binary_golay : IsExtendedBinaryGolayCode C := by
  refine
    { finrank_eq := finrank_C
      self_dual := self_dual_C
      doubly_even := doubly_even_C
      min_weight := min_weight_C }

end Proofs

end Golay
