import OAI.Combinatorics.MatchingPSD.MatrixBounds

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace PerfectMatchingPSD
open Matrix MatchingSmoothing
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable
variable {R : Type u_1} {X : Type u_2} [Fintype R] [DecidableEq R] [Fintype X]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_eq (f : X → Matrix R R ℝ) :
    (𝔼 x, f x) = ((Fintype.card X : ℝ)⁻¹) • (∑ x, f x) := by
  ext i j
  simp [Finset.expect, NNRat.smul_def]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_apply (f : X → Matrix R R ℝ) (u v : R) :
    (𝔼 x, f x) u v = 𝔼 x, f x u v := by
  rw [matrix_expect_eq, Fintype.expect_eq_sum_div_card]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, div_eq_inv_mul]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_psd (f : X → Matrix R R ℝ) (hf : ∀ x, (f x).PosSemidef) :
    (𝔼 x, f x).PosSemidef := by
  rw [matrix_expect_eq]
  exact (matrix_sum_psd Finset.univ f (fun x _ => hf x)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma trace_mul_expect (Q : Matrix R R ℝ) (f : X → Matrix R R ℝ) :
    (Q * (𝔼 x, f x)).trace = 𝔼 x, (Q*f x).trace := by
  rw [matrix_expect_eq, mul_smul_comm, Matrix.trace_smul,
    Finset.mul_sum, Matrix.trace_sum, Fintype.expect_eq_sum_div_card]
  change (Fintype.card X : ℝ)⁻¹ * _ = _ / Fintype.card X
  rw [div_eq_inv_mul]

lemma expect_abs_bound (f : X → ℝ) {b : ℝ} (hb : 0 ≤ b) (hf : ∀ x, |f x| ≤ b) :
    |𝔼 x, f x| ≤ b := by
  by_cases hX : Nonempty X
  · let := hX
    have h0 (x : X) : -b ≤ f x := (abs_le.mp (hf x)).1
    have h1 (x : X) : f x ≤ b := (abs_le.mp (hf x)).2
    apply abs_le.mpr
    constructor
    · simpa using Finset.expect_le_expect (s := Finset.univ) (fun x _ => h0 x)
    · simpa using Finset.expect_le_expect (s := Finset.univ) (fun x _ => h1 x)
  · have : IsEmpty X := not_nonempty_iff.mp hX
    simpa using hb

section CellMatrices
variable {A : Type u_3} {B : Type u_4} {C : Type u_5} {I : Type u_6} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

noncomputable def extensionMatrix (i : I)
    (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (M : Pairing ((A ⊕ B) ⊕ C)) : Matrix R R ℝ :=
  𝔼 N : {j : I // j ≠ i} → Pairing C, Bf (extendLocal i M N)

noncomputable def cellMatrix (i : I)
    (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (x : Fin 3 → ℝ) : Matrix R R ℝ :=
  𝔼 M : {M : Pairing ((A ⊕ B) ⊕ C) // crossVector threeColor M = x}, extensionMatrix i Bf M.1

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_apply (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (x : Fin 3 → ℝ) (u v : R) :
    cellMatrix i Bf x u v = cellAverage i (fun M => Bf M u v) x := by
  rw [cellAverage, predicateAverage_eq_expect]
  simp only [cellMatrix, extensionMatrix, extensionAverage, matrix_expect_apply]
  apply Finset.expect_congr (by ext; simp)
  intro M _
  rfl

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_psd (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (hB : ∀ M, (Bf M).PosSemidef) (x : Fin 3 → ℝ) :
    (cellMatrix i Bf x).PosSemidef := by
  apply matrix_expect_psd
  intro M
  apply matrix_expect_psd
  intro N
  exact hB _

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_star (i j : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (x : ℝ) : cellMatrix i Bf ![x,0,0] = cellMatrix j Bf ![x,0,0] := by
  ext u v
  simp only [cellMatrix_apply, cellAverage_star]

lemma trace_cellMatrix (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (Q : Matrix R R ℝ) (x : Fin 3 → ℝ) :
    (Q*cellMatrix i Bf x).trace = cellAverage i (fun M => (Q*Bf M).trace) x := by
  rw [cellAverage, predicateAverage_eq_expect, cellMatrix, trace_mul_expect]
  apply Finset.expect_congr (by ext; simp)
  intro M _
  exact trace_mul_expect Q _

omit [Fintype A] [Fintype B] in
lemma extensionAverage_sq_bound (i : I)
    (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (hB : ∀ M, (Bf M).PosSemidef) {b : ℝ} (hb : 0 ≤ b)
    (htr : ∀ M, (Bf M).trace ≤ b) (u v : R) (M : Pairing ((A ⊕ B) ⊕ C)) :
    (extensionAverage i (fun N => Bf N u v) M)^2 ≤ b^2 := by
  have he := expect_abs_bound (fun N => Bf (extendLocal i M N) u v) hb
    (fun N => (posSemidef_entry_abs_le_trace (hB _) u v).trans (htr _))
  have hex : extensionAverage i (fun N => Bf N u v) M =
      𝔼 N : {j : I // j ≠ i} → Pairing C, Bf (extendLocal i M N) u v := by
    apply Finset.expect_congr (by ext; simp)
    intro N _
    rfl
  rw [hex]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr he

end CellMatrices
end PerfectMatchingPSD

end OAI
