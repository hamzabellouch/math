import OAI.Analysis.Cuntz.Regularization
import OAI.Analysis.Cuntz.Squares

namespace OAI

noncomputable section

/-! Regularized dimension states and subadditivity. -/

section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace CuntzDimensionState

/-- A common smaller cutoff controls two independent cutoff thresholds. -/
theorem cutoff_value_add_le_regularized (d : CuntzDimensionState A)
    (a b : CuntzPositiveMatrix A) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    d.value (a.cutoff ε) + d.value (b.cutoff δ) ≤ d.regularized (a.add b) := by
  have hp := lt_min hε hδ
  calc
    _ ≤ d.value (a.cutoff (min ε δ)) + d.value (b.cutoff (min ε δ)) :=
      add_le_add (d.cutoff_value_antitone a (min_le_left _ _))
        (d.cutoff_value_antitone b (min_le_right _ _))
    _ = d.value ((a.add b).cutoff (min ε δ)) := by rw [CuntzPositiveMatrix.cutoff_add, d.value_add]
    _ ≤ _ := d.cutoff_value_le_regularized _ hp

theorem regularized_add (d : CuntzDimensionState A) (a b : CuntzPositiveMatrix A) :
    d.regularized (a.add b) = d.regularized a + d.regularized b := by
  apply le_antisymm
  · apply d.regularized_le
    intro ε hε
    rw [CuntzPositiveMatrix.cutoff_add, d.value_add]
    exact add_le_add (d.cutoff_value_le_regularized a hε) (d.cutoff_value_le_regularized b hε)
  · apply (le_sub_iff_add_le).mp
    apply d.regularized_le a
    intro ε hε
    apply (le_sub_iff_add_le).mpr
    apply (le_sub_iff_add_le').mp
    apply d.regularized_le b
    intro δ hδ
    apply (le_sub_iff_add_le').mpr
    exact d.cutoff_value_add_le_regularized a b hε hδ

/-- The regularization descends to an additive, normalized monotone state
on the actual Cuntz monoid. -/
def regularize (d : CuntzDimensionState A) : CuntzDimensionState A where
  state := {
    toFun := Quotient.lift d.regularized (fun _ _ h => d.regularized_eq h)
    map_zero' := d.regularized_zero
    map_add' := by
      intro a b
      induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
      exact d.regularized_add a b }
  monotone := by
    intro a b h
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    exact d.regularized_mono ((cuntzClass_le a b).mp h)
  normalized := by
    change d.regularized (.unit 1) = 1
    exact_mod_cast d.regularized_unit 1

@[simp] theorem regularize_value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.regularize.value a = d.regularized a := rfl

theorem regularize_lowerSemicontinuous (d : CuntzDimensionState A) (n : ℕ) :
    LowerSemicontinuous (fun a : {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} =>
      d.regularize.value ⟨n, CStarMatrix.ofMatrix.symm a.val, a.property⟩) :=
  d.regularized_lowerSemicontinuous n

theorem regularize_idempotent_value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.regularize.regularize.value a = d.regularize.value a :=
  d.regularized_idempotent a

/-- Square swapping for the regularization follows from the proved
Cuntz equivalence, even for unequal matrix sizes. -/
theorem regularized_rectangular_gram (d : CuntzDimensionState A) {n m : ℕ}
    (v : Matrix (Fin n) (Fin m) A)
    (hv : 0 ≤ CStarMatrix.ofMatrix (v*v.conjTranspose))
    (hw : 0 ≤ CStarMatrix.ofMatrix (v.conjTranspose*v)) :
    d.regularized ⟨n, v*v.conjTranspose, hv⟩ =
      d.regularized ⟨m, v.conjTranspose*v, hw⟩ :=
  d.regularized_eq (cuntzEquivalent_rectangular_gram v)

end CuntzDimensionState
end Kaplansky

end

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- The row of two identities compresses the diagonal block to the ordinary sum. -/
theorem cuntzLE_sum_block {n : ℕ} (a b : Matrix (Fin n) (Fin n) A) :
    CuntzLE (a+b) (cuntzBlock a b) := by
  let v := Matrix.fromCols (1 : Matrix (Fin n) (Fin n) A) (1 : Matrix (Fin n) (Fin n) A)
  have h : v * cuntzBlock a b * v.conjTranspose = a+b := by
    simp [v, cuntzBlock, Matrix.fromCols_mul_fromBlocks,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
  simpa only [h] using CuntzLE.exact (cuntzBlock a b) v

namespace CuntzDimensionState

/-- Dimension is subadditive for positive sums, without a commutation hypothesis. -/
theorem value_sum_le (d : CuntzDimensionState A) {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    d.value ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ ≤
      d.value ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.value ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  let pa : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩
  let pb : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩
  rw [← d.value_add pa pb]
  apply d.value_mono
  exact (cuntzLE_sum_block _ _).trans (CuntzPositiveMatrix.add_equiv pa pb).symm.1

theorem regularized_sum_le (d : CuntzDimensionState A) {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    d.regularized ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ ≤
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ :=
  d.regularize.value_sum_le a b ha hb

theorem regularized_orthogonal_add (d : CuntzDimensionState A) {n : ℕ}
    (a b : CStarMatrix (Fin n) (Fin n) A) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a*b=0) :
    d.regularized ⟨n, CStarMatrix.ofMatrix.symm (a+b), add_nonneg ha hb⟩ =
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ +
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ :=
  d.regularize.value_orthogonal_add n a b ha hb hab

end CuntzDimensionState
end Kaplansky

end

end OAI
