import OAI.Analysis.Triangular.Certificate.AtomicResidualPlus
import OAI.Analysis.Triangular.Certificate.AtomicResidualMinus
import OAI.Analysis.Triangular.Certificate.InverseEnclosure

namespace OAI

/-!
The finite interpolation blocks in *An atomic certificate for triangular-lattice
universal optimality* are I−R and I+R. Their rational candidates have right
residuals E=I−AB. The correction B+BE and a second-order remainder bound give
the entrywise enclosures of the actual inverses.
-/

noncomputable section

namespace AtomicTriangular.FiniteCertificate.AtomicMatrix
open AtomicTriangular.Interval AtomicTriangular.MatrixBounds

lemma plusResidual_norm :
    matNorm (1 - (1 - RValue) * candidateValue 0) ≤
      (plusEpsilonNumerator : ℝ) / (scale : ℝ) := by
  simpa only [systemValue, Fin.val_zero, ite_true] using
    matrixNorm_bound (residual_mem 0) residualPlus_bound

lemma minusResidual_norm :
    matNorm (1 - (1 + RValue) * candidateValue 1) ≤
      (minusEpsilonNumerator : ℝ) / (scale : ℝ) := by
  simpa only [systemValue, Fin.val_one, ite_eq_right (by decide : ¬ (1 : ℕ) = 0)] using
    matrixNorm_bound (residual_mem 1) residualMinus_bound

/-- Both finite interpolation blocks are nonsingular. -/
theorem sub_isUnit : IsUnit (1 - RValue) :=
  isUnit_of_right_residual _ _ (plusResidual_norm.trans_lt plus_epsilon_lt_one)

theorem add_isUnit : IsUnit (1 + RValue) :=
  isUnit_of_right_residual _ _ (minusResidual_norm.trans_lt minus_epsilon_lt_one)

theorem sub_inverse_two_sided :
    (1 - RValue) * (1 - RValue)⁻¹ = 1 ∧ (1 - RValue)⁻¹ * (1 - RValue) = 1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det (1 - RValue)).mp sub_isUnit
  exact ⟨Matrix.mul_nonsing_inv _ hd, Matrix.nonsing_inv_mul _ hd⟩

theorem add_inverse_two_sided :
    (1 + RValue) * (1 + RValue)⁻¹ = 1 ∧ (1 + RValue)⁻¹ * (1 + RValue) = 1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det (1 + RValue)).mp add_isUnit
  exact ⟨Matrix.mul_nonsing_inv _ hd, Matrix.nonsing_inv_mul _ hd⟩

private lemma inverseEnclosure_mem_of_bounds (side : Fin 2) (k e : ℝ)
    (hB : matNorm (candidateValue side) ≤ k)
    (hE : matNorm (1 - systemValue side * candidateValue side) ≤ e)
    (he0 : 0 ≤ e) (he : e < 1)
    (htail : k * e^2 / (1-e) ≤ 2 / 10^17) (i j : Fin 20) :
    (inverseEnclosure side i j).Mem ((systemValue side)⁻¹ i j) := by
  apply RI.mem_widen (residualCorrection_mem side i j)
  have h := inverse_entry_second_order_right_residual_bound
    (systemValue side) (candidateValue side) k e hB hE he0 he i j
  exact (h.trans htail).trans_eq (by norm_num [scale])

/-- The original corrected rational enclosure contains every inverse entry. -/
theorem sub_inverse_enclosure (i j : Fin 20) :
    (inverseEnclosure 0 i j).Mem ((1 - RValue)⁻¹ i j) := by
  have hB := matrixNorm_bound (candidate_mem 0) candidatePlus_bound
  simpa only [systemValue, Fin.val_zero, ite_true] using
    inverseEnclosure_mem_of_bounds 0
      ((plusNormNumerator : ℝ) / (scale : ℝ))
      ((plusEpsilonNumerator : ℝ) / (scale : ℝ))
      hB (by simpa only [systemValue, Fin.val_zero, ite_true] using plusResidual_norm)
      plus_epsilon_nonneg plus_epsilon_lt_one plus_second_order_bound i j

theorem add_inverse_enclosure (i j : Fin 20) :
    (inverseEnclosure 1 i j).Mem ((1 + RValue)⁻¹ i j) := by
  have hB := matrixNorm_bound (candidate_mem 1) candidateMinus_bound
  simpa only [systemValue, Fin.val_one, ite_eq_right (by decide : ¬ (1 : ℕ) = 0)] using
    inverseEnclosure_mem_of_bounds 1
      ((minusNormNumerator : ℝ) / (scale : ℝ))
      ((minusEpsilonNumerator : ℝ) / (scale : ℝ))
      hB (by simpa only [systemValue, Fin.val_one,
        ite_eq_right (by decide : ¬ (1 : ℕ) = 0)] using minusResidual_norm)
      minus_epsilon_nonneg minus_epsilon_lt_one minus_second_order_bound i j

/-- The six finite conclusions for the fixed twenty-dimensional atomic system. -/
theorem atomic_finite_certificate :
    IsUnit (1 - RValue) ∧
    IsUnit (1 + RValue) ∧
    ((1 - RValue) * (1 - RValue)⁻¹ = 1 ∧ (1 - RValue)⁻¹ * (1 - RValue) = 1) ∧
    ((1 + RValue) * (1 + RValue)⁻¹ = 1 ∧ (1 + RValue)⁻¹ * (1 + RValue) = 1) ∧
    (∀ i j, (inverseEnclosure 0 i j).Mem ((1 - RValue)⁻¹ i j)) ∧
    (∀ i j, (inverseEnclosure 1 i j).Mem ((1 + RValue)⁻¹ i j)) :=
  ⟨sub_isUnit, add_isUnit, sub_inverse_two_sided, add_inverse_two_sided,
    sub_inverse_enclosure, add_inverse_enclosure⟩

end AtomicTriangular.FiniteCertificate.AtomicMatrix

end

end OAI
