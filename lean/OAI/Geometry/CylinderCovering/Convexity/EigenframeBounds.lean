import Mathlib

namespace OAI

noncomputable section
namespace CylinderCovering.EigenframeBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma positive_coefficient_bound (A : E →L[ℝ] E) {v w : E} {lam : ℝ}
    (hlam : 0 < lam) (hv : ‖v‖ = 1)
    (hAv : A v = lam • v) (hAw : A w = (-lam) • w) (a b : ℝ) :
    2 * lam * |a| ≤ (‖A‖ + lam) * ‖a • v + b • w‖ := by
  have hid : A (a • v + b • w) + lam • (a • v + b • w) =
      (2 * lam * a) • v := by
    simp only [map_add, map_smul, hAv, hAw]
    module
  have hn : ‖(2 * lam * a) • v‖ = 2 * lam * |a| := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hv]
  calc
    2 * lam * |a| = ‖A (a • v + b • w) + lam • (a • v + b • w)‖ := by rw [hid, hn]
    _ ≤ ‖A (a • v + b • w)‖ + ‖lam • (a • v + b • w)‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖a • v + b • w‖ + lam * ‖a • v + b • w‖ := by
      apply add_le_add (A.le_opNorm _)
      exact le_of_eq (by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam])
    _ = (‖A‖ + lam) * ‖a • v + b • w‖ := by ring

theorem coefficient_sum_bound (A : E →L[ℝ] E) {v w : E} {lam : ℝ}
    (hlam : 0 < lam) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hAv : A v = lam • v) (hAw : A w = (-lam) • w) (a b : ℝ) :
    lam * (|a| + |b|) ≤ (‖A‖ + lam) * ‖a • v + b • w‖ := by
  have ha := positive_coefficient_bound A hlam hv hAv hAw a b
  have hb := positive_coefficient_bound (-A) hlam hw
    (show (-A) w = lam • w by simp [hAw])
    (show (-A) v = (-lam) • v by simp [hAv]) b a
  rw [norm_neg, add_comm (b • w) (a • v)] at hb
  linarith

lemma eigenvalue_le_operator_norm (A : E →L[ℝ] E) {v : E} {lam : ℝ}
    (hlam : 0 < lam) (hv : ‖v‖ = 1) (hAv : A v = lam • v) : lam ≤ ‖A‖ := by
  have h := A.le_opNorm v
  simpa [hAv, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hv] using h

theorem uniform_coefficient_sum_bound (A : E →L[ℝ] E) {v w : E} {lam m B : ℝ}
    (hm : 0 < m) (hmlam : m ≤ lam) (hA : ‖A‖ ≤ B)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hAv : A v = lam • v) (hAw : A w = (-lam) • w) (a b : ℝ) :
    |a| + |b| ≤ (2 * B / m) * ‖a • v + b • w‖ := by
  have hlam : 0 < lam := hm.trans_le hmlam
  have hesum := coefficient_sum_bound A hlam hv hw hAv hAw a b
  have hlamB := (eigenvalue_le_operator_norm A hlam hv hAv).trans hA
  have hmul : m * (|a| + |b|) ≤ 2 * B * ‖a • v + b • w‖ := calc
    m * (|a| + |b|) ≤ lam * (|a| + |b|) :=
      mul_le_mul_of_nonneg_right hmlam (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ (‖A‖ + lam) * ‖a • v + b • w‖ := hesum
    _ ≤ 2 * B * ‖a • v + b • w‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hdiv := (le_div_iff₀ hm).mpr (show (|a| + |b|) * m ≤
      2 * B * ‖a • v + b • w‖ by nlinarith [hmul])
  simpa only [div_mul_eq_mul_div] using hdiv

lemma pair_frame_apply (L : (ℝ × ℝ) ≃L[ℝ] E) (a b : ℝ) :
    L (a, b) = a • L (1, 0) + b • L (0, 1) := by
  calc
    L (a, b) = L (a • (1, 0) + b • (0, 1)) := by congr 1; ext <;> simp
    _ = a • L (1, 0) + b • L (0, 1) := by rw [map_add, map_smul, map_smul]

theorem pair_frame_inverse_bound (A : E →L[ℝ] E) (L : (ℝ × ℝ) ≃L[ℝ] E)
    {lam m B : ℝ} (hm : 0 < m) (hmlam : m ≤ lam) (hA : ‖A‖ ≤ B)
    (hv : ‖L (1, 0)‖ = 1) (hw : ‖L (0, 1)‖ = 1)
    (hAv : A (L (1, 0)) = lam • L (1, 0))
    (hAw : A (L (0, 1)) = (-lam) • L (0, 1)) (z : E) :
    ‖L.symm z‖ ≤ (2 * B / m) * ‖z‖ := by
  have h := uniform_coefficient_sum_bound A hm hmlam hA hv hw hAv hAw
    (L.symm z).1 (L.symm z).2
  rw [← pair_frame_apply L, Prod.eta, L.apply_symm_apply] at h
  apply le_trans ?_ h
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_right (abs_nonneg _))
    (le_add_of_nonneg_left (abs_nonneg _))

theorem pair_frame_inverse_opNorm (A : E →L[ℝ] E) (L : (ℝ × ℝ) ≃L[ℝ] E)
    {lam m B : ℝ} (hm : 0 < m) (hmlam : m ≤ lam) (hA : ‖A‖ ≤ B)
    (hv : ‖L (1, 0)‖ = 1) (hw : ‖L (0, 1)‖ = 1)
    (hAv : A (L (1, 0)) = lam • L (1, 0))
    (hAw : A (L (0, 1)) = (-lam) • L (0, 1)) :
    ‖L.symm.toContinuousLinearMap‖ ≤ 2 * B / m := by
  have hB : 0 ≤ B := (norm_nonneg A).trans hA
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact pair_frame_inverse_bound A L hm hmlam hA hv hw hAv hAw

end CylinderCovering.EigenframeBounds

end

end OAI
