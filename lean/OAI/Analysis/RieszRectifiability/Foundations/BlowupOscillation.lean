import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BlowupScalarPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem physical_test_lipschitz {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (φ : Ambient d → ℝ) (hφ : LipschitzWith 1 φ) :
    LipschitzWith 1 (fun y => r * φ (r⁻¹ • (y - a))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hd : dist x y = r * dist (r⁻¹ • (x - a)) (r⁻¹ • (y - a)) := by
    have h := physicalAffine_dist a ((physicalAffine a r hr).symm x)
      ((physicalAffine a r hr).symm y) r hr
    rw [(physicalAffine a r hr).apply_symm_apply, (physicalAffine a r hr).apply_symm_apply] at h
    exact h
  simp only [NNReal.coe_one, one_mul]
  calc
    _ = r * dist (φ (r⁻¹ • (x - a))) (φ (r⁻¹ • (y - a))) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hr]
    _ ≤ r * dist (r⁻¹ • (x - a)) (r⁻¹ • (y - a)) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      simpa only [NNReal.coe_one, one_mul] using! hφ.dist_le_mul (r⁻¹ • (x - a)) (r⁻¹ • (y - a))
    _ = _ := hd.symm

theorem physical_test_tsupport {d : ℕ} (a : Ambient d) (r A : ℝ) (hr : 0 < r)
    (φ : Ambient d → ℝ) (hs : tsupport φ ⊆ ball 0 A) :
    tsupport (fun y => r * φ (r⁻¹ • (y - a))) ⊆ ball a (r * A) := by
  intro y hy
  have hcomp : r⁻¹ • (y - a) ∈ tsupport φ :=
    tsupport_comp_subset_preimage (f := fun y : Ambient d => r⁻¹ • (y - a)) φ
      (by fun_prop) (tsupport_mul_subset_right hy)
  have hyball : y ∈ (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' ball 0 A := hs hcomp
  simpa only [blowup_preimage_ball a 0 r A hr, smul_zero, add_zero] using! hyball

theorem ScalarOscillationBound.blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) [SFinite μ]
    (a : Ambient d) (r A v : ℝ) (hr : 0 < r)
    (hosc : ScalarOscillationBound n μ a (r * A) (r ^ (n + 1) * v)) :
    ScalarOscillationBound n (blowupMeasure n μ a r) 0 A v := by
  intro e he φ hφ hs hzero
  have hmean : (∫ y, φ (r⁻¹ • (y - a)) ∂μ) = 0 := by
    rw [blowupMeasure_integral n μ a r hr, smul_eq_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero (pow_ne_zero n hr.ne'))
  have hmean' : (∫ y, r * φ (r⁻¹ • (y - a)) ∂μ) = 0 := by
    rw [integral_const_mul, hmean, mul_zero]
  have hp := hosc e he (fun y => r * φ (r⁻¹ • (y - a)))
    (physical_test_lipschitz a r hr φ hφ) (physical_test_tsupport a r A hr φ hs) hmean'
  rw [rieszScalarPairing_const_mul, abs_mul, abs_of_pos hr] at hp
  have hbound : |rieszScalarPairing n μ a (2 * (r * A)) e
      (fun y => φ (r⁻¹ • (y - a)))| ≤ r ^ n * v := by
    apply (mul_le_mul_iff_right₀ hr).mp
    simpa only [pow_succ, mul_assoc, mul_comm r] using! hp
  rw [rieszScalarPairing_blowup n μ a r (2 * A) hr, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (r ^ n)⁻¹)]
  have hrad : r * (2 * A) = 2 * (r * A) := by ring
  rw [hrad]
  calc
    _ ≤ (r ^ n)⁻¹ * (r ^ n * v) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = v := by rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hr.ne'), one_mul]

end

end RieszRectifiability

end OAI
