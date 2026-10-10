import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedTransform
import OAI.Analysis.RieszRectifiability.Kernel.FarRieszTransform
import OAI.Analysis.RieszRectifiability.Nets.DensityCancellation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem scalarCappedTransform_withDensity {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (U : Set (Ambient d)) (hU : MeasurableSet U) (e : Ambient d) (ε : ℝ) (x : Ambient d) :
    scalarCappedTransform m ((μ.withDensity (fun y => ENNReal.ofReal (f y))).restrict U)
      e ε (fun _ => 1) x = scalarCappedTransform m (μ.restrict U) e ε f x := by
  unfold scalarCappedTransform
  rw [restrict_withDensity hU, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [ENNReal.toReal_ofReal (hpos y).le, smul_eq_mul, one_mul]

theorem scalarFarRieszTransform_withDensity {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 < f x)
    (e a : Ambient d) (R : ℝ) (x : Ambient d) :
    scalarFarRieszTransform m (μ.withDensity (fun y => ENNReal.ofReal (f y))) e a R x =
      ∫ y in closedExterior a R, f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ := by
  unfold scalarFarRieszTransform
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ (closedExterior_measurable a R)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [ENNReal.toReal_ofReal (hpos y).le, smul_eq_mul]

theorem scalarFarRieszTransform_mul_test_integrable {d : ℕ} (m : ℕ) (C : ℝ)
    (ρ : Measure (Ambient d)) [SFinite ρ] (hgrowth : GlobalUpperGrowth m C ρ)
    (σ : Measure (Ambient d)) (e a : Ambient d) (H R : ℝ)
    (hR : 0 < R) (hHR : 2 * H ≤ R)
    (g : Ambient d → ℝ) (hg : Measurable g) (hgI : Integrable g σ)
    (hsupport : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun x => scalarFarRieszTransform m ρ e a R x * g x) σ := by
  let B := ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)) *
    (2 * (C * 2 ^ m / R))
  have hC := hgrowth.1
  apply (hgI.abs.const_mul B).mono'
    ((scalarFarRieszTransform_measurable m ρ e a R).mul hg).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  by_cases hz : g x = 0
  · simp only [Pi.mul_apply, hz, mul_zero, norm_zero, abs_zero, le_refl]
  have hx := hsupport x hz
  have hF : |scalarFarRieszTransform m ρ e a R x| ≤ B := by
    apply (scalarFarRieszTransform_integrable_and_bound m C ρ hgrowth e a x R hR (by linarith)).2.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (norm_nonneg _)) (by positivity))
      (by positivity)
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hF (abs_nonneg _)

end

end RieszRectifiability

end OAI
