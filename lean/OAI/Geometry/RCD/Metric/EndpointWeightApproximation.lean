import OAI.Geometry.RCD.Transport.RecoveryLimit

namespace OAI

/-! # L1 endpoint approximation under a common marginal bound

A bounded continuous path weight can be multiplied by an integrable
endpoint observable. Approximation errors are uniform over all plans
whose selected marginal is dominated by twice the same finite measure.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem integrable_endpoint_of_domination
    (π : Measure C(Time,X)) (ν : Measure X) (t : Time)
    (hd : π.map (fun γ => γ t)≤(2 : ℝ≥0∞) • ν)
    {f : X → ℝ} (hf : Integrable f ν) : Integrable (fun γ => f (γ t)) π := by
  exact ((hf.smul_measure (by norm_num : (2 : ℝ≥0∞)≠∞)).mono_measure hd).comp_measurable
    (measurable_path_eval t)

theorem integral_endpoint_weight_error
    (π : Measure C(Time,X)) (ν : Measure X) (t : Time)
    (hd : π.map (fun γ => γ t)≤(2 : ℝ≥0∞) • ν)
    (φ : C(Time,X) →ᵇ ℝ) {f g : X → ℝ} (hf : Integrable f ν) (hg : Integrable g ν) :
    ‖(∫γ,φ γ*f (γ t) ∂π)-(∫γ,φ γ*g (γ t) ∂π)‖≤
      (2*‖φ‖)*(∫x,‖f x-g x‖ ∂ν) := by
  have hφ : AEStronglyMeasurable φ π := φ.continuous.measurable.aestronglyMeasurable
  have hφb : ∀ᵐ γ ∂π, ‖φ γ‖≤‖φ‖ := Eventually.of_forall φ.norm_coe_le_norm
  have hif := integrable_endpoint_of_domination π ν t hd hf
  have hig := integrable_endpoint_of_domination π ν t hd hg
  have hid := integrable_endpoint_of_domination π ν t hd (hf.sub hg).norm
  have hm : Integrable (fun x => ‖f x-g x‖) (π.map (fun γ => γ t)) :=
    (((hf.sub hg).norm).smul_measure (by norm_num : (2 : ℝ≥0∞)≠∞)).mono_measure hd
  have hmass : (∫γ,‖f (γ t)-g (γ t)‖ ∂π)≤2*(∫x,‖f x-g x‖ ∂ν) := by
    rw [←integral_map (measurable_path_eval t).aemeasurable hm.aestronglyMeasurable]
    have hh := integral_mono_measure hd (Eventually.of_forall fun x => norm_nonneg (f x-g x))
      (((hf.sub hg).norm).smul_measure (by norm_num : (2 : ℝ≥0∞)≠∞))
    simpa only [integral_smul_measure,ENNReal.toReal_ofNat,smul_eq_mul] using hh
  rw [←integral_sub (hif.bdd_mul hφ hφb) (hig.bdd_mul hφ hφb)]
  calc
    _ ≤ ∫γ,‖φ γ*f (γ t)-φ γ*g (γ t)‖ ∂π := norm_integral_le_integral_norm _
    _ ≤ ∫γ,‖φ‖*‖f (γ t)-g (γ t)‖ ∂π := by
      apply integral_mono ((hif.bdd_mul hφ hφb).sub (hig.bdd_mul hφ hφb)).norm
        (hid.const_mul ‖φ‖)
      intro γ
      change ‖φ γ*f (γ t)-φ γ*g (γ t)‖≤‖φ‖*‖f (γ t)-g (γ t)‖
      rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm γ) (norm_nonneg _)
    _ = ‖φ‖*(∫γ,‖f (γ t)-g (γ t)‖ ∂π) := integral_const_mul _ _
    _ ≤ ‖φ‖*(2*(∫x,‖f x-g x‖ ∂ν)) := mul_le_mul_of_nonneg_left hmass (norm_nonneg _)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
