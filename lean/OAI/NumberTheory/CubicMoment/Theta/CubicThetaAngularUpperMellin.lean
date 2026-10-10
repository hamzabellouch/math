import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularExponential
import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinSplit

namespace OAI

/-! Entire upper-half Mellin transforms of the actual fixed-angular
cubic theta series, proved from their exponential decay. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaAngular_continuous_height {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (z : ℂ) :
    ContinuousOn (fun v : ℝ => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v)) (Ioi 0) := by
  intro v hv
  exact ((cubicThetaAngular_continuousAt hC ha ℓ (p := (z,v)) hv).comp
    (f := fun v : ℝ => (z,v)) (by fun_prop)).continuousWithinAt

lemma cubicThetaAngular_upper_integrable {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (z s : ℂ) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(s-1)*
      cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v)) (Ioi 1) :=
  theta_upper_integrable (show 0 < Real.pi/18 by positivity)
    (cubicThetaAngular_continuous_height hC ha ℓ z)
    (fun v hv => cubicThetaAngular_exponential_bound hC ha ℓ hv z) s

lemma cubicThetaAngular_upper_norm_bound {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (z s : ℂ) :
    ‖∫ v : ℝ in Ioi 1, (v:ℂ)^(s-1)*cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v)‖ ≤
      (36*cubicThetaAngularExpConstant C ℓ/Real.pi)*Real.exp (36*(1+‖s‖)^2/Real.pi) := by
  have h := theta_upper_norm_bound (show 0 < Real.pi/18 by positivity)
    (fun v hv => cubicThetaAngular_exponential_bound hC ha ℓ hv z) s
  have h₁ : 2*cubicThetaAngularExpConstant C ℓ/(Real.pi/18) =
      36*cubicThetaAngularExpConstant C ℓ/Real.pi := by field_simp; ring
  have h₂ : 2*(1+‖s‖)^2/(Real.pi/18) = 36*(1+‖s‖)^2/Real.pi := by field_simp; ring
  simpa only [h₁,h₂] using h

/-- No modular transformation is needed for entireness of this upper
integral; all singularities of the complete Mellin transform arise below. -/
theorem cubicThetaAngular_upper_entire {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (z : ℂ) :
    Differentiable ℂ (mellin (thetaUpper (fun v : ℝ =>
      cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v)))) := by
  let f : ℝ → ℂ := fun v => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v)
  have hint : Integrable (thetaUpper f) := by
    apply (integrable_indicator_iff measurableSet_Ioi).mpr
    simpa only [sub_self,Complex.cpow_zero,one_mul] using
      cubicThetaAngular_upper_integrable hC ha ℓ z 1
  intro s
  have htop : thetaUpper f =O[atTop] (fun v : ℝ => Real.exp (-(Real.pi/18)*v)) := by
    apply IsBigO.of_bound (cubicThetaAngularExpConstant C ℓ)
    filter_upwards [eventually_gt_atTop (1:ℝ)] with v hv
    rw [thetaUpper,indicator_of_mem (show v ∈ Ioi (1:ℝ) from hv),
      Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact cubicThetaAngular_exponential_bound hC ha ℓ hv.le z
  have hbot : thetaUpper f =O[𝓝[>] 0] (fun v : ℝ => v^(-(s.re-1))) := by
    apply IsBigO.of_bound 0
    filter_upwards [(eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with v hv
    rw [thetaUpper,indicator_of_notMem (show v ∉ Ioi (1:ℝ) from not_lt.mpr hv.le),norm_zero]
    simp
  exact mellin_differentiableAt_of_isBigO_rpow_exp (show 0 < Real.pi/18 by positivity)
    (hint.locallyIntegrable.locallyIntegrableOn _) htop hbot (by linarith)

end CubicFirstMoment

end

end OAI
