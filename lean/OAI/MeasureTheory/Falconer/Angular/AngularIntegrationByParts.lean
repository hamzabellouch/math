import OAI.MeasureTheory.Falconer.Angular.StationaryOppositePhase
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def cosineOscillator (Λ x : ℝ) : ℂ :=
  Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos x:ℂ))
noncomputable def angularTransport (q f : ℝ → ℂ) : ℝ → ℂ :=
  deriv (fun x => q x * f x)

 theorem cosineOscillator_hasDerivAt (Λ x : ℝ) :
    HasDerivAt (cosineOscillator Λ)
      (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x) x := by
  have h := (((Real.hasDerivAt_cos x).ofReal_comp).const_mul (Complex.I*(Λ:ℂ))).cexp
  have he : Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos x:ℂ)) *
      (Complex.I*(Λ:ℂ)*(-Real.sin x:ℝ)) =
        -Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x := by
    simp only [cosineOscillator,Complex.ofReal_neg]
    ring
  rw [he] at h
  exact h

 theorem cosineOscillator_continuous (Λ : ℝ) : Continuous (cosineOscillator Λ) :=
  continuous_iff_continuousAt.mpr (fun x => (cosineOscillator_hasDerivAt Λ x).continuousAt)

 theorem cosineOscillator_norm (Λ x : ℝ) : ‖cosineOscillator Λ x‖ = 1 := by
  simp [cosineOscillator,Complex.norm_exp]

 theorem angularTransport_support (q f : ℝ → ℂ) :
    tsupport (angularTransport q f) ⊆ tsupport f :=
  tsupport_deriv_subset.trans tsupport_mul_subset_right

 theorem angular_integration_by_parts {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hqs : ∀ x ∈ tsupport f, (Real.sin x:ℂ)*q x = 1) (Λ : ℝ) :
    (∫ x : ℝ, cosineOscillator Λ x * angularTransport q f x) =
      (Complex.I*(Λ:ℂ)) * ∫ x : ℝ, cosineOscillator Λ x * f x := by
  let v : ℝ → ℂ := fun x => q x * f x
  have hv : ContDiff ℝ ∞ v := hq.mul hf
  have hvc : HasCompactSupport v := hc.mul_left
  have hE := cosineOscillator_continuous Λ
  have hv' : Continuous (angularTransport q f) := hv.continuous_deriv (by simp)
  have hi₁ : Integrable (fun x => cosineOscillator Λ x * angularTransport q f x) :=
    (hE.mul hv').integrable_of_hasCompactSupport hvc.deriv.mul_left
  have hE' : Continuous (fun x => -Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sin)).mul hE
  have hi₂ : Integrable (fun x => (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x)*v x) :=
    (hE'.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hi₃ : Integrable (fun x => cosineOscillator Λ x * v x) :=
    (hE.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := cosineOscillator Λ) (v := v) (v' := angularTransport q f)
    (fun x _ => cosineOscillator_hasDerivAt Λ x)
    (fun x _ => (hv.differentiable (by simp)).differentiableAt.hasDerivAt) hi₁ hi₂ hi₃
  change (∫ x : ℝ, cosineOscillator Λ x * angularTransport q f x) = _ at hh
  rw [hh]
  have he : (fun x => (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x)*v x) =
      fun x => -(Complex.I*(Λ:ℂ)) * (cosineOscillator Λ x * f x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · dsimp [v]
      calc
        _ = -(Complex.I*(Λ:ℂ)) * cosineOscillator Λ x * ((Real.sin x:ℂ)*q x) * f x := by ring
        _ = _ := by rw [hqs x hx]; ring
    · simp [v,image_eq_zero_of_notMem_tsupport hx]
  rw [he,integral_const_mul]
  ring

end PlanarFalconer

end OAI
