import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCriticalKernel
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTwistedTransform
import OAI.NumberTheory.CubicMoment.Estimates.HeckeFunctionalEquation

namespace OAI

/-! Move each finite retained transform to the critical line before
summing. The Mellin weight is translated back to one fixed function. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem metaplecticTransform_critical (ℓ : ℤ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {A v : ℝ} (hA : 0 ≤ A) (hv : 0 < v)
    (hm : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-A))
    (hp : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-A))
    (t : ℝ) :
    metaplecticTransform ℓ (fun x => W x*mellinPhase t x) A v =
      (Real.sqrt v:ℂ)*((1/(2*Real.pi):ℝ):ℂ)*
        ∫ τ : ℝ, metaplecticCriticalKernel ℓ W v (fun _ => 1) τ t := by
  have hc := metaplectic_transform_contour ℓ (fun x => W x*mellinPhase t x)
    (phaseWeight_compact hW t) (phaseWeight_positive hpos t)
    (phaseWeight_smooth hpos hsm t) (a := -A) (b := 1/2)
    (by linarith) le_rfl hv hm hp
  let F : ℝ → ℂ := fun τ =>
    (v:ℂ)^((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      metaplecticGammaQuotient ℓ ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)*
      mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)
  have he (τ : ℝ) :
      (v:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
        mellin (fun x => W x*mellinPhase t x) ((1/2:ℂ)+(τ:ℂ)*Complex.I) = F (τ+t) := by
    rw [mellin_mul_phase]
    dsimp [F]
    have h1 : ((τ+t-t:ℝ):ℂ) = (τ:ℂ) := by push_cast; ring
    have h2 : (1/2:ℂ)+(τ:ℂ)*Complex.I+(t:ℂ)*Complex.I =
        (1/2:ℂ)+((τ+t:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [h1,h2]
  have hf (τ : ℝ) : F τ = (Real.sqrt v:ℂ)*
      metaplecticCriticalKernel ℓ W v (fun _ => 1) τ t := by
    dsimp [F,metaplecticCriticalKernel]
    rw [hecke_scale_phase hv]
    ring
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hc
  unfold metaplecticTransform
  rw [hc]
  simp_rw [he]
  rw [integral_add_right_eq_self F t]
  simp_rw [hf]
  rw [integral_const_mul]
  ring

end CubicFirstMoment

end

end OAI
