import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialRealSourceGauge

namespace OAI

/-! An actual radial Jordan source pair passes to the matched-profile gauge. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

def IsRadialLogGaugeSourcePair (m : ℕ) (Q : ℝ → ℂ) (η lam : ℂ) (f g F G : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r →
    (lam*f r+F r=-(deriv (deriv g) r+
      (11/(r : ℂ)+deriv Q r/Q r+star (deriv Q r)/star (Q r))*deriv g r-
      η/(r : ℂ)^2*g r)-
      ((r : ℂ)/2-Complex.I*(deriv Q r/Q r-star (deriv Q r)/star (Q r)))*deriv f r) ∧
    (lam*g r+G r=deriv (deriv f) r+
      (11/(r : ℂ)+deriv Q r/Q r+star (deriv Q r)/star (Q r))*deriv f r-
      η/(r : ℂ)^2*f r-
      ((r : ℂ)/2-Complex.I*(deriv Q r/Q r-star (deriv Q r)/star (Q r)))*deriv g r-
      2*(m : ℂ)*((‖Q r‖^(2*m) : ℝ) : ℂ)*f r)

theorem radialMatchedGauge_source_equation (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η lam : ℂ) (F G f g F₀ G₀ f₀ g₀ : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hpair : ∀ r, (radialMatchedEvenProfile n z r*(f r+Complex.I*g r),
      star (radialMatchedEvenProfile n z r)*(f r-Complex.I*g r))=(F r,G r))
    (hpair₀ : ∀ r, (radialMatchedEvenProfile n z r*(f₀ r+Complex.I*g₀ r),
      star (radialMatchedEvenProfile n z r)*(f₀ r-Complex.I*g₀ r))=(F₀ r,G₀ r))
    (he : IsHarmonicRadialSourcePair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) η lam F G F₀ G₀) :
    IsRadialLogGaugeSourcePair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) η lam f g f₀ g₀ := by
  let Q := radialMatchedEvenProfile n z
  have hF : (fun r => Q r*(f r+Complex.I*g r))=F := funext (fun r => congrArg Prod.fst (hpair r))
  have hG : (fun r => star (Q r)*(f r-Complex.I*g r))=G := funext (fun r => congrArg Prod.snd (hpair r))
  have hF₀ : (fun r => Q r*(f₀ r+Complex.I*g₀ r))=F₀ := funext (fun r => congrArg Prod.fst (hpair₀ r))
  have hG₀ : (fun r => star (Q r)*(f₀ r-Complex.I*g₀ r))=G₀ := funext (fun r => congrArg Prod.snd (hpair₀ r))
  have hE : IsHarmonicRadialSourcePair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      Q η lam (fun r => Q r*(f r+Complex.I*g r))
      (fun r => star (Q r)*(f r-Complex.I*g r))
      (fun r => Q r*(f₀ r+Complex.I*g₀ r))
      (fun r => star (Q r)*(f₀ r-Complex.I*g₀ r)) := by
    rw [hF,hG,hF₀,hG₀]
    intro r hr
    simpa only [Q,radialMatchedEvenProfile_nonneg n z r hr.le] using he r hr
  intro r hr
  exact spectralRadialRealSourceGauge _ _ _ η lam Q f g f₀ g₀
    ((radialMatchedEvenProfile_contDiff n z hX hz).of_le (by simp)) hf hg hE r hr
    (radialMatchedEvenProfile_ne_zero n z hX r)
    (radialMatchedEvenProfile_stationary n z hX hz r hr)

end DefocusingNLS

end OAI
