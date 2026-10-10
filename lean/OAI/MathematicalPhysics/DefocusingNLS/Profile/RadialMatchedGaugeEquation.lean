import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedGaugeMembership
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialRealGauge

namespace OAI

/-! Actual physical radial eigenmodes yield classical gauge eigenmodes in the energy space. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

def IsRadialLogGaugeEigenpair (m : ℕ) (Q : ℝ → ℂ) (η lam : ℂ) (f g : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r →
    (lam*f r=-(deriv (deriv g) r+
      (11/(r : ℂ)+deriv Q r/Q r+star (deriv Q r)/star (Q r))*deriv g r-
      η/(r : ℂ)^2*g r)-
      ((r : ℂ)/2-Complex.I*(deriv Q r/Q r-star (deriv Q r)/star (Q r)))*deriv f r) ∧
    (lam*g r=deriv (deriv f) r+
      (11/(r : ℂ)+deriv Q r/Q r+star (deriv Q r)/star (Q r))*deriv f r-
      η/(r : ℂ)^2*f r-
      ((r : ℂ)/2-Complex.I*(deriv Q r/Q r-star (deriv Q r)/star (Q r)))*deriv g r-
      2*(m : ℂ)*((‖Q r‖^(2*m) : ℝ) : ℂ)*f r)

theorem radialMatchedGauge_equation (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (η lam : ℂ) (F G f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hpair : ∀ r, (radialMatchedEvenProfile n z r*(f r+Complex.I*g r),
      star (radialMatchedEvenProfile n z r)*(f r-Complex.I*g r))=(F r,G r))
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) η lam F G) :
    IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
      (radialMatchedEvenProfile n z) η lam f g := by
  let Q := radialMatchedEvenProfile n z
  have hF : (fun r => Q r*(f r+Complex.I*g r))=F := funext (fun r => congrArg Prod.fst (hpair r))
  have hG : (fun r => star (Q r)*(f r-Complex.I*g r))=G := funext (fun r => congrArg Prod.snd (hpair r))
  have hE : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      Q η lam (fun r => Q r*(f r+Complex.I*g r))
      (fun r => star (Q r)*(f r-Complex.I*g r)) := by
    rw [hF,hG]
    intro r hr
    simpa only [Q,radialMatchedEvenProfile_nonneg n z r hr.le] using he r hr
  intro r hr
  exact spectralRadialRealGauge _ _ _ η lam Q f g
    ((radialMatchedEvenProfile_contDiff n z hX hz).of_le (by simp)) hf hg hE r hr
    (radialMatchedEvenProfile_ne_zero n z hX r)
    (radialMatchedEvenProfile_stationary n z hX hz r hr)

theorem radialMatchedGauge_classical_energy (n ell : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R : ℝ) (hR : 0 < R)
    (η lam : ℂ) (F G : ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) η lam F G) :
    ∃ f g : ℝ → ℂ, ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧
      IsRadialLogGaugeEigenpair (n+radialInnerShootingThreshold)
        (radialMatchedEvenProfile n z) η lam f g ∧
      ∃ u : SpectralHarmonicPair ell R,
        (∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r) ∧
        (∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r) ∧
        (spectralHarmonicDerivative ell R u.fst =ᵐ[radialPressureMeasure R] deriv f) ∧
        (spectralHarmonicDerivative ell R u.snd =ᵐ[radialPressureMeasure R] deriv g) ∧
        ∀ r ∈ Ioc 0 R,
          spectralPhysicalValueMap (spectralPhysicalGaugePair (radialMatchedProfile n z)
            (spectralHarmonicRepresentative ell R hR u.fst)
            (spectralHarmonicRepresentative ell R hR u.snd) r)=(F r,G r) := by
  obtain ⟨f,g,hf,hg,u,hu,hv,hdu,hdv,hpair,hphys⟩ :=
    radialMatchedGaugeJet 2 (by norm_num) n ell z hX hz R hR F G hF hG
  exact ⟨f,g,hf,hg,radialMatchedGauge_equation n z hX hz η lam F G f g hf hg hpair he,
    u,hu,hv,hdu,hdv,hphys⟩

end DefocusingNLS

end OAI
