import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedClassicalPencil
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugeBoundary

namespace OAI

/-! Nonzero physical eigenmodes yield nonzero actual compact-pencil kernels;
energy membership and the boundary gauge are constructed here. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedPhysical_pencil (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density=radialMatchedMassFunction n z)
    (hp : s.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (ha : s.scale i=radialShootingA n) (lam : ℂ) (F G : ℝ → ℂ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (he : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam F G)
    (hne : ∃ r ∈ Ioc 0 R, F r ≠ 0 ∨ G r ≠ 0)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) (hM : (deriv F R,deriv G R)=M (F R,G R)) :
    ∃ v : SpectralRadialObservationSpace R, v ≠ 0 ∧
      s.compactPencil ell hR i
        (radialMatchedWeakOperator n ell z hX hz R hR lam
          (spectralFluxBoundary R (radialMatchedMassFunction n z R)
            (radialMatchedTransportFunction n z R)
            (spectralGaugeRobin (radialMatchedProfile n z R)
              (deriv (radialMatchedProfile n z) R) M))) v=v := by
  obtain ⟨f,g,hf,hg,u,huf,hug,hudf,hudg,hpair,_⟩ :=
    radialMatchedGaugeJet 2 (by norm_num) n ell z hX hz R hR F G hF hG
  have hEq := radialMatchedGauge_equation n z hX hz _ lam F G f g hf hg hpair he
  have hQ := (radialMatchedEvenProfile_contDiff n z hX hz).differentiable (by simp) R
  have hμn : radialMatchedMassFunction n z R ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX R hR.le))
  have hb := spectralPhysicalGaugeBoundary R (radialMatchedMassFunction n z R)
    (radialMatchedTransportFunction n z R) hR.ne' hμn
    (radialMatchedEvenProfile n z) f g F G hQ
    (hf.differentiable (by norm_num) R) (hg.differentiable (by norm_num) R)
    (radialMatchedEvenProfile_ne_zero n z hX R) hpair M hM
  rw [radialMatchedEvenProfile_nonneg n z R hR.le,
    (radialMatchedEvenProfile_eventuallyEq n z R hR).deriv_eq] at hb
  change (spectralGaugeFirstFlux (radialMatchedMassFunction n z)
    (radialMatchedTransportFunction n z) f g R,
    spectralGaugeSecondFlux (radialMatchedMassFunction n z)
      (radialMatchedTransportFunction n z) f g R)=_ at hb
  refine ⟨spectralHarmonicObservation ell R hR u,?_,?_⟩
  · apply spectralObservation_ne_zero_of_classical ell R hR u f g
      hf.continuous.continuousOn hg.continuous.continuousOn huf hug
    obtain ⟨r,hr,hne⟩ := hne
    refine ⟨r,⟨hr.1.le,hr.2⟩,?_⟩
    by_contra hzero
    push Not at hzero
    have hzfg : (F r,G r)=(0,0) := by
      rw [← hpair r,hzero.1,hzero.2]
      simp
    rcases hne with hne | hne
    · exact hne (congrArg Prod.fst hzfg)
    · exact hne (congrArg Prod.snd hzfg)
  · exact radialMatchedClassical_pencil n ell i z hX hz R l hR s hw hp ha lam
      f g hf hg hEq u huf hug hudf hudg _ hb

end DefocusingNLS

end OAI
