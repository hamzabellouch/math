import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedClassicalSourcePencil
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPhysicalSourceBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPhysicalPencil

namespace OAI

/-! An actual physical Jordan pair with the differentiated outgoing condition
produces a nonzero first analytic chain of the finite-power compact pencil. -/

open Set MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance physicalSourcePencilNormed (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralRadialObservationSpace R) := by
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedPhysical_source_pencil (n ell i : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (R l : ℝ) (hR : 0 < R)
    (s : SpectralPenaltyFamily R l)
    (hw : (s.weight i).density=radialMatchedMassFunction n z)
    (hp : s.pressure i=fun r => ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)))
    (ha : s.scale i=radialShootingA n) (lam : ℂ) (F G F₀ G₀ : ℝ → ℂ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (hF₀ : ContDiff ℝ 2 F₀) (hG₀ : ContDiff ℝ 2 G₀)
    (he₀ : IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam F₀ G₀)
    (he : IsHarmonicRadialSourcePair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) (((ell : ℝ)*(ell+10) : ℝ) : ℂ) lam F G F₀ G₀)
    (hne : ∃ r ∈ Ioc 0 R, F₀ r ≠ 0 ∨ G₀ r ≠ 0)
    (M : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hM : HasDerivAt M M' lam)
    (hb₀ : (deriv F₀ R,deriv G₀ R)=M lam (F₀ R,G₀ R))
    (hb : (deriv F R,deriv G R)=M lam (F R,G R)+M' (F₀ R,G₀ R)) :
    let B := fun t => spectralFluxBoundary R (radialMatchedMassFunction n z R)
      (radialMatchedTransportFunction n z R)
      (spectralGaugeRobin (radialMatchedProfile n z R) (deriv (radialMatchedProfile n z) R) (M t))
    let P := fun t => s.compactPencil ell hR i (radialMatchedWeakOperator n ell z hX hz R hR t (B t))
    ∃ v₀ v₁ : SpectralRadialObservationSpace R, v₀ ≠ 0 ∧ P lam v₀=v₀ ∧
      v₁-P lam v₁=deriv P lam v₀ := by
  intro B P
  obtain ⟨f,g,hf,hg,u,huf,hug,hudf,hudg,hpair,_⟩ :=
    radialMatchedGaugeJet 2 (by norm_num) n ell z hX hz R hR F G hF hG
  obtain ⟨f₀,g₀,hf₀,hg₀,u₀,huf₀,hug₀,hudf₀,hudg₀,hpair₀,_⟩ :=
    radialMatchedGaugeJet 2 (by norm_num) n ell z hX hz R hR F₀ G₀ hF₀ hG₀
  let B' := spectralFluxBoundarySlope R (radialMatchedMassFunction n z R)
    (spectralGaugeRobinSlope (radialMatchedProfile n z R) M')
  have hB : HasDerivAt B B' lam :=
    spectralFluxBoundary_hasDerivAt R (radialMatchedMassFunction n z R)
      (radialMatchedTransportFunction n z R) _ _ lam
      (spectralGaugeRobin_hasDerivAt _ _ M M' lam hM)
  have heq := radialMatchedGauge_source_equation n z hX hz _ lam F G f g F₀ G₀ f₀ g₀
    hf hg hpair hpair₀ he
  have hboundary := radialMatchedPhysical_source_boundary n z hX hz R hR
    F G f g F₀ G₀ f₀ g₀ hf hg hpair hpair₀ (M lam) M' hb
  have hchain := radialMatchedClassical_source_pencil n ell i z hX hz R l hR s hw hp ha lam
    f g f₀ g₀ hf₀.continuous hg₀.continuous hf hg heq u huf hug hudf hudg
    u₀ huf₀ hug₀ B B' hB hboundary
  have heq₀ := radialMatchedGauge_equation n z hX hz _ lam F₀ G₀ f₀ g₀ hf₀ hg₀ hpair₀ he₀
  have hQ := (radialMatchedEvenProfile_contDiff n z hX hz).differentiable (by simp) R
  have hμn : radialMatchedMassFunction n z R ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (radialMatchedProfile_ne_zero n z hX R hR.le))
  have hboundary₀ := spectralPhysicalGaugeBoundary R (radialMatchedMassFunction n z R)
    (radialMatchedTransportFunction n z R) hR.ne' hμn
    (radialMatchedEvenProfile n z) f₀ g₀ F₀ G₀ hQ
    (hf₀.differentiable (by norm_num) R) (hg₀.differentiable (by norm_num) R)
    (radialMatchedEvenProfile_ne_zero n z hX R) hpair₀ (M lam) hb₀
  rw [radialMatchedEvenProfile_nonneg n z R hR.le,
    (radialMatchedEvenProfile_eventuallyEq n z R hR).deriv_eq] at hboundary₀
  have hkernel := radialMatchedClassical_pencil n ell i z hX hz R l hR s hw hp ha lam
    f₀ g₀ hf₀ hg₀ heq₀ u₀ huf₀ hug₀ hudf₀ hudg₀ (B lam) hboundary₀
  refine ⟨spectralHarmonicObservation ell R hR u₀,spectralHarmonicObservation ell R hR u,?_,hkernel,hchain⟩
  apply spectralObservation_ne_zero_of_classical ell R hR u₀ f₀ g₀
    hf₀.continuous.continuousOn hg₀.continuous.continuousOn huf₀ hug₀
  obtain ⟨r,hr,hne⟩ := hne
  refine ⟨r,⟨hr.1.le,hr.2⟩,?_⟩
  by_contra hzero
  push Not at hzero
  have hzfg : (F₀ r,G₀ r)=(0,0) := by
    rw [← hpair₀ r,hzero.1,hzero.2]
    simp
  rcases hne with hne | hne
  · exact hne (congrArg Prod.fst hzfg)
  · exact hne (congrArg Prod.snd hzfg)

end DefocusingNLS

end OAI
