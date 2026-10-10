import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothLocalWeak
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateSectionPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticChartWeak

namespace OAI

/-! The exact local Green identity descends through an injective
arithmetic chart with the actual hyperbolic measure. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaSmooth_chart_weak (G : cubicThetaSmoothTests) (J : CubicThetaSection)
    (lam : ℂ) (hEq : ∀ p : ℂ × ℝ, 0<p.2 →
      cubicThetaCoordinateLaplacian (cubicThetaSectionFunction G) p=
        lam*cubicThetaSectionFunction G p-cubicThetaSectionFunction J p)
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hgs : tsupport g⊆K)
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source) :
    let P := cubicThetaPoincareSection (cubicThetaCoordinateSeed g hg.continuous hc (hgs.trans hp))
    (∫ q, cubicThetaC1Pairing P G q ∂cubicThetaQuotientMeasure)+
      lam*(∫ q, cubicThetaSectionPairing P G q ∂cubicThetaQuotientMeasure)=
      ∫ q, cubicThetaSectionPairing P J q ∂cubicThetaQuotientMeasure := by
  intro P
  rw [cubicThetaCoordinateSection_gradient_pairing hg hc hK hp hgs e he hKe _
    (G.property.1.of_le (by simp)),
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe,
    cubicThetaCoordinateSection_mass_pairing hg hc hK hp hgs e he hKe]
  have hG : (∫ y in K, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
      (cubicThetaSectionFunction G) y)=
      ∫ y, cubicThetaHeightInverse y*cubicThetaCoordinatePairing g
        (cubicThetaSectionFunction G) y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [cubicThetaCoordinatePairing_zero_left (fun h => hy (hgs h)),mul_zero])
  have hM (F : CubicThetaSection) :
      (∫ y in K, star (g y)*cubicThetaSectionFunction F y/(y.2:ℂ)^3)=
        ∫ y, star (g y)*cubicThetaSectionFunction F y/(y.2:ℂ)^3 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgs h)),star_zero,zero_mul,zero_div])
  rw [hG,hM,hM]
  exact cubicThetaSmooth_local_weak G J lam hEq g hg hc (hgs.trans hp)

end CubicFirstMoment

end

end OAI
