import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexDensity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1Pairing

namespace OAI

/-! Exact complex integration of a quotient function supported in one
injective coordinate sheet. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaCoordinateChart_integral
    (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {K : Set (ℂ × ℝ)} (hK : IsCompact K) (hp : K⊆{y : ℂ × ℝ | 0<y.2})
    (hKe : cubicThetaPointInclusion.symm '' K⊆e.source)
    (F : CubicThetaQuotient → ℂ) (hF : StronglyMeasurable F)
    (hs : Function.support F⊆cubicThetaQuotientMap '' (cubicThetaPointInclusion.symm '' K))
    (f : ℂ × ℝ → ℂ)
    (hf : ∀ p∈cubicThetaPointInclusion.symm '' K, F (cubicThetaQuotientMap p)=f p.val) :
    (∫ q, F q ∂cubicThetaQuotientMeasure)=∫ y in K, f y/(y.2:ℂ)^3 := by
  let S := cubicThetaPointInclusion.symm '' K
  have hi : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  have hS : IsCompact S := hK.image_of_continuousOn (hi.mono hp)
  have hcoords : cubicThetaPointCoordinates '' S=K := by
    ext y
    constructor
    · rintro ⟨p,⟨z,hz,rfl⟩,rfl⟩
      have heq := cubicThetaPointInclusion.right_inv
        (show z∈cubicThetaPointInclusion.target by rw [cubicThetaPointInclusion_target]; exact hp hz)
      change cubicThetaPointCoordinates (cubicThetaPointInclusion.symm z)∈K
      change cubicThetaPointCoordinates (cubicThetaPointInclusion.symm z)=z at heq
      rw [heq]
      exact hz
    · intro hy
      exact ⟨cubicThetaPointInclusion.symm y,⟨y,hy,rfl⟩,
        cubicThetaPointInclusion.right_inv (by rw [cubicThetaPointInclusion_target]; exact hp hy)⟩
  have hz : ∀ q, q∉cubicThetaQuotientMap '' S → F q=0 := by
    intro q hq
    by_contra hn
    exact hq (hs hn)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    cubicThetaChart_complex_integral e he hS.measurableSet hKe F hF]
  rw [setIntegral_congr_fun hS.measurableSet hf]
  change (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=_
  simpa only [hcoords] using cubicThetaPointIntegral_complex_density hS.measurableSet f

end CubicFirstMoment

end

end OAI
