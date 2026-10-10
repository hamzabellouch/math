import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeDilationNorm

namespace OAI

/-! Complex integration on the actual cubed-prime cover and the
integrability of Hermitian products of square-integrable sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeComplexSheetIntegral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℂ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure)=
      ∑' t : cubicThetaPrimeCubeTransversal p,
        ∫ x in cubicThetaFundamentalDomain,f (t.val • x) ∂cubicThetaPointMeasure := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  rw [tsum_fintype]
  have hmeas (t : cubicThetaPrimeCubeTransversal p) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (measurableEmbedding_const_smul t.val).measurableSet_image' cubicThetaFundamentalDomain_measurable
  have hint (t : cubicThetaPrimeCubeTransversal p) :
      IntegrableOn f ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        cubicThetaPointMeasure :=
    hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
      (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  change (∫ x in ⋃ t : cubicThetaPrimeCubeTransversal p,
    (fun y : CubicThetaPoint => t.val • y) '' cubicThetaFundamentalDomain,f x
      ∂cubicThetaPointMeasure)=_
  rw [integral_iUnion_fintype hmeas (cubicThetaPrimeCubeCoverDomain_disjoint p) hint]
  apply Finset.sum_congr rfl
  intro t _
  exact (measurePreserving_smul t.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul t.val) f cubicThetaFundamentalDomain

lemma cubicThetaSquareIntegrablePair {S : Set CubicThetaPoint}
    (F G : CubicThetaPoint → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hFs : IntegrableOn (fun x => ‖F x‖^2) S cubicThetaPointMeasure)
    (hGs : IntegrableOn (fun x => ‖G x‖^2) S cubicThetaPointMeasure) :
    IntegrableOn (fun x => star (F x)*G x) S cubicThetaPointMeasure := by
  apply ((hFs.add hGs).div_const 2).mono'
    ((hF.star.mul hG).aestronglyMeasurable)
  filter_upwards with x
  change ‖star (F x)*G x‖ ≤ (‖F x‖^2+‖G x‖^2)/2
  rw [norm_mul,norm_star]
  nlinarith [sq_nonneg (‖F x‖-‖G x‖)]

lemma cubicThetaPrimeCubeComplexSheet_integrable {p : Eisenstein} (_hp : primaryPrime p)
    {f : CubicThetaPoint → ℂ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (t : cubicThetaPrimeCubeTransversal p) :
    IntegrableOn (fun x => f (t.val • x)) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hs := hf.mono_set (subset_iUnion (fun u : cubicThetaPrimeCubeTransversal p =>
    (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t)
  exact ((measurePreserving_smul t.val cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul t.val)).mp hs

end CubicFirstMoment

end

end OAI
