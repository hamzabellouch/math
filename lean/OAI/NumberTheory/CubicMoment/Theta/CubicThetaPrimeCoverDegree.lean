import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverMeasure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIntegralQuotient

namespace OAI

/-! The finite arithmetic covering has exactly its subgroup index as
measure degree. This gives the normalization for lifting actual L2 vectors. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaFundamentalDomain_translates_disjoint
    {g h : cubicThetaPrincipalGroup} (hne : g≠h) :
    Disjoint ((fun x : CubicThetaPoint => g • x) '' cubicThetaFundamentalDomain)
      ((fun x : CubicThetaPoint => h • x) '' cubicThetaFundamentalDomain) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hga⟩ ⟨b,hb,hgb⟩
  dsimp only at hga hgb
  have hm : (h⁻¹*g) • a=b := by
    rw [mul_smul,hga,←hgb,inv_smul_smul]
  have he : h⁻¹*g=(1:cubicThetaPrincipalGroup) :=
    (cubicThetaFundamentalDomain_unique a).unique (by rwa [hm]) (by simpa using ha)
  exact hne (inv_mul_eq_one.mp he).symm

lemma cubicThetaFundamentalDomain_translate_map (g : cubicThetaPrincipalGroup) :
    (cubicThetaPointMeasure.restrict
      ((fun x : CubicThetaPoint => g • x) '' cubicThetaFundamentalDomain)).map
        cubicThetaQuotientMap=cubicThetaQuotientMeasure :=
  (cubicThetaQuotientMeasure_independent (cubicThetaIntegralImage_fundamental g.val)).symm

theorem cubicThetaPrimeCoverProjection_measure {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPrimeCoverMeasure hp).map (cubicThetaPrimeCoverProjection hp)=
      ((cubicThetaPrimeCoverGroup hp).index : ℝ≥0∞) • cubicThetaQuotientMeasure := by
  let : Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _
  have hdis : Pairwise (fun t u : cubicThetaPrimeTransversal hp =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain)) := by
    intro t u htu
    exact cubicThetaFundamentalDomain_translates_disjoint
      (fun he => htu (Subtype.ext he))
  have hmeas (t : cubicThetaPrimeTransversal hp) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image'
      cubicThetaFundamentalDomain_measurable
  rw [cubicThetaPrimeCoverMeasure,
    Measure.map_map (cubicThetaPrimeCoverProjection_continuous hp).measurable
      (cubicThetaPrimeCoverMap_open hp).continuous.measurable]
  change (cubicThetaPointMeasure.restrict (⋃ t : cubicThetaPrimeTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)).map
      cubicThetaQuotientMap=_
  rw [Measure.restrict_iUnion hdis hmeas,
    Measure.map_sum cubicThetaQuotientMap_open.continuous.measurable.aemeasurable]
  simp_rw [cubicThetaFundamentalDomain_translate_map]
  ext S hS
  rw [Measure.sum_apply _ hS,Measure.smul_apply,tsum_fintype,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,(cubicThetaPrimeTransversal_complement hp).card_right]
  rfl

end CubicFirstMoment

end

end OAI
