import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCoverDomain
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootSections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCoverDegree
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionL2Bounds

namespace OAI

/-! Exact global mass on the cubic root domain, without introducing
another quotient representative or any analytic input. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootDomain_global_map {p : Eisenstein} (hp : primaryPrime p) :
    (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)).map
      cubicThetaQuotientMap=
        ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ≥0∞) • cubicThetaQuotientMeasure := by
  let : Fintype (cubicThetaPrimeCubeRootTransversal hp) := Fintype.ofFinite _
  have hdis : Pairwise (fun t u : cubicThetaPrimeCubeRootTransversal hp =>
      Disjoint ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)
        ((fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain)) := by
    intro t u htu
    exact cubicThetaFundamentalDomain_translates_disjoint (fun he => htu (Subtype.ext he))
  have hmeas (t : cubicThetaPrimeCubeRootTransversal hp) :
      MeasurableSet ((fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain) :=
    (Homeomorph.smul t.val).measurableEmbedding.measurableSet_image' cubicThetaFundamentalDomain_measurable
  change (cubicThetaPointMeasure.restrict (⋃ t : cubicThetaPrimeCubeRootTransversal hp,
    (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain)).map cubicThetaQuotientMap=_
  rw [Measure.restrict_iUnion hdis hmeas,
    Measure.map_sum cubicThetaQuotientMap_open.continuous.measurable.aemeasurable]
  simp_rw [cubicThetaFundamentalDomain_translate_map]
  ext S hS
  rw [Measure.sum_apply _ hS,Measure.smul_apply,tsum_fintype,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,(cubicThetaPrimeCubeRootTransversal_complement hp).card_right]
  rfl

theorem cubicThetaPrimeCubeRootDomain_global_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp F.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp)) := by
  apply (memLp_norm_iff F.val.continuous.aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaSectionRepresentative_norm] at hn
  have hs := hn.smul_measure
    (by simp : ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ≥0∞)≠∞)
  rw [←cubicThetaPrimeCubeRootDomain_global_map hp] at hs
  have hc := hs.comp_of_map cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using hc

theorem cubicThetaPrimeCubeRootDomain_global_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    (∫ x in cubicThetaPrimeCubeRootCoverDomain hp,‖F.val x‖^2 ∂cubicThetaPointMeasure)=
      ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ)*
        ∫ q, (cubicThetaSectionNorm F q)^2 ∂cubicThetaQuotientMeasure := by
  have hi := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict (cubicThetaPrimeCubeRootCoverDomain hp))
    cubicThetaQuotientMap_open.continuous.measurable
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable
  simp only [Pi.pow_apply,cubicThetaSectionNorm_apply] at hi
  rw [cubicThetaPrimeCubeRootDomain_global_map hp,integral_smul_measure] at hi
  simpa only [ENNReal.toReal_natCast,smul_eq_mul] using hi.symm

end CubicFirstMoment

end

end OAI
