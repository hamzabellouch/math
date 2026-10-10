import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceSection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeL2

namespace OAI

/-! The finite trace has finite mass. Each sheet is integrated using
the actual hyperbolic measure and the constructed disjoint fundamental domain. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

local instance primeTraceL2_fintype {p : Eisenstein} (hp : primaryPrime p) :
    Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _

lemma cubicThetaPrimeSection_memLp_domain {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) :
    MemLp F.val.val 2 (cubicThetaPointMeasure.restrict (cubicThetaPrimeCoverDomain hp)) := by
  apply (memLp_norm_iff F.val.val.continuous.aestronglyMeasurable).mp
  have hn := F.property.norm
  simp only [cubicThetaPrimeSectionRepresentative_norm] at hn
  have hc := hn.comp_of_map (cubicThetaPrimeCoverMap_open hp).continuous.measurable.aemeasurable
  simpa only [Function.comp_def,cubicThetaPrimeSectionNorm_apply] using hc

lemma cubicThetaPrimeSheet_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) (t : cubicThetaPrimeTransversal hp) :
    MemLp (fun x : CubicThetaPoint => F.val.val (t.val • x)) 2
      (cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain) := by
  have hs : (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain ⊆
      cubicThetaPrimeCoverDomain hp := subset_iUnion (fun u : cubicThetaPrimeTransversal hp =>
        (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t
  have hF := (cubicThetaPrimeSection_memLp_domain hp F).mono_measure
    (Measure.restrict_mono_set cubicThetaPointMeasure hs)
  exact hF.comp_measurePreserving
    ((measurePreserving_smul t.val cubicThetaPointMeasure).restrict_image_emb
      (measurableEmbedding_const_smul t.val) cubicThetaFundamentalDomain)

lemma cubicThetaPrimeTraceSection_memLp_domain {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) :
    MemLp (cubicThetaPrimeTraceSection hp F.val).val 2
      (cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain) := by
  change MemLp (fun x => ∑ t : cubicThetaPrimeTransversal hp,
    cubicThetaPrimeTraceTerm hp F.val t.val x) 2 _
  apply memLp_finsetSum
  intro t _
  change MemLp (star (cubicThetaKubotaValue t.val) •
    (fun x : CubicThetaPoint => F.val.val (t.val • x))) 2 _
  exact (cubicThetaPrimeSheet_memLp hp F t).const_smul (star (cubicThetaKubotaValue t.val))

theorem cubicThetaPrimeTraceSection_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteSections hp) :
    MemLp (cubicThetaSectionRepresentative (cubicThetaPrimeTraceSection hp F.val))
      2 cubicThetaQuotientMeasure := by
  have htrace := cubicThetaPrimeTraceSection_memLp_domain hp F
  apply (memLp_norm_iff (cubicThetaSectionRepresentative_measurable _).aestronglyMeasurable).mp
  simp only [cubicThetaSectionRepresentative_norm]
  apply (memLp_map_measure_iff
    (cubicThetaSectionNorm_continuous _).aestronglyMeasurable
    cubicThetaQuotientMap_open.continuous.measurable.aemeasurable).mpr
  simpa only [Function.comp_def,cubicThetaSectionNorm_apply] using htrace.norm

end CubicFirstMoment

end

end OAI
