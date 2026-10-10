import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceEnergyBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeTraceL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeFiniteEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergySections

namespace OAI

/-! The literal finite trace maps every actual finite-energy C1 section
on the prime cover into the original closed energy space. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

local instance primeTraceFiniteEnergy_fintype {p : Eisenstein} (hp : primaryPrime p) :
    Fintype (cubicThetaPrimeTransversal hp) := Fintype.ofFinite _

lemma cubicThetaPrimeEnergy_integrable_domain {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    IntegrableOn (cubicThetaPrimeSectionEnergy hp F.val.val)
      (cubicThetaPrimeCoverDomain hp) cubicThetaPointMeasure := by
  have hq : Integrable (cubicThetaPrimeQuotientEnergy hp F.val) (cubicThetaPrimeCoverMeasure hp) := by
    simpa only [cubicThetaPrimeGradientRepresentative_norm_sq] using
      F.property.2.integrable_norm_pow (by norm_num)
  have hc := hq.comp_measurable (cubicThetaPrimeCoverMap_open hp).continuous.measurable
  simpa only [IntegrableOn,Function.comp_def,cubicThetaPrimeQuotientEnergy_apply] using hc

lemma cubicThetaPrimeEnergy_integrable_sheet {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) (t : cubicThetaPrimeTransversal hp) :
    IntegrableOn (fun x : CubicThetaPoint => cubicThetaPrimeSectionEnergy hp F.val.val (t.val • x))
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hs : (fun x : CubicThetaPoint => t.val • x) '' cubicThetaFundamentalDomain ⊆
      cubicThetaPrimeCoverDomain hp := subset_iUnion (fun u : cubicThetaPrimeTransversal hp =>
        (fun x : CubicThetaPoint => u.val • x) '' cubicThetaFundamentalDomain) t
  have hd : Integrable (cubicThetaPrimeSectionEnergy hp F.val.val)
      (cubicThetaPointMeasure.restrict (cubicThetaPrimeCoverDomain hp)) :=
    cubicThetaPrimeEnergy_integrable_domain hp F
  have hF := hd.mono_measure
    (Measure.restrict_mono_set cubicThetaPointMeasure hs)
  have hpres := (measurePreserving_smul t.val cubicThetaPointMeasure).restrict_image_emb
    (measurableEmbedding_const_smul t.val) cubicThetaFundamentalDomain
  rw [←hpres.map_eq] at hF
  exact hF.comp_measurable hpres.measurable

lemma cubicThetaPrimeTraceEnergy_integrable_domain {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    IntegrableOn (cubicThetaSectionEnergy (cubicThetaPrimeTraceSection hp F.val.val))
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hb := (integrable_finsetSum Finset.univ
    (fun t _ => cubicThetaPrimeEnergy_integrable_sheet hp F t)).const_mul
    ((cubicThetaPrimeCoverGroup hp).index:ℝ)
  apply hb.mono' (cubicThetaC1Energy_continuous _ (cubicThetaPrimeTraceSection_c1 hp F.val)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hn : 0≤cubicThetaSectionEnergy (cubicThetaPrimeTraceSection hp F.val.val) x :=
    mul_nonneg (sq_nonneg _) (cubicThetaTangentEnergy_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact cubicThetaPrimeTraceSection_energy_le hp F.val x

lemma cubicThetaPrimeTraceEnergy_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    Integrable (cubicThetaC1QuotientEnergy (cubicThetaPrimeTraceSection hp F.val.val))
      cubicThetaQuotientMeasure := by
  apply (integrable_map_measure
    (cubicThetaC1QuotientEnergy_continuous _ (cubicThetaPrimeTraceSection_c1 hp F.val)).aestronglyMeasurable
    cubicThetaQuotientMap_open.continuous.measurable.aemeasurable).mpr
  simpa only [IntegrableOn,Function.comp_def,cubicThetaC1QuotientEnergy_apply _
    (cubicThetaPrimeTraceSection_c1 hp F.val)] using cubicThetaPrimeTraceEnergy_integrable_domain hp F

lemma cubicThetaPrimeTraceGradient_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    MemLp (cubicThetaGradientRepresentative (cubicThetaPrimeTraceSection hp F.val.val))
      2 cubicThetaQuotientMeasure := by
  have hm : Measurable (cubicThetaGradientRepresentative (cubicThetaPrimeTraceSection hp F.val.val)) :=
    (cubicThetaC1Gradient_continuous _ (cubicThetaPrimeTraceSection_c1 hp F.val)).measurable.comp
      cubicThetaBorelSection_measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [cubicThetaC1Gradient_norm_sq _ (cubicThetaPrimeTraceSection_c1 hp F.val)] using
    cubicThetaPrimeTraceEnergy_integrable hp F

def cubicThetaPrimeTraceFiniteEnergy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) : cubicThetaFiniteEnergySections :=
  ⟨cubicThetaPrimeTraceSection hp F.val.val,cubicThetaPrimeTraceSection_c1 hp F.val,
    cubicThetaPrimeTraceSection_memLp hp ⟨F.val.val,F.property.1⟩,
    cubicThetaPrimeTraceGradient_memLp hp F⟩

end CubicFirstMoment

end

end OAI
