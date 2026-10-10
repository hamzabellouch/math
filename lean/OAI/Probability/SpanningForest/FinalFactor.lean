import OAI.Probability.SpanningForest.AllPairWiener
import OAI.Probability.SpanningForest.GraphTreePosteriorEquiv
import OAI.Probability.SpanningForest.CanonicalBrownianSampler
import OAI.Probability.SpanningForest.GraphFUSFLaw
import OAI.Probability.SpanningForest.FUSFPosteriorResponse
import OAI.Probability.SpanningForest.AllPairPosteriorDrift

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.FinalFactor

local instance : MeasurableSpace GlobalWiener.Path := borel _
local instance : BorelSpace GlobalWiener.Path := ⟨rfl⟩

def rule : FactorRule :=
  FactorAssembly.rule GraphTreePosterior.drift AllPairWiener.noise

theorem rule_borel : RuleBorel rule :=
  FactorAssembly.rule_borel GraphTreePosterior.measurable_drift
    AllPairWiener.noise_borel

theorem rule_equivariant : RuleEquivariant rule :=
  FactorAssembly.rule_equivariant GraphTreePosterior.drift_relabel
    AllPairWiener.noise_equivariant

theorem rule_eq_sample (G : GraphCode) :
    rule G = PicardSampler.sample (AllPairWiener.noise G) (GraphTreePosterior.drift G) :=
  FactorAssembly.rule_eq_sample GraphTreePosterior.drift AllPairWiener.noise G

theorem sample_hasLaw {G : GraphCode}
    (hc : GraphConnected G) (hf : GraphLocallyFinite G)
    {μ : ProbabilityMeasure EdgeConfiguration}
    (hμ : HasFUSFLaw G (μ : Measure EdgeConfiguration) id) :
    HasLaw (PicardSampler.NonnegativeTime.sample
      (fun (W : EdgeCode → GlobalWiener.Path) e t => W e t)
      (GraphTreePosterior.drift G)) (μ : Measure EdgeConfiguration) AllPairWiener.law := by
  rw [GraphTreePosterior.drift_fun_eq_allPair_posteriorDrift_of_hasFUSFLaw hc hf hμ]
  exact CanonicalBrownianSampler.hasLaw_sample μ (AllPairObservation.observations G)
    (AllPairObservation.observations_mono G)
    (fun e f => AllPairObservation.exists_mem_observations hc hf e f)
    (L := (1 / 2 : ℝ)) (by norm_num) (hμ.finiteResponseBound hc _)

theorem worksOnGraph (G : GraphCode) : WorksOnGraph rule G := by
  apply (CanonicalIID.worksOnGraph_iff_canonical rule G).mpr
  intro hc hf
  obtain ⟨μ, hμ⟩ := exists_hasFUSFLaw G hc hf
  exact FactorAssembly.canonical_hasFUSFLaw_of_sampler_hasLaw
    GraphTreePosterior.measurable_drift AllPairWiener.noise_borel G hμ
    (AllPairWiener.sampler_hasLaw_of_product GraphTreePosterior.drift G hc hf
      (sample_hasLaw hc hf hμ))

theorem exists_factor :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧
      ∀ G : GraphCode, WorksOnGraph Phi G :=
  ⟨rule, rule_borel, rule_equivariant, worksOnGraph⟩

end Problem336.FinalFactor

end

end OAI
