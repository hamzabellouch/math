import OAI.Probability.SpanningForest.FactorLawTransport
import OAI.Probability.SpanningForest.PicardSamplerLaw
import OAI.Probability.SpanningForest.CanonicalIID

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem336.FactorAssembly

theorem rule_eq_sample (b : GraphDrift) (w : GraphNoise) (G : GraphCode) :
    rule b w G = PicardSampler.sample (w G) (b G) := by
  funext U e
  exact (PicardSampler.sample_apply_unshifted (w G) (b G) U e).symm

theorem canonical_hasFUSFLaw_of_sampler_hasLaw
    {b : GraphDrift} {w : GraphNoise} (hb : DriftBorel b) (hw : NoiseBorel w)
    (G : GraphCode) {ν : Measure EdgeConfiguration}
    (hν : HasFUSFLaw G ν id)
    (hLaw : HasLaw (PicardSampler.sample (w G) (b G)) ν privatePoolLaw) :
    HasFUSFLaw G privatePoolLaw (rule b w G) := by
  have hm : Measurable (rule b w G) :=
    measurable_rule_section (rule_borel hb hw) G
  have heq : privatePoolLaw.map (rule b w G) = ν.map id := by
    rw [rule_eq_sample, hLaw.map_eq, Measure.map_id]
  exact hasFUSFLaw_of_map_eq (X := rule b w G) (Y := id) hm hν heq

theorem worksOnGraph_of_canonical_sampler_law
    {b : GraphDrift} {w : GraphNoise} (hb : DriftBorel b) (hw : NoiseBorel w)
    (G : GraphCode) (ν : Measure EdgeConfiguration)
    (hν : GraphConnected G → GraphLocallyFinite G → HasFUSFLaw G ν id)
    (hLaw : GraphConnected G → GraphLocallyFinite G →
      HasLaw (PicardSampler.sample (w G) (b G)) ν privatePoolLaw) :
    WorksOnGraph (rule b w) G := by
  apply (CanonicalIID.worksOnGraph_iff_canonical (rule b w) G).mpr
  intro hconn hfin
  exact canonical_hasFUSFLaw_of_sampler_hasLaw hb hw G
    (hν hconn hfin) (hLaw hconn hfin)

theorem exists_factor_of_canonical_sampler_laws
    (b : GraphDrift) (w : GraphNoise)
    (hb : DriftBorel b) (hw : NoiseBorel w)
    (hbe : DriftEquivariant b) (hwe : NoiseEquivariant w)
    (ν : GraphCode → Measure EdgeConfiguration)
    (hν : ∀ G, GraphConnected G → GraphLocallyFinite G → HasFUSFLaw G (ν G) id)
    (hLaw : ∀ G, GraphConnected G → GraphLocallyFinite G →
      HasLaw (PicardSampler.sample (w G) (b G)) (ν G) privatePoolLaw) :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧
      ∀ G : GraphCode, WorksOnGraph Phi G := by
  exact ⟨rule b w, rule_borel hb hw, rule_equivariant hbe hwe,
    fun G => worksOnGraph_of_canonical_sampler_law hb hw G (ν G) (hν G) (hLaw G)⟩

end Problem336.FactorAssembly

end

end OAI
