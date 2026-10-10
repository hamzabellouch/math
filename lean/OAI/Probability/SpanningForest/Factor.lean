import OAI.Probability.SpanningForest.Theory
import OAI.Probability.SpanningForest.FinalFactor

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Problem336

theorem fusf_is_factor_iid :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧ ∀ G : GraphCode, WorksOnGraph Phi G := by
  exact FinalFactor.exists_factor

theorem fusf_factor_for_every_unimodular_law :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧ ∀ Q : Measure (GraphCode × ℕ), IsUnimodular Q → GraphLawSupported Q → ∀ᵐ x ∂Q, WorksOnGraph Phi x.1 := by
  obtain ⟨Phi, hBorel, hEquivariant, hWorks⟩ := fusf_is_factor_iid
  refine ⟨Phi, hBorel, hEquivariant, ?_⟩
  intro Q _ _
  exact Filter.Eventually.of_forall (fun x => hWorks x.1)

end Problem336

end

end OAI
