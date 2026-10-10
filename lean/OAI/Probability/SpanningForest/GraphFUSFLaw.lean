import OAI.Probability.SpanningForest.USTFiniteDeterminantal
import OAI.Probability.SpanningForest.GraphFreeKernel
import OAI.Probability.SpanningForest.FUSFExistenceReduction
import OAI.Probability.SpanningForest.IntrinsicExhaustion
import OAI.Probability.SpanningForest.Exhaustion

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

theorem exists_connectedExhaustion (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G) :
    ∃ H : ℕ → FiniteSubgraphCode, IsConnectedExhaustion G H := by
  obtain ⟨v, hv⟩ := hC.exists_adj 0
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    simp [Adj, G.2.1 0] at hv
  let e : EdgeCode := ⟨(0, v), Nat.pos_of_ne_zero hv0⟩
  exact ⟨IntrinsicExhaustion.edgeBallSubgraph G hL e,
    IntrinsicExhaustion.isConnectedExhaustion_edgeBallSubgraph hC hL e hv⟩

theorem exists_hasFUSFLaw_of_finite_identity (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G)
    (hfinite : ∀ K : FiniteSubgraphCode, IsFiniteConnectedSubgraph G K →
      ∀ A : Finset EdgeCode,
        ustCylinder K A ∅ = FreeKernel.finiteInclusionMinor K A) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  obtain ⟨H, hH⟩ := exists_connectedExhaustion G hC hL
  exact exists_hasFUSFLaw_of_inclusion_limits G H hH
    (FreeKernel.inclusionMinorLimit G)
    (FreeKernel.common_inclusion_limits_of_finite_identity G hfinite)

theorem exists_hasFUSFLaw (G : GraphCode)
    (hC : GraphConnected G) (hL : GraphLocallyFinite G) :
    ∃ μ : ProbabilityMeasure EdgeConfiguration,
      HasFUSFLaw G (μ : Measure EdgeConfiguration) id := by
  apply exists_hasFUSFLaw_of_finite_identity G hC hL
  intro K hK A
  exact FreeKernel.ustCylinder_eq_finiteKernel_minor hK A

end Problem336

end

end OAI
