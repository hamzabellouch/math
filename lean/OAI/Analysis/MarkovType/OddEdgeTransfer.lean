import OAI.Analysis.MarkovType.MarkovFiniteRepresentability
import OAI.Analysis.MarkovType.LatticeCosts

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X V : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem MarkovTypeWith.of_near_isometric_embeddings {p K : ℝ}
    (hX : MarkovTypeWith p K X)
    (hVX : ∀ η : ℝ, 0 < η → ∃ T : V →ₗ[ℝ] X,
      ∀ z : V, ‖z‖ ≤ ‖T z‖ ∧ ‖T z‖ ≤ (1 + η) * ‖z‖) :
    MarkovTypeWith p K V := by
  apply hX.of_finitelyRepresentable
  intro E _ η hη
  obtain ⟨T, hT⟩ := hVX η hη
  refine ⟨T.comp E.subtype, ?_⟩
  intro z
  exact hT z

theorem MarkovTypeWith.odd_edge_bound_of_embeddings
    {S E : Type*} [Fintype S] [Fintype E] {p K : ℝ}
    (hX : MarkovTypeWith p K X)
    (hVX : ∀ η : ℝ, 0 < η → ∃ T : V →ₗ[ℝ] X,
      ∀ z : V, ‖z‖ ≤ ‖T z‖ ∧ ‖T z‖ ≤ (1 + η) * ‖z‖)
    (C : FiniteMarkedChain S E) (g : E → V) (hg : OddLabel C g)
    (n : ℕ) (hn : 1 ≤ n) :
    markedSumCost C g p n ≤ Real.rpow K p * (n : ℝ) * stationaryEdgeCost C g p :=
  (hX.of_near_isometric_embeddings hVX).odd_edge_bound C g hg n hn

end MarkovSuperreflexivity

end

end OAI
