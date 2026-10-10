import OAI.Algebra.DepthFive.RelaxedWordBridge
import OAI.Algebra.DepthFive.ActualBalancedWordSum

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335.MomentPairing
open Pairings LowerParameters

theorem balanced_normalV_endpoints_disjoint {L : ℕ} (hn : 4 ≤ L + 1)
    (τ : Fin (L + 1) → Kind) :
    Pairwise (fun t u : normalVLayers (balancedLayer hn) τ =>
      Disjoint (internalEndpointSet t.1) (internalEndpointSet u.1)) := by
  intro t u htu
  rw [internalEndpointSet_eq_internalEnds, internalEndpointSet_eq_internalEnds]
  apply balancedLayer_internalEnds_disjoint hn
  · exact (Finset.mem_filter.mp t.property).2.1
  · exact (Finset.mem_filter.mp u.property).2.1
  · exact fun h => htu (Subtype.ext h)

theorem sum_relaxed_pathWeight_balanced_le_exp {L : ℕ} (hn : 16 ≤ L + 1)
    (endpoint : Fin (L + 1)) :
    (∑ τ : Fin (L + 1) → Kind,
      ∑ x : RelaxedPaths (Fin (L + 1)) endpoint τ,
        pathWeight (balancedLayer (show 4 ≤ L + 1 by omega))
          (alpha (L + 1)) (beta (L + 1)) endpoint τ x.1) ≤
      (1 + beta (L + 1)) ^ m (L + 1) * ((L + 1 : ℕ) : ℝ) ^ (2 * L) *
        Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
  have hn4 : 4 ≤ L + 1 := by omega
  have h := sum_relaxed_pathWeight_le_of_boolWordSum
    (balancedLayer hn4) (alpha_pos hn4).le (beta_pos hn4).le endpoint
    (balanced_normalV_endpoints_disjoint hn4)
    (B := Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)))
  have hw : (∑ w : Fin (L + 1) → Bool,
      relaxedWordWeight (balancedLayer hn4) (Fintype.card (Fin (L + 1)))
        (alpha (L + 1)) (beta (L + 1)) (fun t => boolKindEquiv (w t))) ≤
      Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
    simpa only [Fintype.card_fin, relaxedWordWeight_eq_isolatedWeight] using
      actual_balanced_word_sum_bound hn
  simpa only [Fintype.card_fin, uLayerCount, balancedLayer_card_false] using h hw

end Problem335.MomentPairing

end

end OAI
