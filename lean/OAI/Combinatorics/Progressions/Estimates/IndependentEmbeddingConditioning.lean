import OAI.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem conditionAlongEmbedding_pi_complexMean {n : ℕ} {X Y : Fin n → Type*}
    [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
    (w : ∀ j, X j → ℝ) (hw : ∀ j x, 0 ≤ w j x) (e : ∀ j, Y j ↪ X j)
    (hmass : ∀ j, 0 < ∑ y, w j (e j y)) (f : (∀ j, X j) → ℂ) :
    let p := fun j => ofPositiveWeights (w j) (hw j) (total_pos_of_embedding (w j) (hw j) (e j) (hmass j))
    let hG : ∀ j, 0 < (p j).mass (finiteEmbeddingRange (e j)) := fun j => by
      rw [ofPositiveWeights_mass, sum_finiteEmbeddingRange]
      exact div_pos (hmass j) (total_pos_of_embedding (w j) (hw j) (e j) (hmass j))
    ((pi p).condition (piRestrictionSet (fun j => finiteEmbeddingRange (e j)))
      (piRestriction_mass_pos p (fun j => finiteEmbeddingRange (e j)) hG)).complexMean f =
      (pi (fun j => ofPositiveWeights (fun y => w j (e j y)) (fun y => hw j (e j y)) (hmass j))).complexMean
        (fun y => f (fun j => e j (y j))) := by
  dsimp only
  rw [← pi_condition _ _ (fun j => by
    rw [ofPositiveWeights_mass, sum_finiteEmbeddingRange]
    exact div_pos (hmass j) (total_pos_of_embedding (w j) (hw j) (e j) (hmass j)))]
  change (pi (fun j => conditionAlongEmbedding (w j) (hw j) (e j) (hmass j))).complexMean f = _
  exact complexMean_pi_transport
    (fun j => conditionAlongEmbedding (w j) (hw j) (e j) (hmass j))
    (fun j => ofPositiveWeights (fun y => w j (e j y)) (fun y => hw j (e j y)) (hmass j))
    (fun _ x => x) (fun j y => e j y)
    (fun j test => conditionAlongEmbedding_complexMean (w j) (hw j) (e j) (hmass j) test) f

end Erdos3.FiniteProbabilityWeights

end

end OAI
