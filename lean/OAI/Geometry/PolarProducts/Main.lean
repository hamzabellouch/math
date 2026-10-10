import OAI.Geometry.PolarProducts.UpperBound

namespace OAI

namespace SymmetricPolar

theorem symmetric_polar_main {n : ℕ} (hn : 2 ≤ n)
    (K : Set (Position n)) (hK : IsSymmetricConvexBody K) :
    gromovWidth (polarProduct K) = 4 ∧
      ∀ c : ℝ, 0 < c → c < 4 →
        HasSymplecticEmbedding (capacityBall n c) (polarProduct K) := by
  refine ⟨le_antisymm (gromovWidth_polarProduct_le_four hK (by omega))
    (four_le_gromovWidth_polarProduct hK), ?_⟩
  intro c hc hc4
  exact symmetric_polar_embedding hK hc hc4

end SymmetricPolar

end OAI
