import OAI.Analysis.MutuallyUnbiased.Bases.ThreeBases

namespace OAI

/-! Explicit mutually unbiased bases from two- and three-dimensional unitary matrices. -/

namespace MUB3Supporting

theorem three_mutually_unbiased_bases :
    ∃ B : Fin 3 → OrthonormalBasis (Fin 6) ℂ (EuclideanSpace ℂ (Fin 6)),
      ∀ r s : Fin 3, r ≠ s → ∀ i j : Fin 6,
        Complex.normSq (inner ℂ (B r i) (B s j)) = (1 : ℝ) / 6 := by
  simpa only [MUB6.Attainable, MUB6.IsMUBFamily] using
    MUB6.three_mutually_unbiased_bases

end MUB3Supporting

end OAI
