import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace GeneralMahler

abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The polar of a convex body translated by an interior center. -/
def polarAt {n : ℕ} (K : Set (Rn n)) (z : Rn n) : Set (Rn n) :=
  {y | ∀ x ∈ K, ⟪y, x - z⟫ ≤ 1}

/-- The volume product minimized over the interior centers of the body. -/
def volumeProduct {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf ((fun z => (volume K).toReal * (volume (polarAt K z)).toReal) ''
    interior K)

/-- The sharp general Mahler inequality, with equality exactly for simplices. -/
theorem general_mahler {n : ℕ} (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty) :
    ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ≤ volumeProduct K ∧
      (volumeProduct K = ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ↔
        ∃ vertices : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
          AffineIndependent ℝ vertices ∧ K = convexHull ℝ (range vertices)) := by
  sorry

end GeneralMahler

end

end OAI
