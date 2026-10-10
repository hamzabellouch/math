import OAI.Geometry.Convex.GeneralMahler.Main

namespace OAI

noncomputable section

open Set MeasureTheory

namespace GeneralMahler

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
  let D := ofSet K hcompact hconvex hinterior
  have h := (general_geometric hn K hcompact hconvex hinterior).2.2.2.2
  change ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ≤ D.P ∧
    (D.P = ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ↔
      ∃ vertices : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
        AffineIndependent ℝ vertices ∧ K = convexHull ℝ (range vertices)) at h
  have hInf : D.P = volumeProduct K := D.product_inf
  rw [hInf] at h
  exact h

end GeneralMahler

end

end OAI
