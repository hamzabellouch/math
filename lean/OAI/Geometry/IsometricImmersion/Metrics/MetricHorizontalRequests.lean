import OAI.Geometry.IsometricImmersion.Metrics.MetricQSpatialBundle

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem horizontalJet_coordinate_word_prefix (f : Coord → ℝ) (ds : List (Fin 2)) (n : ℕ) :
    horizontalJet (iteratedCoordPartial ds f) n =
      iteratedCoordPartial (List.replicate n 0 ++ ds) f := by
  induction n with
  | zero => rfl
  | succ n hn =>
      simp only [horizontalJet, List.replicate_succ, List.cons_append, iteratedCoordPartial, hn]

theorem coordinateMetricBound_to_horizontalTwoJet
    {g : MetricField} {S : Set Coord} {N : ℕ} {G : ℝ}
    (hgB : ∀ i j, CoordinateBound (fun p => g p i j) S (N + 2) G)
    {p : Coord} (hp : p ∈ S) : HorizontalMetricTwoJetBound g p N G := by
  have hb (i j : Fin 2) (ds : List (Fin 2)) (hds : ds.length ≤ 2) (n : ℕ) (hn : n ≤ N) :
      |horizontalJet (iteratedCoordPartial ds (fun x => g x i j)) n p| ≤ G := by
    rw [horizontalJet_coordinate_word_prefix]
    apply hgB i j _ _ p hp
    simp only [List.length_append, List.length_replicate]
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i j n hn
    exact hb i j [] (by simp) n hn
  · intro d i j n hn
    exact hb i j [d] (by simp) n hn
  · intro d e i j n hn
    exact hb i j [d, e] (by simp) n hn

end SmoothLocal.HighEquation

end

end OAI
