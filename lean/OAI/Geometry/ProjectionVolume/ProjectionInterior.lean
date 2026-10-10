import OAI.Geometry.ProjectionVolume.FiniteApproximation
import OAI.Geometry.ProjectionVolume.SimplexAffine
import Mathlib.Analysis.Convex.Measure

namespace OAI

open Set Metric MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace Paper092

theorem convex_interior_nonempty_of_volume_pos {n : ℕ} {C : Set (Euclidean n)}
    (hc : IsClosed C) (hv : Convex ℝ C) (hpos : 0 < (volume C).toReal) :
    (interior C).Nonempty := by
  by_contra h
  have hi : interior C = ∅ := not_nonempty_iff_eq_empty.mp h
  have hm := hv.addHaar_frontier volume
  rw [frontier, hc.closure_eq, hi, sdiff_empty] at hm
  simp [hm] at hpos

theorem projectionBody_interior_nonempty {n : ℕ} (hn : 0 < n)
    (K : Set (Euclidean n)) (hK : IsCompact K) (hint : (interior K).Nonempty) :
    (interior (projectionBody K)).Nonempty := by
  obtain ⟨x, hx⟩ := hint
  have hnhood : K ∈ nhds x := mem_interior_iff_mem_nhds.mp hx
  obtain ⟨b, _, hbK⟩ := exists_mem_interior_convexHull_affineBasis hnhood
  let s : Affine.Simplex ℝ (Euclidean n) n :=
    ⟨b ∘ (finCongr (by simp : n + 1 = Module.finrank ℝ (Euclidean n) + 1)),
      b.ind.comp_embedding (finCongr (by simp : n + 1 = Module.finrank ℝ (Euclidean n) + 1)).toEmbedding⟩
  have hsRange : range s.points = range b := by
    exact (finCongr (by simp : n + 1 = Module.finrank ℝ (Euclidean n) + 1)).surjective.range_comp b
  have hsK : convexHull ℝ (range s.points) ⊆ K := by rwa [hsRange]
  have hsbody := simplex_is_convex_body s
  have hvol : 0 < (volume (convexHull ℝ (range s.points))).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Measure.measure_pos_of_nonempty_interior volume hsbody.2.2))
      hsbody.1.measure_lt_top.ne
  have hnorm : 0 < normalizedProjectionVolume (convexHull ℝ (range s.points)) := by
    rw [simplex_normalizedProjectionVolume hn]
    unfold simplexConstant
    positivity
  have hpi : 0 < (volume (projectionBody (convexHull ℝ (range s.points)))).toReal := by
    change 0 < _ / _ at hnorm
    exact (div_pos_iff_of_pos_right (pow_pos hvol _)).mp hnorm
  exact (convex_interior_nonempty_of_volume_pos (projectionBody_isClosed _)
    (projectionBody_convex _) hpi).mono (interior_mono (projectionBody_mono hsK hK))

theorem projectionBody_is_convex_body {d : ℕ} (hd : 2 ≤ d) (K : Set (Euclidean d))
    (hK : IsCompact K) (_hconv : Convex ℝ K) (hint : (interior K).Nonempty) :
    IsCompact (projectionBody K) ∧ Convex ℝ (projectionBody K) ∧
      (interior (projectionBody K)).Nonempty :=
  ⟨projectionBody_isCompact K, projectionBody_convex K,
    projectionBody_interior_nonempty (by omega) K hK hint⟩

end Paper092

end OAI
