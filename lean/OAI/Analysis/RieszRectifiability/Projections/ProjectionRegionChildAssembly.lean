import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.RegionRepresentativeGeometry
import OAI.Analysis.RieszRectifiability.Restart.SelectedStopChildGluing
import OAI.Analysis.RieszRectifiability.Surfaces.BoundedNormalizedBallCharts
import OAI.Analysis.RieszRectifiability.Projections.ProjectionDiskCoordinates

namespace OAI

/-!
# Projection-region child assembly

Projection-disk coordinates and separated-patch gluing assemble child charts into a
bounded Lipschitz chart covering the region limit and each child's covered cell.
The uncovered parent-cell mass is bounded by the sum of the uncovered child-cell masses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def projectionRegionAssemblyConstant (d : ℕ) (L M : ℝ≥0) : ℝ≥0 :=
  ((lipschitzExtensionConstant (Ambient d) *
    separatedPatchGluingConstant (M * (4 * (32 * L))) (32 * L) L) * 2) * 2

theorem exists_projection_region_child_assembly {n d : ℕ}
    (ν : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets ν R hR k).points)
    (Good : SupportCellDescendant ν R hR k z → Prop)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (L : ℝ≥0) (hL : 1 ≤ L)
    (hsep : ∀ x ∈ cellRegionRepresentatives ν R hR k z Good,
      ∀ y ∈ cellRegionRepresentatives ν R hR k z Good,
        dist x y ≤ (L : ℝ) * dist (P.starProjection x) (P.starProjection y))
    (child : ∀ i : cellRegionStops ν R hR k z Good,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
      LipschitzWith (projectionRegionAssemblyConstant d L M) g ∧
      Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
      (cellRegionLimit ν R hR k z Good ⊆ Set.range g) ∧
      (∀ i, i.val.cell ∩ Set.range (child i) ⊆ Set.range g) ∧
      ν (cleanSupportCell ν R hR k z \ Set.range g) ≤
        ∑' i : cellRegionStops ν R hR k z Good, ν (i.val.cell \ Set.range (child i)) := by
  let := supportCellDescendant_countable ν R hR k z
  let E := cellRegionRepresentatives ν R hR k z Good
  let F := cellRegionStops ν R hR k z Good
  have hr := latticeRadius_pos R hR k
  obtain ⟨T, hnorm, hT, _⟩ := exists_projection_disk_coordinates P hdim
  let coord (x : Ambient d) := T (x - z)
  have hdist (x y : Ambient d) : dist (coord x) (coord y) =
      dist (P.starProjection x) (P.starProjection y) := by
    change dist (T (x - z)) (T (y - z)) = _
    rw [dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right, hnorm, map_sub, ← dist_eq_norm]
  have hcoord : ∀ x ∈ E, ∀ y ∈ E,
      dist x y ≤ (L : ℝ) * dist (coord x) (coord y) := by
    intro x hx y hy
    rw [hdist]
    exact hsep x hx y hy
  have hcoordBall : ∀ x ∈ E, coord x ∈ closedBall (0 : Ambient n) (2 * latticeRadius R k) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    change ‖T (x - z)‖ ≤ 2 * latticeRadius R k
    have hb := (supportLatticeCell_bounds ν R hR k z).2
      (cellRegionRepresentatives_subset_top ν R hR k z Good hx).1
    exact (hT (x - z)).trans (by simpa only [mem_closedBall, dist_eq_norm] using! hb)
  have hx (i : F) : i.val.center ∈ closedBall i.val.center (i.val.radius / 32) :=
    mem_closedBall_self (by have hi := i.val.radius_pos; positivity)
  have hxE (i : F) : i.val.center ∈ E := Or.inr (Set.mem_range_self i)
  have hradius (i : F) : i.val.radius ≤ 2 * latticeRadius R k := by
    have hi : i.val.radius ≤ latticeRadius R k :=
      latticeRadius_antitone R hR.le (Nat.le_add_right k i.val.depth)
    linarith
  obtain ⟨f, hf, hcover⟩ := exists_ball_lipschitz_cover_of_stop_children_and_survivors
    ν R hR k z Good E coord L hL hcoord (2 * latticeRadius R k) (by positivity) hcoordBall
    F (fun _ hi => hi) (fun i => i.val.center) hx hxE hradius child M hLip himage
  obtain ⟨g₁, hg₁, _, hcover₁⟩ := exists_bounded_normalized_ball_chart (2 * latticeRadius R k)
    (z : Ambient d) (2 * latticeRadius R k) (by positivity) f _ hf
  obtain ⟨g, hg, hgrange, hcover₂⟩ := exists_bounded_normalized_ball_chart (latticeRadius R k)
    (z : Ambient d) (2 * latticeRadius R k) (by positivity) g₁ _ hg₁
  have hfix (y : Ambient d) (hy : y ∈ cleanSupportCell ν R hR k z) (hyf : y ∈ Set.range f) :
      y ∈ Set.range g := by
    have hb := (supportLatticeCell_bounds ν R hR k z).2 hy.1
    exact hcover₂ ⟨hb, hcover₁ ⟨hb, hyf⟩⟩
  have hparent : cellRegionLimit ν R hR k z Good ⊆ Set.range g := by
    intro y hy
    exact hfix y hy.1 (hcover (Or.inl ⟨hy, Or.inl hy⟩))
  have hchild (i : F) : i.val.cell ∩ Set.range (child i) ⊆ Set.range g := by
    intro y hy
    exact hfix y (i.val.cell_subset_top hy.1) (hcover (Or.inr (mem_iUnion.mpr ⟨i, hy.2⟩)))
  have hsub : cleanSupportCell ν R hR k z \ Set.range g ⊆
      ⋃ i : F, i.val.cell \ Set.range (child i) := by
    intro y hy
    have hnot : y ∉ cellRegionLimit ν R hR k z Good := fun h => hy.2 (hparent h)
    obtain ⟨i, hi, hyi⟩ := exists_first_failing_cell ν R hR k z Good y hy.1 hnot
    refine mem_iUnion.mpr ⟨⟨i, hi⟩, hyi, ?_⟩
    intro h
    exact hy.2 (hchild ⟨i, hi⟩ ⟨hyi, h⟩)
  exact ⟨g, hg, hgrange, hparent, hchild, (measure_mono hsub).trans (measure_iUnion_le _)⟩

end

end RieszRectifiability

end OAI
