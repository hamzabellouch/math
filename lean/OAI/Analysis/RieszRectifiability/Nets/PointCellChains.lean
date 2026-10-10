import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainComposition
import OAI.Analysis.RieszRectifiability.Nets.AnnularLatticeScales

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_unique_support_descendant_at_point {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (x : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z) (t : ℕ) :
    ∃! i : SupportCellDescendant μ R hR k z, i.depth = t ∧ x ∈ i.cell := by
  rw [cleanSupportCell_eq_iUnion_descendants μ R hR k t z] at hx
  obtain ⟨w, hw⟩ := mem_iUnion.mp hx
  obtain ⟨hanc, hxw⟩ := mem_iUnion.mp hw
  let i : SupportCellDescendant μ R hR k z :=
    { depth := t, center := w, mem_net := w.property, ancestor := hanc }
  refine ⟨i, ⟨rfl, hxw⟩, ?_⟩
  intro j hj
  exact j.eq_of_common_point_same_depth i hj.1 x hj.2 hxw

theorem cleanSupportCell_pair_distance_le {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (x y : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z)
    (hy : y ∈ cleanSupportCell μ R hR k z) :
    dist x y ≤ 4 * latticeRadius R k := by
  have hxz := (supportLatticeCell_bounds μ R hR k z).2 hx.1
  have hyz := (supportLatticeCell_bounds μ R hR k z).2 hy.1
  change dist x (z : Ambient d) ≤ 2 * latticeRadius R k at hxz
  change dist y (z : Ambient d) ≤ 2 * latticeRadius R k at hyz
  have ht := dist_triangle_right x y (z : Ambient d)
  linarith

theorem exists_pair_scale_support_descendant {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (x y : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z)
    (hy : y ∈ cleanSupportCell μ R hR k z) (hne : x ≠ y) :
    ∃ i : SupportCellDescendant μ R hR k z,
      x ∈ i.cell ∧ i.radius ≤ dist x y / 8 ∧ dist x y ≤ 512 * i.radius ∧
        x ∈ ball i.center (1024 * i.radius) ∧
        y ∈ ball i.center (1024 * i.radius) := by
  have hdist : 0 < dist x y := dist_pos.mpr hne
  let t := annularLatticeDepth R k (dist x y) hdist
  obtain ⟨i, hi, _⟩ := exists_unique_support_descendant_at_point μ R hR k z x hx t
  have hu : i.radius ≤ dist x y / 8 := by
    simpa only [SupportCellDescendant.radius, hi.1, t] using!
      annularLatticeDepth_radius_upper R k (dist x y) hdist
  have htop : dist x y ≤ 8 * latticeRadius R k := by
    have hb := cleanSupportCell_pair_distance_le μ R hR k z x y hx hy
    have hr := latticeRadius_pos R hR k
    linarith
  have hl : dist x y ≤ 512 * i.radius := by
    simpa only [SupportCellDescendant.radius, hi.1, t] using!
      annularLatticeDepth_radius_lower R hR k (dist x y) hdist htop
  have hxcenter := i.dist_center_of_mem x hi.2
  have hxycenter := dist_triangle y x i.center
  rw [dist_comm y x] at hxycenter
  have hr := i.radius_pos
  refine ⟨i, hi.2, hu, hl, ?_, ?_⟩
  · rw [mem_ball]
    linarith
  · rw [mem_ball]
    linarith

end

end RieszRectifiability

end OAI
