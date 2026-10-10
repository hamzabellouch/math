import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.CellRegionStopping

namespace OAI

/-!
# Mass decomposition for a cell region

The clean root cell splits into the region limit and the pairwise disjoint stopping
cells. Countability of descendants and measurability of the cells turn this partition
into an exact identity between the root mass, the limit mass, and the sum of stop masses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem cellRegion_mass_identity {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    μ (cleanSupportCell μ R hR k z) = μ (cellRegionLimit μ R hR k z Good) +
      ∑' i : cellRegionStops μ R hR k z Good, μ i.val.cell := by
  let := supportCellDescendant_countable μ R hR k z
  have hd : Pairwise (fun i j : cellRegionStops μ R hR k z Good => Disjoint i.val.cell j.val.cell) := by
    intro i j hij
    exact cellRegionStops_pairwise_disjoint μ R hR k z Good i.property j.property
      (fun heq => hij (Subtype.ext heq))
  have hm : ∀ i : cellRegionStops μ R hR k z Good, MeasurableSet i.val.cell :=
    fun i => cleanSupportCell_measurable μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have hs : Disjoint (cellRegionLimit μ R hR k z Good)
      (⋃ i : cellRegionStops μ R hR k z Good, i.val.cell) := by
    apply Set.disjoint_left.mpr
    intro x hx hstop
    obtain ⟨i, hi⟩ := mem_iUnion.mp hstop
    exact Set.disjoint_left.mp
      (cellRegionLimit_disjoint_stops μ R hR k z Good i.val i.property) hx hi
  conv_lhs => rw [cleanSupportCell_eq_region_limit_union_stops μ R hR k z Good]
  rw [measure_union hs (MeasurableSet.iUnion hm), measure_iUnion hd hm]

theorem cellRegion_stopping_mass_le_top {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    (∑' i : cellRegionStops μ R hR k z Good, μ i.val.cell) ≤ μ (cleanSupportCell μ R hR k z) := by
  rw [cellRegion_mass_identity μ R hR k z Good]
  exact le_add_left le_rfl

end

end RieszRectifiability

end OAI
