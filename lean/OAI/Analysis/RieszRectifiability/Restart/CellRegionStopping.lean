import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.PointCellChains
import OAI.Analysis.RieszRectifiability.Foundations.SupportDescendantCountable

namespace OAI

/-!
# Limits and stops of good cell regions

The limit region consists of points whose containing descendants all satisfy a
chosen good-cell predicate. Stops are the first failures along containment chains.
Countability of descendants makes the limit region measurable by removing the
union of bad cells from the starting cell.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def cellRegionLimit {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) : Set (Ambient d) :=
  {x ∈ cleanSupportCell μ R hR k z | ∀ i, x ∈ i.cell → Good i}

def cellRegionStops {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    Set (SupportCellDescendant μ R hR k z) :=
  {i | ¬Good i ∧ ∀ j, j.depth < i.depth → i.cell ⊆ j.cell → Good j}

theorem cellRegionLimit_measurable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    MeasurableSet (cellRegionLimit μ R hR k z Good) := by
  let := supportCellDescendant_countable μ R hR k z
  have heq : cellRegionLimit μ R hR k z Good =
      cleanSupportCell μ R hR k z \ ⋃ i : {i // ¬Good i}, i.val.cell := by
    ext x
    simp only [cellRegionLimit, mem_ofPred_eq, mem_sdiff, mem_iUnion, not_exists]
    constructor
    · rintro ⟨hx, hall⟩
      exact ⟨hx, fun i hi => i.property (hall i.val hi)⟩
    · rintro ⟨hx, hbad⟩
      refine ⟨hx, ?_⟩
      intro i hi
      by_contra hnot
      exact hbad ⟨i, hnot⟩ hi
  rw [heq]
  exact (cleanSupportCell_measurable μ R hR k z).diff
    (MeasurableSet.iUnion fun i => cleanSupportCell_measurable μ R hR
      (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩)

theorem exists_first_failing_cell {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (x : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z)
    (hnot : x ∉ cellRegionLimit μ R hR k z Good) :
    ∃ i ∈ cellRegionStops μ R hR k z Good, x ∈ i.cell := by
  classical
  have hb : ∃ t : ℕ, ∃ i : SupportCellDescendant μ R hR k z,
      i.depth = t ∧ x ∈ i.cell ∧ ¬Good i := by
    by_contra hnone
    apply hnot
    refine ⟨hx, ?_⟩
    intro i hi
    by_contra hbad
    exact hnone ⟨i.depth, i, rfl, hi, hbad⟩
  obtain ⟨i, hi, hxi, hbad⟩ := Nat.find_spec hb
  refine ⟨i, ⟨hbad, ?_⟩, hxi⟩
  intro j hj hsub
  by_contra hjbad
  have hmin := Nat.find_min' hb ⟨j, rfl, hsub hxi, hjbad⟩
  omega

theorem cellRegionStops_pairwise_disjoint {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    (cellRegionStops μ R hR k z Good).Pairwise (fun i j => Disjoint i.cell j.cell) := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_trichotomy i.depth j.depth with hlt | heq | hgt
  · exact hi.1 (hj.2 i hlt (j.cell_nested_of_common_point i hlt.le x hxj hxi))
  · exact hne (i.eq_of_common_point_same_depth j heq x hxi hxj)
  · exact hj.1 (hi.2 j hgt (i.cell_nested_of_common_point j hgt.le x hxi hxj))

theorem cellRegionLimit_disjoint_stops {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good) :
    Disjoint (cellRegionLimit μ R hR k z Good) i.cell := by
  apply Set.disjoint_left.mpr
  intro x hx hxi
  exact hi.1 (hx.2 i hxi)

theorem cleanSupportCell_eq_region_limit_union_stops {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    cleanSupportCell μ R hR k z = cellRegionLimit μ R hR k z Good ∪
      ⋃ i : cellRegionStops μ R hR k z Good, i.val.cell := by
  ext x
  constructor
  · intro hx
    by_cases hgood : x ∈ cellRegionLimit μ R hR k z Good
    · exact Or.inl hgood
    · obtain ⟨i, hi, hxi⟩ := exists_first_failing_cell μ R hR k z Good x hx hgood
      exact Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  · rintro (hx | hx)
    · exact hx.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact i.val.cell_subset_top hi

end

end RieszRectifiability

end OAI
