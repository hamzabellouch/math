import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelWeights

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def supportImmediateChildren {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    Finset (SupportCellDescendant μ R hR k z) :=
  activeLevelIndex μ R hR k z (fun _ => True) 1

theorem mem_supportImmediateChildren {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (i : SupportCellDescendant μ R hR k z) :
    i ∈ supportImmediateChildren μ R hR k z ↔ i.depth = 1 := by
  rw [supportImmediateChildren, mem_activeLevelIndex]
  change (i.depth = 1 ∧ activeRegionCell (fun _ => True) i) ↔ i.depth = 1
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ => trivial⟩⟩

theorem supportImmediateChild_radius {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (i : supportImmediateChildren μ R hR k z) :
    i.val.radius = latticeRadius R k / 64 := by
  have hi := (mem_supportImmediateChildren μ R hR k z i.val).mp i.property
  simp only [SupportCellDescendant.radius, hi, latticeRadius_succ]

theorem cleanSupportCell_eq_immediate_children {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    cleanSupportCell μ R hR k z = ⋃ i : supportImmediateChildren μ R hR k z, i.val.cell := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, _⟩ := exists_unique_support_descendant_at_point μ R hR k z x hx 1
    exact mem_iUnion.mpr ⟨⟨i, (mem_supportImmediateChildren μ R hR k z i).mpr hi.1⟩, hi.2⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact i.val.cell_subset_top hi

theorem supportImmediateChildren_pairwise_disjoint {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    Pairwise (fun i j : supportImmediateChildren μ R hR k z => Disjoint i.val.cell j.val.cell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi := (mem_supportImmediateChildren μ R hR k z i.val).mp i.property
  have hj := (mem_supportImmediateChildren μ R hR k z j.val).mp j.property
  exact hij (Subtype.ext (i.val.eq_of_common_point_same_depth j.val (hi.trans hj.symm) x hxi hxj))

theorem supportImmediateChildren_card_le {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    (supportImmediateChildren μ R hR k z).card ≤ 257 ^ d := by
  have hnear : ∀ i ∈ supportImmediateChildren μ R hR k z,
      dist i.center (z : Ambient d) ≤ 128 * latticeRadius R (k + 1) := by
    intro i _
    rw [latticeRadius_succ]
    linarith [i.center_dist_top]
  have h := active_level_local_card_bound μ R hR k z (fun _ => True) 1
    (supportImmediateChildren μ R hR k z)
    (fun i hi => (mem_activeLevelIndex μ R hR k z (fun _ => True) 1 i).mp hi)
    (z : Ambient d) 128 (by norm_num) hnear
  norm_num at h
  exact_mod_cast h

theorem cleanSupportCell_mass_eq_immediate_children {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ (cleanSupportCell μ R hR k z) = ∑ i : supportImmediateChildren μ R hR k z, μ i.val.cell := by
  rw [cleanSupportCell_eq_immediate_children μ R hR k z]
  have h := measure_iUnion (μ := μ) (supportImmediateChildren_pairwise_disjoint μ R hR k z)
    (fun i : supportImmediateChildren μ R hR k z => cleanSupportCell_measurable μ R hR
      (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩)
  simpa only [tsum_fintype] using! h

end

end RieszRectifiability

end OAI
