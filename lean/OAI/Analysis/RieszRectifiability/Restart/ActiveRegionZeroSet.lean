import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelCover

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)

def cellRegionZeroSet : Set (Ambient d) :=
  {x | cellRegionStoppingScale μ R hR k z Good x = 0}

theorem cellRegionZeroSet_closed : IsClosed (cellRegionZeroSet μ R hR k z Good) :=
  isClosed_eq (cellRegionStoppingScale_lipschitz μ R hR k z Good).continuous continuous_const

theorem cellRegionZeroSet_subset_closed_top :
    cellRegionZeroSet μ R hR k z Good ⊆ supportLatticeCell μ R hR k z := by
  intro x hx
  have hz : cellRegionStoppingScale μ R hR k z Good x = 0 := hx
  have hcl : x ∈ closure (supportLatticeCell μ R hR k z) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ht⟩ := exists_annular_lattice_depth R k ε hε
    have hsmall : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + t) := by
      rw [hz]
      exact latticeRadius_pos R hR (k + t)
    obtain ⟨i, _, hdist⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good t x hsmall
    refine ⟨i.center, (i.cell_subset_top i.center_mem_cell).1, ?_⟩
    linarith
  exact (supportLatticeCell_closed μ R hR k z).closure_eq ▸ hcl

theorem cellRegionZeroSet_compact : IsCompact (cellRegionZeroSet μ R hR k z Good) :=
  (supportLatticeCell_compact μ R hR k z).of_isClosed_subset
    (cellRegionZeroSet_closed μ R hR k z Good) (cellRegionZeroSet_subset_closed_top μ R hR k z Good)

theorem cellRegionLimit_subset_zeroSet :
    cellRegionLimit μ R hR k z Good ⊆ cellRegionZeroSet μ R hR k z Good := by
  intro x hx
  exact cellRegionStoppingScale_eq_zero_of_region_limit μ R hR k z Good x hx

end

end RieszRectifiability

end OAI
