import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelWeights
import OAI.Analysis.RieszRectifiability.Packing.LatticeMassPacking

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem SupportCellDescendant.radius_power_le_mass {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) (i : SupportCellDescendant μ R hR k z) :
    (ENNReal.ofReal i.radius) ^ n ≤ ENNReal.ofReal (C * 8 ^ n) * μ i.cell := by
  have hci : AdmissibleRadius μ (i.radius / 8) := by
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using! i.core_admissible hcore
  have hl := (cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR
    (k + i.depth) hci ⟨i.center, i.mem_net⟩).1
  change ENNReal.ofReal ((i.radius / 8) ^ n / C) ≤ μ i.cell at hl
  have heq : (ENNReal.ofReal i.radius) ^ n =
      ENNReal.ofReal (C * 8 ^ n) * ENNReal.ofReal ((i.radius / 8) ^ n / C) := by
    rw [← ENNReal.ofReal_pow i.radius_pos.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * 8 ^ n)]
    congr 1
    rw [div_pow]
    field_simp
  rw [heq]
  exact mul_le_mul_right hl _

theorem active_level_cell_mass_sum_le_top {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ) :
    (∑ i : activeLevelIndex μ R hR k z Good t, μ i.val.cell) ≤
      μ (cleanSupportCell μ R hR k z) := by
  classical
  let F := activeLevelIndex μ R hR k z Good t
  have hd : Pairwise (fun i j : F => Disjoint i.val.cell j.val.cell) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi := (mem_activeLevelIndex μ R hR k z Good t i).mp i.property
    have hj := (mem_activeLevelIndex μ R hR k z Good t j).mp j.property
    exact hij (Subtype.ext (i.val.eq_of_common_point_same_depth j.val
      (hi.1.trans hj.1.symm) x hxi hxj))
  have hm (i : F) : MeasurableSet i.val.cell :=
    cleanSupportCell_measurable μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have hsum : (∑ i : F, μ i.val.cell) = μ (⋃ i : F, i.val.cell) := by
    simpa only [tsum_fintype] using! (measure_iUnion hd hm).symm
  change (∑ i : F, μ i.val.cell) ≤ _
  rw [hsum]
  exact measure_mono (iUnion_subset (fun i => i.val.cell_subset_top))

theorem active_level_radius_power_sum_le_top {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ) :
    (∑ i : activeLevelIndex μ R hR k z Good t, (ENNReal.ofReal i.val.radius) ^ n) ≤
      ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z) := by
  classical
  calc
    _ ≤ ∑ i : activeLevelIndex μ R hR k z Good t, ENNReal.ofReal (C * 8 ^ n) * μ i.val.cell :=
      Finset.sum_le_sum (fun i _ =>
        SupportCellDescendant.radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z i.val)
    _ = ENNReal.ofReal (C * 8 ^ n) *
        ∑ i : activeLevelIndex μ R hR k z Good t, μ i.val.cell := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_right (active_level_cell_mass_sum_le_top μ R hR k z Good t) _

end

end RieszRectifiability

end OAI
