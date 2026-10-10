import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelOriginalMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem active_level_subfamily_mass_sum_le {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (F : Finset (SupportCellDescendant μ R hR k z))
    (hF : F ⊆ activeLevelIndex μ R hR k z Good t)
    (Ω : Set (Ambient d)) (hΩ : ∀ i ∈ F, i.cell ⊆ Ω) :
    (∑ i : F, μ i.val.cell) ≤ μ Ω := by
  classical
  have hd : Pairwise (fun i j : F => Disjoint i.val.cell j.val.cell) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi := (mem_activeLevelIndex μ R hR k z Good t i).mp (hF i.property)
    have hj := (mem_activeLevelIndex μ R hR k z Good t j).mp (hF j.property)
    exact hij (Subtype.ext (i.val.eq_of_common_point_same_depth j.val
      (hi.1.trans hj.1.symm) x hxi hxj))
  have hm (i : F) : MeasurableSet i.val.cell :=
    cleanSupportCell_measurable μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have hsum : (∑ i : F, μ i.val.cell) = μ (⋃ i : F, i.val.cell) := by
    simpa only [tsum_fintype] using! (measure_iUnion hd hm).symm
  rw [hsum]
  exact measure_mono (iUnion_subset (fun i => hΩ i.val i.property))

theorem active_level_subfamily_radius_power_sum_le {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (F : Finset (SupportCellDescendant μ R hR k z))
    (hF : F ⊆ activeLevelIndex μ R hR k z Good t)
    (Ω : Set (Ambient d)) (hΩ : ∀ i ∈ F, i.cell ⊆ Ω) :
    (∑ i : F, (ENNReal.ofReal i.val.radius) ^ n) ≤ ENNReal.ofReal (C * 8 ^ n) * μ Ω := by
  classical
  calc
    _ ≤ ∑ i : F, ENNReal.ofReal (C * 8 ^ n) * μ i.val.cell :=
      Finset.sum_le_sum (fun i _ =>
        SupportCellDescendant.radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z i.val)
    _ = ENNReal.ofReal (C * 8 ^ n) * ∑ i : F, μ i.val.cell := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_right
      (active_level_subfamily_mass_sum_le μ R hR k z Good t F hF Ω hΩ) _

end

end RieszRectifiability

end OAI
