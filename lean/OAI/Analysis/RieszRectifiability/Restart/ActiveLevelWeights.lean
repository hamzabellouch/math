import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelPacking
import OAI.Analysis.RieszRectifiability.Nets.FiniteCoverCutoff
import OAI.Analysis.RieszRectifiability.Foundations.FiniteNormalizedWeights

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)

def activeLevelIndex : Finset (SupportCellDescendant μ R hR k z) :=
  (activeRegionLevel_finite μ R hR k z Good t).toFinset

theorem mem_activeLevelIndex (i : SupportCellDescendant μ R hR k z) :
    i ∈ activeLevelIndex μ R hR k z Good t ↔
      i ∈ activeRegionLevel μ R hR k z Good t := by
  classical
  exact (activeRegionLevel_finite μ R hR k z Good t).mem_toFinset

def activeLevelCutoff (i : SupportCellDescendant μ R hR k z) (x : Ambient d) : ℝ :=
  finiteCoverCutoff i.center (latticeRadius R (k + t)) x

def activeLevelWeight (i : SupportCellDescendant μ R hR k z) (x : Ambient d) : ℝ :=
  finiteNormalizedWeight (activeLevelIndex μ R hR k z Good t)
    (fun j => activeLevelCutoff μ R hR k z t j x) i

theorem activeLevelWeight_nonneg (i : SupportCellDescendant μ R hR k z) (x : Ambient d) :
    0 ≤ activeLevelWeight μ R hR k z Good t i x :=
  finiteNormalizedWeight_nonneg _ _ i (finiteCoverCutoff_nonneg _ _ _)

theorem activeLevelWeight_sum_le_one (x : Ambient d) :
    (∑ i ∈ activeLevelIndex μ R hR k z Good t,
      activeLevelWeight μ R hR k z Good t i x) ≤ 1 :=
  finiteNormalizedWeight_sum_le_one _ _

theorem activeLevelWeight_sum_eq_one (x : Ambient d)
    (hx : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + t)) :
    (∑ i ∈ activeLevelIndex μ R hR k z Good t,
      activeLevelWeight μ R hR k z Good t i x) = 1 := by
  classical
  apply finiteNormalizedWeight_sum_eq_one
  obtain ⟨i, hi, hxi⟩ :=
    exists_active_level_center_of_small_stopping_scale μ R hR k z Good t x hx
  have hiF := (mem_activeLevelIndex μ R hR k z Good t i).mpr hi
  have hone : activeLevelCutoff μ R hR k z t i x = 1 :=
    finiteCoverCutoff_eq_one _ _ (latticeRadius_pos R hR (k + t)) _ hxi.le
  rw [← hone]
  exact Finset.single_le_sum (fun j _ => finiteCoverCutoff_nonneg j.center _ x) hiF

theorem activeLevelWeight_ne_zero_iff (i : SupportCellDescendant μ R hR k z)
    (x : Ambient d) :
    activeLevelWeight μ R hR k z Good t i x ≠ 0 ↔
      dist x i.center < 4 * latticeRadius R (k + t) := by
  rw [activeLevelWeight, ne_eq, finiteNormalizedWeight_eq_zero_iff]
  exact finiteCoverCutoff_ne_zero_iff _ _ (latticeRadius_pos R hR (k + t)) _

theorem active_level_cutoff_support_card_bound (x : Ambient d) :
    ((activeLevelIndex μ R hR k z Good t).filter
      (fun i => activeLevelCutoff μ R hR k z t i x ≠ 0)).card ≤ (9 : ℝ) ^ d := by
  classical
  have h := active_level_local_card_bound μ R hR k z Good t
    ((activeLevelIndex μ R hR k z Good t).filter
      (fun i => activeLevelCutoff μ R hR k z t i x ≠ 0))
    (fun i hi => (mem_activeLevelIndex μ R hR k z Good t i).mp (Finset.mem_filter.mp hi).1)
    x 4 (by norm_num) (by
      intro i hi
      have hnear := (finiteCoverCutoff_ne_zero_iff i.center _
        (latticeRadius_pos R hR (k + t)) x).mp (Finset.mem_filter.mp hi).2
      simpa only [dist_comm] using! hnear.le)
  norm_num at h ⊢
  exact h

end

end RieszRectifiability

end OAI
