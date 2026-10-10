import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Nearly optimal countable covers at a prescribed positive scale. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma iSup_nonempty_ediam {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X) :
    (⨆ _ : S.Nonempty, ediam S) = ediam S := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · simp only [iSup_pos hS]

lemma exists_small_hausdorff_cover {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[1] : Measure X) A < ∞)
    (r ε : ℝ≥0∞) (hr : 0 < r) (hε : 0 < ε) :
    ∃ T : ℕ → Set X, A ⊆ ⋃ k, T k ∧ (∀ k, ediam (T k) ≤ r) ∧
      (∑' k, ediam (T k)) < (μH[1] : Measure X) A + ε := by
  have hle : (⨅ (T : ℕ → Set X) (_ : A ⊆ ⋃ k, T k) (_ : ∀ k, ediam (T k) ≤ r),
      ∑' k, ⨆ _ : (T k).Nonempty, ediam (T k) ^ (1 : ℝ)) ≤ (μH[1] : Measure X) A := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hlt := hle.trans_lt (ENNReal.lt_add_right hA.ne hε.ne')
  simp only [iInf_lt_iff] at hlt
  obtain ⟨T, hc, hd, hcost⟩ := hlt
  refine ⟨T, hc, hd, ?_⟩
  simpa only [ENNReal.rpow_one, iSup_nonempty_ediam] using hcost

end CircleDomainRigidity

end

end OAI
