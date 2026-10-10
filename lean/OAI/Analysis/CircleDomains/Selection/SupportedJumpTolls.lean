import OAI.Analysis.CircleDomains.Selection.JumpTollLowerBound

namespace OAI

/-! For a dust-supported toll, restricting the neighborhood supremum to
the dust has no effect. -/

open Set
open scoped ENNReal

namespace CircleDomainRigidity

variable {X : Type*}

theorem neighborhoodTollSup_inter_eq (B V : Set X) (m : X → ℝ≥0∞)
    (hm : ∀x ∉ B, m x = 0) : neighborhoodTollSup m (B ∩ V) = neighborhoodTollSup m V := by
  unfold neighborhoodTollSup
  apply le_antisymm
  · exact iSup_le fun x => iSup_le fun hx => le_iSup_of_le x (le_iSup_of_le hx.2 le_rfl)
  · refine iSup_le fun x => iSup_le fun hx => ?_
    by_cases hxB : x ∈ B
    · exact le_iSup_of_le x (le_iSup_of_le ⟨hxB, hx⟩ le_rfl)
    · rw [hm x hxB]
      exact bot_le

variable [MetricSpace X]

theorem fixedWidthJumpToll_eq_neighborhood (B : Set X) (V : Set X)
    (m : X → ℝ≥0∞) (hm : ∀x ∉ B, m x = 0) (ρ : ℝ≥0∞) (τ : ℝ) :
    fixedWidthJumpToll B m ρ τ V = max ρ (neighborhoodTollSup m (Metric.thickening τ V)) := by
  rw [fixedWidthJumpToll, neighborhoodTollSup_inter_eq B _ m hm]

end CircleDomainRigidity

end OAI
