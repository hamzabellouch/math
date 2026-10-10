import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderThreshold

namespace OAI

/-! Simultaneous preservation of the finite input and normalized metric budgets. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

theorem correction_budget_threshold {A B a N L : ℝ} (hAB : A < B) (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < ε →
      A+N*t^(1/5 : ℝ)*(1+B) ≤ B ∧ L*(1+2*B)*t^(1/5 : ℝ) ≤ a/8 := by
  obtain ⟨ε₁,hε₁,hε₁1,h₁⟩ := positive_power_threshold (N*(1+B)) (1/5) (B-A)
    (by norm_num) (sub_pos.mpr hAB)
  obtain ⟨ε₂,hε₂,_,h₂⟩ := positive_power_threshold (L*(1+2*B)) (1/5) (a/8)
    (by norm_num) (by positivity)
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,(min_le_left _ _).trans hε₁1,?_⟩
  intro t ht htε
  have hb := (h₁ t ht (htε.trans_le (min_le_left _ _))).le
  have hm := (h₂ t ht (htε.trans_le (min_le_right _ _))).le
  exact ⟨by nlinarith,hm⟩

end ClosedSurfaceR4.ExactCorrection

end

end OAI
