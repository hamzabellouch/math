import OAI.NumberTheory.CubicMoment.Estimates.SmallPartSizes

namespace OAI

/-! Explicit eventual scale margins for the dominant smooth dyad. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventual_dominant_smooth_scales (C : ℝ) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      2*Y ≤ Y^(1001/1000:ℝ) ∧ C*Y ≤ Y^(1001/1000:ℝ) ∧
      (∀ X : ℝ, Y^(9999/10000:ℝ) ≤ X → X ≤ C*Y →
        Y^(999/1000:ℝ) ≤ X/2 ∧ X/2 ≤ Y^(1001/1000:ℝ)) ∧
      (∀ Q : ℝ, Q ≤ Y^(1/100000:ℝ) → 9*Q ≤ Y^(1/10000:ℝ)) := by
  obtain ⟨T₁,h₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 1/1000 by norm_num)).eventually_ge_atTop (max 2 C))
  obtain ⟨T₂,h₂⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 9/10000 by norm_num)).eventually_ge_atTop (2:ℝ))
  obtain ⟨T₃,h₃⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 9/100000 by norm_num)).eventually_ge_atTop (9:ℝ))
  refine ⟨max 2 (max T₁ (max T₂ T₃)),le_max_left _ _,?_⟩
  intro Y hY
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := by linarith
  have hY₁ : T₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hY₂ : T₂ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hY₃ : T₃ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hp := h₁ Y hY₁
  have htwo := (le_max_left (2:ℝ) C).trans hp
  have hC := (le_max_right (2:ℝ) C).trans hp
  have hid : Y^(1/1000:ℝ)*Y = Y^(1001/1000:ℝ) := by
    conv_lhs => arg 2; rw [← Real.rpow_one Y]
    rw [← Real.rpow_add hY0]
    norm_num
  have hupper : C*Y ≤ Y^(1001/1000:ℝ) :=
    (mul_le_mul_of_nonneg_right hC hY0.le).trans_eq hid
  refine ⟨(mul_le_mul_of_nonneg_right htwo hY0.le).trans_eq hid,hupper,?_,?_⟩
  · intro X hlo hhi
    constructor
    · apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
      calc
        _ ≤ Y^(999/1000:ℝ)*Y^(9/10000:ℝ) :=
          mul_le_mul_of_nonneg_left (h₂ Y hY₂) (Real.rpow_nonneg hY0.le _)
        _ = Y^(9999/10000:ℝ) := by rw [← Real.rpow_add hY0]; norm_num
        _ ≤ X := hlo
    · have hX0 : 0 ≤ X := (Real.rpow_nonneg hY0.le _).trans hlo
      exact (div_le_self hX0 (by norm_num : (1:ℝ) ≤ 2)).trans (hhi.trans hupper)
  · intro Q hQ
    calc
      _ ≤ 9*Y^(1/100000:ℝ) := mul_le_mul_of_nonneg_left hQ (by norm_num)
      _ ≤ Y^(9/100000:ℝ)*Y^(1/100000:ℝ) :=
        mul_le_mul_of_nonneg_right (h₃ Y hY₃) (Real.rpow_nonneg hY0.le _)
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num

end CubicFirstMoment

end

end OAI
