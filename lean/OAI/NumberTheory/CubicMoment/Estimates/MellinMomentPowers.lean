import OAI.NumberTheory.CubicMoment.Estimates.FullMellinMoment

namespace OAI

/-! The fixed powers in the central-plus-tail short-convolution estimate. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma short_mellin_tail_power {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^2*((K*Y^2/(Y^(9/25:ℝ))^20)*J)^2 =
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  have hp : (Y^(9/25:ℝ))^20 = Y^(36/5:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le]
    norm_num
  have hd : Y^2/Y^(36/5:ℝ) = Y^(-26/5:ℝ) := by
    rw [← Real.rpow_two,← Real.rpow_sub hY]
    norm_num
  rw [hp,show K*Y^2/Y^(36/5:ℝ) = K*(Y^2/Y^(36/5:ℝ)) by ring,hd]
  have he : Y^2*(Y^(-26/5:ℝ))^2 = Y^(-42/5:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_two,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^2*(Y^(-26/5:ℝ))^2) := by ring
    _ = _ := by rw [he]

theorem absorb_short_mellin_bounds {ε : ℝ} (hε : 0 < ε) (C E : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
      C*Y^(7/3-ε)+E*Y^(-42/5:ℝ) ≤ Y^(7/3-min ε (1/3)/2) := by
  let η := min ε (1/3:ℝ)
  have hη : 0 < η := lt_min hε (by norm_num)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < η/2 by linarith)).eventually_ge_atTop (C+E))
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hηε : η ≤ ε := min_le_left _ _
  have hη3 : η ≤ 1/3 := min_le_right _ _
  calc
    _ ≤ C*Y^(7/3-η)+E*Y^(7/3-η) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) hC
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) hE
    _ = (C+E)*Y^(7/3-η) := by ring
    _ ≤ Y^(η/2)*Y^(7/3-η) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; dsimp [η]; ring

end CubicFirstMoment

end

end OAI
