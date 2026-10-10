import OAI.NumberTheory.CubicMoment.Estimates.SmallPartGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Subpower local data satisfy the quantitative conductor margins. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventual_small_part_conductor_size :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y B V Q : ℝ, Y₀ ≤ Y →
      0 ≤ B → 0 ≤ V → 0 ≤ Q → B ≤ Y^(1/10000:ℝ) →
      V ≤ Y^(1/10000:ℝ) → Q ≤ Y^(1/10000:ℝ) →
      B*(9*V^2*Q)^2 ≤ Y^(1/1000:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 3/10000 by norm_num)).eventually_ge_atTop (81:ℝ))
  refine ⟨max 2 T,le_max_left _ _,?_⟩
  intro Y B V Q hY hB hV hQ hBY hVY hQY
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := by linarith
  have hscale : 81 ≤ Y^(3/10000:ℝ) := hT Y ((le_max_right _ _).trans hY)
  have hinner : 9*V^2*Q ≤ 9*Y^(3/10000:ℝ) := by
    calc
      _ ≤ 9*(Y^(1/10000:ℝ))^2*Y^(1/10000:ℝ) := by gcongr
      _ = _ := by
        rw [← Real.rpow_mul_natCast hY0.le,mul_assoc,← Real.rpow_add hY0]
        norm_num
  calc
    _ ≤ Y^(1/10000:ℝ)*(9*Y^(3/10000:ℝ))^2 :=
      mul_le_mul hBY (pow_le_pow_left₀ (by positivity) hinner 2)
        (sq_nonneg _) (Real.rpow_nonneg hY0.le _)
    _ = 81*Y^(7/10000:ℝ) := by
      rw [mul_pow,← Real.rpow_mul_natCast hY0.le]
      rw [show (9:ℝ)^2 = 81 by norm_num]
      rw [mul_left_comm,← Real.rpow_add hY0]
      norm_num
    _ ≤ Y^(3/10000:ℝ)*Y^(7/10000:ℝ) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hY0.le _)
    _ = _ := by rw [← Real.rpow_add hY0]; norm_num

theorem eventual_small_part_modulus_size :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y V Q : ℝ, Y₀ ≤ Y →
      0 ≤ V → 0 ≤ Q → V ≤ Y^(1/10000:ℝ) → Q ≤ Y^(1/10000:ℝ) →
      9*V^2*Q ≤ Y^(1/1000:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 7/10000 by norm_num)).eventually_ge_atTop (9:ℝ))
  refine ⟨max 2 T,le_max_left _ _,?_⟩
  intro Y V Q hY hV hQ hVY hQY
  have hY0 : 0 < Y := by have := (le_max_left (2:ℝ) T).trans hY; linarith
  have hscale : 9 ≤ Y^(7/10000:ℝ) := hT Y ((le_max_right _ _).trans hY)
  calc
    _ ≤ 9*(Y^(1/10000:ℝ))^2*Y^(1/10000:ℝ) := by gcongr
    _ = 9*Y^(3/10000:ℝ) := by
      rw [← Real.rpow_mul_natCast hY0.le,mul_assoc,← Real.rpow_add hY0]
      norm_num
    _ ≤ Y^(7/10000:ℝ)*Y^(3/10000:ℝ) :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hY0.le _)
    _ = _ := by rw [← Real.rpow_add hY0]; norm_num

lemma small_part_smaller_than_row {Y V A : ℝ} (hY : 1 < Y)
    (hV : V ≤ Y^(1/10000:ℝ)) (hA : Y^(1/1000:ℝ) ≤ A) : V < A :=
  hV.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num)).trans_le hA)

end CubicFirstMoment

end

end OAI
