import OAI.NumberTheory.CubicMoment.Estimates.MellinMomentPowers

namespace OAI

/-! Concrete height margins and tail exponents for independently weighted
prime factors. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventual_independent_shift_height_bound :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ t τ : ℝ,
      |t| ≤ Y^(9/25:ℝ) → |τ| ≤ Y^(1/1000:ℝ) → |t-τ| ≤ Y^(361/1000:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 1/1000 by norm_num)).eventually_ge_atTop (2:ℝ))
  refine ⟨max 1 T,?_⟩
  intro Y hY t τ ht hτ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hτ' : |τ| ≤ Y^(9/25:ℝ) := hτ.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  calc
    _ ≤ |t|+|τ| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le t 0 τ
    _ ≤ 2*Y^(9/25:ℝ) := by linarith
    _ ≤ Y^(1/1000:ℝ)*Y^(9/25:ℝ) :=
      mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; norm_num

lemma coordinate_tail_power (k : ℕ) {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^2*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+6)))*J)^2 =
      (2*K^2*J^2)*Y^(-10:ℝ) := by
  have hp : (Y^(1/1000:ℝ))^(1000*(2*k+6)) = Y^(2*k+6) := by
    rw [← Real.rpow_mul_natCast hY.le]
    have he : (1/1000:ℝ)*(1000*(2*k+6):ℕ) = ((2*k+6:ℕ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
  have hd : Y^(2*k)/Y^(2*k+6) = Y^(-6:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_sub hY]
    congr 1
    push_cast
    ring
  rw [hp,show K*Y^(2*k)/Y^(2*k+6) = K*(Y^(2*k)/Y^(2*k+6)) by ring,hd]
  have he : Y^2*(Y^(-6:ℝ))^2 = Y^(-10:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_two,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^2*(Y^(-6:ℝ))^2) := by ring
    _ = _ := by rw [he]

lemma coordinate_tail_le_short_tail (k : ℕ) {Y K J : ℝ} (hY : 1 ≤ Y) :
    2*Y^2*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+6)))*J)^2 ≤
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  rw [coordinate_tail_power k (zero_lt_one.trans_le hY)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
