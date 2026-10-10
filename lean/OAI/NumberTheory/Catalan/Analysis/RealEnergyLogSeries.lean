import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section
open Set

namespace InternalCatalan

theorem energy_summable_norm_complex_power_div {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖z ^ k / (k : ℂ)‖) := by
  refine (summable_geometric_of_norm_lt_one hz).norm.of_nonneg_of_le
    (fun _ => norm_nonneg _) ?_
  intro k
  simp only [norm_div, norm_pow, Complex.norm_natCast]
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hk)
    exact div_le_self (pow_nonneg (norm_nonneg z) k) hk1

theorem energy_hasSum_re_power_div {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (z ^ k).re / (k : ℝ))
      (-Real.log ‖1 - z‖) := by
  simpa only [Complex.div_natCast_re, Complex.neg_re, Complex.log_re] using
    Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz)

theorem energy_hasSum_re_power_div_succ {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (z ^ (k + 1)).re / ((k + 1 : ℕ) : ℝ))
      (-Real.log ‖1 - z‖) := by
  apply (hasSum_nat_add_iff
    (f := fun k : ℕ => (z ^ k).re / (k : ℝ)) 1).2
  simpa using energy_hasSum_re_power_div hz

theorem energy_summable_abs_re_power_div {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => |(z ^ k).re / (k : ℝ)|) := by
  refine (energy_summable_norm_complex_power_div hz).of_nonneg_of_le
    (fun _ => abs_nonneg _) ?_
  intro k
  simpa only [Complex.div_natCast_re] using
    Complex.abs_re_le_norm (z ^ k / (k : ℂ))

theorem energy_summable_re_power_div {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => (z ^ k).re / (k : ℝ)) :=
  (energy_hasSum_re_power_div hz).summable

theorem energy_hasSum_real_power_div {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u ^ k / (k : ℝ)) (-Real.log (1 - u)) := by
  have huNorm : ‖(u : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_lt.mpr hu
  have hnorm : ‖(1 : ℂ) - (u : ℂ)‖ = 1 - u := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu.2)]
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, hnorm] using
    energy_hasSum_re_power_div huNorm

theorem energy_hasSum_real_power_div_succ {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => u ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (-Real.log (1 - u)) := by
  apply (hasSum_nat_add_iff (f := fun k : ℕ => u ^ k / (k : ℝ)) 1).2
  simpa using energy_hasSum_real_power_div hu

theorem energy_summable_abs_real_power_div {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    Summable (fun k : ℕ => |u ^ k / (k : ℝ)|) := by
  have huNorm : ‖(u : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_lt.mpr hu
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using
    energy_summable_abs_re_power_div huNorm

theorem energy_mul_mem_Ioo {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    x * y ∈ Ioo (-1 : ℝ) 1 := by
  apply abs_lt.mp
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (abs_lt.mpr hy).le (abs_nonneg x)
    _ < 1 := by simpa only [mul_one] using abs_lt.mpr hx

theorem energy_hasSum_mul_power_div {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => (x * y) ^ k / (k : ℝ))
      (-Real.log (1 - x * y)) :=
  energy_hasSum_real_power_div (energy_mul_mem_Ioo hx hy)

theorem energy_summable_abs_mul_power_div {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    Summable (fun k : ℕ => |(x * y) ^ k / (k : ℝ)|) :=
  energy_summable_abs_real_power_div (energy_mul_mem_Ioo hx hy)

end InternalCatalan

end

end OAI
