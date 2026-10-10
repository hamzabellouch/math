import OAI.NumberTheory.JointDickman.Analysis.MellinShortComparison

namespace OAI

/-! # Varying the short length on a fixed interval of origins -/
namespace JointDickman
open Finset PublishedInputs

lemma norm_short_sum_le (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n‖ ≤ H + 1 := by
  calc
    _ ≤ ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, (1 : ℝ) := sum_le_sum (fun n _ => hf n)
    _ = ((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) := by simp
    _ ≤ _ := mellin_short_interval_card_le hx hH

lemma norm_short_sum_length_difference (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x H K : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) (hHK : H ≤ K) :
    ‖(∑ n ∈ Ioc ⌊x⌋₊ ⌊x + K⌋₊, f n) -
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n‖ ≤ K - H + 1 := by
  have hab : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_mono (by linarith)
  have hbc : ⌊x + H⌋₊ ≤ ⌊x + K⌋₊ := Nat.floor_mono (by linarith)
  have hsub : Ioc ⌊x⌋₊ ⌊x + H⌋₊ ⊆ Ioc ⌊x⌋₊ ⌊x + K⌋₊ :=
    fun _ hn => mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans hbc⟩
  have hset : Ioc ⌊x⌋₊ ⌊x + K⌋₊ \ Ioc ⌊x⌋₊ ⌊x + H⌋₊ =
      Ioc ⌊x + H⌋₊ ⌊x + K⌋₊ := by
    ext n
    simp only [mem_sdiff, mem_Ioc]
    omega
  rw [← sum_sdiff hsub, add_sub_cancel_right, hset]
  have he : x + H + (K - H) = x + K := by ring
  simpa only [he] using norm_short_sum_le f hf (by linarith : 0 ≤ x + H)
    (sub_nonneg.mpr hHK)

lemma norm_shortAverage_le_two (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x H : ℝ} (hx : 0 ≤ x) (hH : 1 ≤ H) : ‖complexShortAverage f H x‖ ≤ 2 := by
  have hH0 : 0 < H := by linarith
  rw [complexShortAverage, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH0]
  apply (div_le_iff₀ hH0).mpr
  exact (norm_short_sum_le f hf hx hH0.le).trans (by linarith)

/-- Nearby lengths have uniformly close normalized averages. -/
theorem shortAverage_length_difference (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x H K : ℝ} (hx : 0 ≤ x) (hH : 1 ≤ H) (hHK : H ≤ K) :
    ‖complexShortAverage f H x - complexShortAverage f K x‖ ≤
      3 * (K - H + 1) / H := by
  have hH0 : 0 < H := by linarith
  have hK0 : 0 < K := hH0.trans_le hHK
  let S := ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n
  let T := ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + K⌋₊, f n
  have he : complexShortAverage f H x - complexShortAverage f K x =
      (S - T) / (H : ℂ) + (((K - H) / H : ℝ) : ℂ) * complexShortAverage f K x := by
    dsimp [S, T, complexShortAverage]
    push_cast
    field_simp [show (H : ℂ) ≠ 0 by exact_mod_cast hH0.ne',
      show (K : ℂ) ≠ 0 by exact_mod_cast hK0.ne']
    ring
  have htail : ‖S - T‖ ≤ K - H + 1 := by
    rw [norm_sub_rev]
    exact norm_short_sum_length_difference f hf hx hH0.le hHK
  have hcoef : 0 ≤ (K - H) / H := div_nonneg (sub_nonneg.mpr hHK) hH0.le
  rw [he]
  calc
    _ ≤ ‖(S - T) / (H : ℂ)‖ +
        ‖(((K - H) / H : ℝ) : ℂ) * complexShortAverage f K x‖ := norm_add_le _ _
    _ = ‖S - T‖ / H + ((K - H) / H) * ‖complexShortAverage f K x‖ := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hH0, Real.norm_eq_abs, abs_of_nonneg hcoef]
    _ ≤ (K - H + 1) / H + ((K - H) / H) * 2 :=
      add_le_add (div_le_div_of_nonneg_right htail hH0.le)
        (mul_le_mul_of_nonneg_left (norm_shortAverage_le_two f hf hx (hH.trans hHK)) hcoef)
    _ = (3 * (K - H) + 1) / H := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hH0.le

end JointDickman

end OAI
