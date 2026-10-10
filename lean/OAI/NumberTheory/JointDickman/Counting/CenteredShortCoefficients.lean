import OAI.NumberTheory.JointDickman.Analysis.ShortMellinDyadicEnergy

namespace OAI

/-! # Centering the short average before the Mellin transfer -/
namespace JointDickman
open Finset PublishedInputs

/-- The factor three accommodates a long average of norm at most two. -/
noncomputable def centeredShortCoefficients (f : ArithmeticFunction ℂ) (c : ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (f n - c) / 3, by simp⟩

theorem centeredShortCoefficients_norm_le (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {c : ℂ} (hc : ‖c‖ ≤ 2) (n : ℕ) :
    ‖centeredShortCoefficients f c n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [centeredShortCoefficients, hn]
  · change ‖if n = 0 then (0 : ℂ) else (f n - c) / 3‖ ≤ 1
    rw [ite_eq_right hn, norm_div]
    norm_num
    have hh := norm_sub_le (f n) c
    linarith [hf n]

lemma short_interval_card_error {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    |((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) - H| ≤ 1 := by
  rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : x ≤ x + H)), abs_le]
  have h1 := Nat.floor_le hx
  have h2 := Nat.floor_le (show 0 ≤ x + H by linarith)
  have h3 := Nat.lt_floor_add_one x
  have h4 := Nat.lt_floor_add_one (x + H)
  constructor <;> linarith

/-- Centering commutes with short averaging up to the exact integer count. -/
theorem centeredShortCoefficients_short_identity (f : ArithmeticFunction ℂ) (c : ℂ)
    (x H : ℝ) :
    complexShortAverage f H x - c =
      3 * complexShortAverage (centeredShortCoefficients f c) H x +
        (((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℂ) / (H : ℂ) - 1) * c := by
  have hterm (n : ℕ) (hn : n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊) :
      centeredShortCoefficients f c n = (f n - c) / 3 := by
    have hn0 : n ≠ 0 := ne_of_gt ((Nat.zero_le ⌊x⌋₊).trans_lt (mem_Ioc.mp hn).1)
    simp [centeredShortCoefficients, hn0]
  have hs : (∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, centeredShortCoefficients f c n) =
      ((∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n) -
        ((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℂ) * c) / 3 := by
    calc
      _ = ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, (f n - c) / 3 := sum_congr rfl hterm
      _ = (∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, (f n - c)) / 3 := (sum_div _ _ _).symm
      _ = _ := by rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  simp only [complexShortAverage]
  rw [hs]
  ring

/-- The integer count costs at most `2/H`; no regularity of the coefficients
is used in this centering step. -/
theorem centeredShortCoefficients_short_error (f : ArithmeticFunction ℂ)
    {c : ℂ} (hc : ‖c‖ ≤ 2) {x H : ℝ} (hx : 0 ≤ x) (hH : 0 < H) :
    ‖complexShortAverage f H x - c‖ ≤
      3 * ‖complexShortAverage (centeredShortCoefficients f c) H x‖ + 2 / H := by
  have hcard := short_interval_card_error hx hH.le
  have hfactor : ‖((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℂ) / (H : ℂ) - 1‖ ≤ 1 / H := by
    have he : ((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℂ) / (H : ℂ) - 1 =
        ((((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) - H) / H : ℝ) := by
      push_cast
      field_simp [show (H : ℂ) ≠ 0 by exact_mod_cast hH.ne']
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hH]
    exact div_le_div_of_nonneg_right hcard hH.le
  rw [centeredShortCoefficients_short_identity f c x H]
  calc
    _ ≤ ‖3 * complexShortAverage (centeredShortCoefficients f c) H x‖ +
        ‖(((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℂ) / (H : ℂ) - 1) * c‖ := norm_add_le _ _
    _ ≤ 3 * ‖complexShortAverage (centeredShortCoefficients f c) H x‖ + (1 / H) * 2 := by
      rw [norm_mul, norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num]
      exact add_le_add le_rfl (mul_le_mul hfactor hc (norm_nonneg _) (by positivity))
    _ = _ := by ring

end JointDickman

end OAI
