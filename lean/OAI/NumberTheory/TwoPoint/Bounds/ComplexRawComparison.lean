import OAI.NumberTheory.TwoPoint.Bounds.ComplexFullDilation
import OAI.NumberTheory.TwoPoint.Bounds.MultiplicativeExtraction
import OAI.NumberTheory.TwoPoint.Bounds.NearbyCutoffs
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI

/-! Raw complex correlations retain the actual prime-dependent extraction cost.
This is essential when the padding includes small primes. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma correlation_oneBounded {f g : ℕ → ℂ} (hf : OneBounded f)
    (hg : OneBounded g) (h : ℕ) : OneBounded (fun n => f n * g (n + h)) := by
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul (hf n hn) (hg (n + h) (by omega)) (norm_nonneg _) zero_le_one).trans
    (by norm_num)

lemma dilated_correlation_extraction {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u h : ℕ) (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ p, p.Prime → p ∣ u → p ∈ P)
    (T : ℝ) (hT : 0 < T) :
    ‖positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ / (T : ℂ) -
      (f u * g u) * (positivePrefix (fun n => f n * g (n + h)) ⌊T / u⌋₊ /
        (T : ℂ))‖ ≤
      (1 / (u : ℝ)) * (4 * (∑ p ∈ P, 1 / (p : ℝ))) + 4 * P.card / T := by
  have he : positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ -
      (f u * g u) * positivePrefix (fun n => f n * g (n + h)) ⌊T / u⌋₊ =
      positivePrefix (multiplicativeExtractionGap f g u h) ⌊T / u⌋₊ := by
    unfold positivePrefix multiplicativeExtractionGap
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [← mul_div_assoc, ← sub_div, he, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT]
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hfloor : (⌊T / u⌋₊ : ℝ) ≤ T / u := Nat.floor_le (div_nonneg hT.le huR.le)
  apply (div_le_iff₀ hT).mpr
  calc
    _ ≤ 4 * (⌊T / u⌋₊ : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card :=
      multiplicativeExtraction_sum_bound hfm hgm hf hg u h _ hu P hP hcover
    _ ≤ 4 * (T / u) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card := by
      gcongr
    _ = _ := by field_simp

lemma dilated_correlation_bin_error {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u h : ℕ) (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ p, p.Prime → p ∣ u → p ∈ P)
    (X T η : ℝ) (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : X * Real.exp (-η) ≤ T / u) (hhi : T / u ≤ X) :
    ‖positivePrefix (fun n => f (u * n) * g (u * (n + h))) (⌊T⌋₊ / u) /
        (T : ℂ) -
      ((f u * g u) / (u : ℂ)) *
        (positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ))‖ ≤
      (1 / (u : ℝ)) * ((4 * (∑ p ∈ P, 1 / (p : ℝ))) + 2 * η + 1 / X) +
        4 * P.card / T := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hY : 0 < T / u := (mul_pos hX (Real.exp_pos _)).trans_le hlo
  have hT : 0 < T := (div_pos_iff_of_pos_right huR).mp hY
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  let C := f u * g u
  let A := positivePrefix (fun n => f n * g (n + h)) ⌊T / u⌋₊ / ((T / u : ℝ) : ℂ)
  let B := positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)
  have hC : ‖C‖ ≤ 1 := by
    dsimp [C]
    rw [norm_mul]
    exact (mul_le_mul (hf u hu) (hg u hu) (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hnear : ‖A - B‖ ≤ 2 * η + 1 / X :=
    real_prefix_log_bin _ (correlation_oneBounded hf hg h) X (T / u) η hX hη hlo hhi
  have hscale : C * (positivePrefix (fun n => f n * g (n + h)) ⌊T / u⌋₊ /
      (T : ℂ)) = (C / (u : ℂ)) * A := by
    dsimp [A]
    push_cast
    field_simp [huC, hTC]
  rw [← Nat.floor_div_natCast]
  have he := dilated_correlation_extraction hfm hgm hf hg u h hu P hP hcover T hT
  change ‖_ - (C / (u : ℂ)) * B‖ ≤ _
  calc
    _ ≤ ‖positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ /
        (T : ℂ) - (C / (u : ℂ)) * A‖ + ‖(C / (u : ℂ)) * (A - B)‖ := by
      have heq : positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ /
          (T : ℂ) - (C / (u : ℂ)) * B =
          (positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ /
            (T : ℂ) - (C / (u : ℂ)) * A) + (C / (u : ℂ)) * (A - B) := by ring
      rw [heq]
      exact norm_add_le _ _
    _ ≤ ((1 / (u : ℝ)) * (4 * (∑ p ∈ P, 1 / (p : ℝ))) + 4 * P.card / T) +
        (1 / (u : ℝ)) * (2 * η + 1 / X) := by
      apply add_le_add
      · simpa only [← hscale, C] using he
      · rw [norm_mul, norm_div, Complex.norm_natCast]
        exact mul_le_mul (div_le_div_of_nonneg_right hC huR.le) hnear
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
