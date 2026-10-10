import OAI.NumberTheory.JointDickman.Analysis.MellinLowFrequencyEnergy
import OAI.NumberTheory.JointDickman.Amplification.CanonicalTypicalDensity

namespace OAI

/-! # The effect of the typical-set cutoff on bounded-frequency energy -/
namespace JointDickman
open Finset MeasureTheory
open scoped Classical

lemma angularMellinPolynomial_sub (S : Finset ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    angularMellinPolynomial S (fun n => a n-b n) t =
      angularMellinPolynomial S a t-angularMellinPolynomial S b t := by
  unfold angularMellinPolynomial
  simp_rw [sub_div, sub_mul]
  rw [Finset.sum_sub_distrib]

lemma norm_angularMellinPolynomial_le (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖angularMellinPolynomial S a t‖ ≤ ∑ n ∈ S, ‖a n‖ / n := by
  unfold angularMellinPolynomial
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div, Complex.norm_natCast]

lemma angularMellin_restriction_difference (E : ℕ → Prop) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {N K : ℕ} (hN : 0 < N) (t : ℝ) :
    ‖angularMellinPolynomial (Ioc N K) (fun n => if E n then f n else 0) t -
      angularMellinPolynomial (Ioc N K) f t‖ ≤
      (((Ioc N K).filter fun n => ¬E n).card : ℝ) / N := by
  rw [← angularMellinPolynomial_sub]
  apply (norm_angularMellinPolynomial_le _ _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc N K, if E n then 0 else (1/(N : ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hN.trans (mem_Ioc.mp hn).1
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      by_cases hE : E n
      · simp [hE]
      · simp only [hE, ite_false, zero_sub, norm_neg]
        exact (div_le_div_of_nonneg_right (hf n) hn0.le).trans
          (one_div_le_one_div_of_le hN0 (by exact_mod_cast (mem_Ioc.mp hn).1.le))
    _ = _ := by
      calc
        _ = ∑ n ∈ Ioc N K, if ¬E n then (1/(N : ℝ)) else 0 := by
          apply sum_congr rfl
          intro n _
          by_cases h : E n <;> simp [h]
        _ = _ := by
          rw [← sum_filter]
          simp only [sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]

/-- Cutting out a set of small ordinary density preserves the bounded
frequency estimate, with an explicit squared counting error. -/
theorem angularMellin_restriction_low_energy (E : ℕ → Prop) (f b : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {N K : ℕ} (hN : 0 < N) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N K)
      (fun n => (if E n then f n else 0)-b n) t‖^2) ≤
      2*(∫ t in -T..T, ‖angularMellinPolynomial (Ioc N K) (fun n => f n-b n) t‖^2) +
      4*T*((((Ioc N K).filter fun n => ¬E n).card : ℝ)/N)^2 := by
  let δ : ℝ := (((Ioc N K).filter fun n => ¬E n).card : ℝ)/N
  have hd : 0 ≤ δ := by dsimp [δ]; positivity
  have hpoint (t : ℝ) :
      ‖angularMellinPolynomial (Ioc N K) (fun n => (if E n then f n else 0)-b n) t‖^2 ≤
        2*‖angularMellinPolynomial (Ioc N K) (fun n => f n-b n) t‖^2 + 2*δ^2 := by
    have hb := angularMellin_restriction_difference E f hf (K := K) hN t
    change _ ≤ δ at hb
    have he : angularMellinPolynomial (Ioc N K) (fun n => (if E n then f n else 0)-b n) t =
        (angularMellinPolynomial (Ioc N K) (fun n => if E n then f n else 0) t -
          angularMellinPolynomial (Ioc N K) f t) +
        angularMellinPolynomial (Ioc N K) (fun n => f n-b n) t := by
      simp only [angularMellinPolynomial_sub]
      ring
    rw [he]
    have hh := norm_add_le
      (angularMellinPolynomial (Ioc N K) (fun n => if E n then f n else 0) t -
        angularMellinPolynomial (Ioc N K) f t)
      (angularMellinPolynomial (Ioc N K) (fun n => f n-b n) t)
    have h1 := norm_nonneg (angularMellinPolynomial (Ioc N K) (fun n => if E n then f n else 0) t -
        angularMellinPolynomial (Ioc N K) f t)
    have h2 := norm_nonneg (angularMellinPolynomial (Ioc N K) (fun n => f n-b n) t)
    have h3 := norm_nonneg ((angularMellinPolynomial (Ioc N K) (fun n => if E n then f n else 0) t -
        angularMellinPolynomial (Ioc N K) f t) +
        angularMellinPolynomial (Ioc N K) (fun n => f n-b n) t)
    nlinarith [sq_nonneg (δ-‖angularMellinPolynomial (Ioc N K) (fun n => f n-b n) t‖)]
  have hi (a : ℕ → ℂ) : IntervalIntegrable
      (fun t => ‖angularMellinPolynomial (Ioc N K) a t‖^2) volume (-T) T :=
    ((angularMellinPolynomial_continuous _ _).norm.pow 2).intervalIntegrable _ _
  have hh := intervalIntegral.integral_mono (by linarith : -T ≤ T) (hi _)
    (((hi _).const_mul 2).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add ((hi _).const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hh
  simp only [smul_eq_mul] at hh
  change _ ≤ 2*(∫ t in -T..T, ‖angularMellinPolynomial (Ioc N K) (fun n => f n-b n) t‖^2) + 4*T*δ^2
  linarith

end JointDickman

end OAI
