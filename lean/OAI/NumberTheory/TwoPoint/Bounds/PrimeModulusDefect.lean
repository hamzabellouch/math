import OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectCRT
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! The exact modulus-defect series used in the qualitative reduction. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def primeModulusDefect (f : ℕ → ℂ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0

lemma primeModulusDefect_nonneg {f : ℕ → ℂ} (hf : OneBounded f) (p : ℕ) :
    0 ≤ primeModulusDefect f p := by
  unfold primeModulusDefect
  split_ifs with hp
  · exact div_nonneg (sub_nonneg.mpr (hf p hp.pos)) (Nat.cast_nonneg p)
  · exact le_rfl

lemma prime_square_density_lower {p : ℕ} (hp : p.Prime) :
    (1 / (p : ℝ)) / 2 ≤ 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ = ((p : ℝ) / 2) / (p : ℝ) ^ 2 := by field_simp [hp0.ne']
    _ ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by field_simp [hp0.ne']

lemma prime_square_defect_factor_nonneg {f : ℕ → ℂ} (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
  have hi : 1 / (p : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hp.pos)).mpr hp1
  have hc : 0 ≤ 1 - ‖f p‖ := sub_nonneg.mpr (hf p hp.pos)
  have hd : 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 ≤ 1 := by
    have hh : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
    linarith
  have hb := mul_le_mul_of_nonneg_left hd hc
  have hn := norm_nonneg (f p)
  nlinarith

lemma prime_square_defect_factor_le_exp {f : ℕ → ℂ} (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) :
    1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) ≤
      Real.exp (-primeModulusDefect f p / 2) := by
  have hc : 0 ≤ 1 - ‖f p‖ := sub_nonneg.mpr (hf p hp.pos)
  have hd := mul_le_mul_of_nonneg_left (prime_square_density_lower hp) hc
  have hd' : primeModulusDefect f p / 2 ≤
      (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) := by
    simpa only [primeModulusDefect, ite_eq_left hp, div_eq_mul_inv, one_mul,
      mul_assoc] using hd
  have he := Real.add_one_le_exp (-primeModulusDefect f p / 2)
  linarith

lemma prime_square_defect_product_le_exp {f : ℕ → ℂ} (hf : OneBounded f)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2))) ≤
      Real.exp (-(∑ p ∈ P, primeModulusDefect f p) / 2) := by
  calc
    _ ≤ ∏ p ∈ P, Real.exp (-primeModulusDefect f p / 2) :=
      prod_le_prod₀ (fun p hp => prime_square_defect_factor_nonneg hf (hP p hp))
        (fun p hp => prime_square_defect_factor_le_exp hf (hP p hp))
    _ = _ := by rw [← Real.exp_sum, ← sum_div, sum_neg_distrib]

end TwoPointCorrelations

end OAI
