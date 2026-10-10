import Mathlib.Analysis.MeanInequalitiesPow
import OAI.NumberTheory.Ostmann.Construction.WeightedRepeatRemoval

namespace OAI

/-! # Jensen amplification of the actual translated-character biases -/

namespace Ostmann

open scoped BigOperators Classical

theorem ternaryMean_sum_lower {ι A : Type*} [Fintype A]
    (S : Finset ι) (y : ι → A → ℝ) (c : ℝ) (hA : 0 < Fintype.card A)
    (hy : ∀ a, (S.card : ℝ) * c ≤ ∑ i ∈ S, y i a) :
    (S.card : ℝ) * c ≤ ∑ i ∈ S, ternaryMean (y i) := by
  have hJ : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hy a)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm] at hs
  simp only [ternaryMean, ← Finset.sum_div]
  apply (le_div_iff₀ hJ).mpr
  nlinarith only [hs]

theorem finite_even_moment_lower {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (heven : Even k)
    (hbias : (S.card : ℝ) * c ≤ ∑ i ∈ S, f i) :
    (S.card : ℝ) * c ^ k ≤ ∑ i ∈ S, f i ^ k := by
  by_cases hS : S.Nonempty
  · have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hw : (∑ _i ∈ S, (S.card : ℝ)⁻¹) = 1 := by simp [hcard.ne']
    have hmean : c ≤ (S.card : ℝ)⁻¹ * ∑ i ∈ S, f i := by
      rw [← div_eq_inv_mul, le_div_iff₀ hcard]
      nlinarith only [hbias]
    have hj := Real.pow_arith_mean_le_arith_mean_pow_of_even S
      (fun _ => (S.card : ℝ)⁻¹) f (fun _ _ => inv_nonneg.mpr hcard.le) hw heven
    simp only [← Finset.mul_sum] at hj
    have hp := (pow_le_pow_left₀ hc hmean k).trans hj
    rw [← div_eq_inv_mul, le_div_iff₀ hcard] at hp
    nlinarith only [hp]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

/-- Positive weight on a finite endpoint tail amplifies its simultaneous
individual prime biases. The moment on the right is an actual infinite sum. -/
theorem weighted_finite_bias_moment {ι A : Type*} [Fintype A]
    (S : Finset ι) (w : ι → ℝ) (y : ι → A → ℝ) (c w₀ : ℝ)
    (k : ℕ) (heven : Even k) (hA : 0 < Fintype.card A)
    (hc : 0 ≤ c) (hw₀ : 0 ≤ w₀) (hw : ∀ i, 0 ≤ w i)
    (hwS : ∀ i ∈ S, w₀ ≤ w i) (hws : Summable w)
    (hy : ∀ i a, y i a = 0 ∨ y i a = 1 ∨ y i a = -1)
    (hbias : ∀ a, (S.card : ℝ) * c ≤ ∑ i ∈ S, y i a) :
    w₀ * S.card * c ^ k ≤ ∑' i, w i * ternaryMean (y i) ^ k := by
  have he (i : ι) : 0 ≤ ternaryMean (y i) ^ k := heven.pow_nonneg _
  have hfs : Summable (fun i => w i * ternaryMean (y i) ^ k) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hw i) (he i)) _ hws
    intro i
    have hpow : ternaryMean (y i) ^ k ≤ 1 := by
      rw [← heven.pow_abs]
      exact pow_le_one₀ (abs_nonneg _) (ternaryMean_abs_le_one (y i) (hy i))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (hw i)
  have hm := finite_even_moment_lower S (fun i => ternaryMean (y i)) c hc k heven
    (ternaryMean_sum_lower S y c hA hbias)
  calc
    w₀ * S.card * c ^ k = w₀ * ((S.card : ℝ) * c ^ k) := by ring
    _ ≤ w₀ * ∑ i ∈ S, ternaryMean (y i) ^ k := mul_le_mul_of_nonneg_left hm hw₀
    _ = ∑ i ∈ S, w₀ * ternaryMean (y i) ^ k := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ S, w i * ternaryMean (y i) ^ k :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hwS i hi) (he i))
    _ ≤ _ := hfs.sum_le_tsum S (fun i _ => mul_nonneg (hw i) (he i))

end Ostmann

end OAI
