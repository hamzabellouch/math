import OAI.NumberTheory.Ostmann.Dirichlet.TailBase

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open MeasureTheory Set
open scoped Topology

namespace Ostmann.Dirichlet

lemma dirichletPolynomial_eq_sum_div {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) :
    dirichletPolynomial χ N s =
      ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) / (n : ℂ) ^ s := by
  simp only [dirichletPolynomial, Complex.cpow_neg, div_eq_mul_inv]

lemma LFunction_sub_dirichletPolynomial_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    χ.LFunction s - dirichletPolynomial χ N s =
      s * (∫ t : ℝ in Ioi (N : ℝ), partialSumKernel χ s t) -
        (N : ℂ) ^ (-s) * characterPartialSum χ N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hint := integrableOn_partialSumKernel χ hχ hs zero_lt_one
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint
    (hint.mono_set (Ioi_subset_Ioi hNR))
  rw [intervalIntegral.integral_of_le hNR] at hsplit
  have hL : χ.LFunction s = s * ∫ t : ℝ in Ioi 1, partialSumKernel χ s t :=
    LFunction_eq_partial_sum_integral_of_re_pos χ hχ hs
  rw [hL, dirichletPolynomial_eq_integral χ hχ hs N, ← hsplit]
  ring

lemma norm_tail_integral_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    {a : ℝ} (ha : 0 < a) :
    ‖∫ t : ℝ in Ioi a, partialSumKernel χ s t‖ ≤
      q * a ^ (-s.re) / s.re := by
  have hbound : ‖∫ t : ℝ in Ioi a, partialSumKernel χ s t‖ ≤
      ∫ t : ℝ in Ioi a, (q : ℝ) * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le
      ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha).const_mul (q : ℝ))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_partialSumKernel_le χ hχ s (ha.trans ht)
  calc
    _ ≤ ∫ t : ℝ in Ioi a, (q : ℝ) * t ^ (-s.re - 1) := hbound
    _ = q * a ^ (-s.re) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) ha]
      rw [show -s.re - 1 + 1 = -s.re by ring]
      ring

theorem norm_LFunction_sub_dirichletPolynomial_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖χ.LFunction s - dirichletPolynomial χ N s‖ ≤
      q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  have hA : ‖characterPartialSum χ N‖ ≤ q := by
    simpa only [characterPartialSum, Nat.floor_natCast] using
      (norm_sum_character_Icc_lt χ hχ N).le
  have hpow : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
    simpa only [Complex.ofReal_natCast, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos hNp (-s)
  rw [LFunction_sub_dirichletPolynomial_eq χ hχ hs hN]
  calc
    _ ≤ ‖s * ∫ t : ℝ in Ioi (N : ℝ), partialSumKernel χ s t‖ +
        ‖(N : ℂ) ^ (-s) * characterPartialSum χ N‖ := norm_sub_le _ _
    _ = ‖s‖ * ‖∫ t : ℝ in Ioi (N : ℝ), partialSumKernel χ s t‖ +
        (N : ℝ) ^ (-s.re) * ‖characterPartialSum χ N‖ := by
      rw [norm_mul, norm_mul, hpow]
    _ ≤ ‖s‖ * ((q : ℝ) * (N : ℝ) ^ (-s.re) / s.re) +
        (N : ℝ) ^ (-s.re) * q := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (norm_tail_integral_le χ hχ hs hNp) (norm_nonneg s)
      · exact mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hNp.le _)
    _ = _ := by ring

end Ostmann.Dirichlet

end OAI
