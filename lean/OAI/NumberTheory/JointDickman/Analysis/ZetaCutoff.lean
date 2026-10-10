import OAI.NumberTheory.JointDickman.Analysis.CharacterLFunctionCutoff

namespace OAI

/-! # A bounded zeta truncation error away from the pole -/
namespace JointDickman
open Complex Finset LargePrimeGaps

lemma regularSeries_constant_eq {s : ℂ} (hs : 1 < s.re) :
    regularSeries (positiveCoefficients (fun _ => 1)) 1 s =
      riemannZeta s - 1 / (s - 1) := by
  rw [regularSeries_eq_LSeries_sub
    (positiveCoefficients_norm_le (by intro n; simp)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun t ht => discrepancy_constant_bound ht.le) hs,
    LSeries_positiveCoefficients]
  change LSeries (1 : ℕ → ℂ) s - 1 / (s - 1) = _
  rw [LSeries_one_eq_riemannZeta hs]

lemma zeta_cutoff_bound {s : ℂ} (hs : 1 < s.re) (hs2 : s.re ≤ 2)
    {N : ℕ} (hN : 1 ≤ N) (htlo : 1 ≤ |s.im|) (hthi : |s.im| ≤ N) :
    ‖riemannZeta s - ∑ n ∈ Icc 1 N, (n : ℂ)^(-s)‖ ≤ 5 := by
  have hs0 : 0 < s.re := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hsne : s - 1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [sub_re, one_re, zero_re] at hr
    linarith
  let A := seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1
  have he := regularSeries_cutoff (positiveCoefficients_zero (fun _ => 1))
    (D := 1) (by norm_num) (fun t ht => discrepancy_constant_bound ht.le) hN hs0
  rw [regularSeries_constant_eq hs] at he
  have hp : (∑ n ∈ Icc 1 N, positiveCoefficients (fun _ => 1) n * (n : ℂ)^(-s)) =
      ∑ n ∈ Icc 1 N, (n : ℂ)^(-s) := by
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    simp [positiveCoefficients, hn0]
  rw [hp, one_mul] at he
  have hi : (1 / (s - 1) : ℂ) - (∫ t in (1 : ℝ)..N, (t : ℂ)^(-s)) =
      (N : ℂ)^(1-s)/(s-1) := by
    have hc := cpow_sub_eq_mul_intervalIntegral hNR s
    simp only [Complex.ofReal_natCast] at hc
    apply (eq_div_iff hsne).mpr
    calc
      _ = 1 + (1-s)*(∫ t in (1 : ℝ)..N, (t : ℂ)^(-s)) := by field_simp; ring
      _ = _ := by rw [←hc]; ring
  have herr : riemannZeta s - ∑ n ∈ Icc 1 N, (n : ℂ)^(-s) =
      -(A N * (N : ℂ)^(-s)) + s * discrepancyTail A N s + (N : ℂ)^(1-s)/(s-1) := by
    dsimp [A]
    rw [←hi]
    linear_combination he
  have hpow : (N : ℝ)^(-s.re) ≤ (N : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hNR
      (show -s.re ≤ -1 by linarith)
  have htail : ‖discrepancyTail A N s‖ ≤ (N : ℝ)⁻¹ := by
    have hh := discrepancyTail_norm_le hN0 (by norm_num : (0 : ℝ) ≤ 1)
      (measurable_seriesDiscrepancy _ (1 : ℂ))
      (fun t (ht : (N : ℝ) < t) => discrepancy_constant_bound (hNR.trans ht.le)) hs0
    apply hh.trans
    simp only [one_mul]
    exact (div_le_self (by positivity) hs.le).trans hpow
  have hc : ‖A N * (N : ℂ)^(-s)‖ ≤ (N : ℝ)⁻¹ := by
    rw [norm_mul, show (N : ℂ) = ((N : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos hN0, neg_re]
    exact (mul_le_of_le_one_left (by positivity) (discrepancy_constant_bound hNR)).trans hpow
  have hnorm : ‖s‖ ≤ 2 + (N : ℝ) := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at hh
    linarith
  have hpole : ‖(N : ℂ)^(1-s)/(s-1)‖ ≤ 1 := by
    rw [norm_div, show (N : ℂ) = ((N : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos hN0]
    apply (div_le_one (norm_pos_iff.mpr hsne)).mpr
    have hnum : (N : ℝ)^((1-s).re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hNR (by simp only [sub_re, one_re]; linarith)
    have him : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s-1)
    linarith
  rw [herr]
  calc
    _ ≤ (‖A N * (N : ℂ)^(-s)‖ + ‖s‖ * ‖discrepancyTail A N s‖) +
        ‖(N : ℂ)^(1-s)/(s-1)‖ := by
      simpa only [norm_neg, norm_mul] using
        (norm_add_le (-(A N * (N : ℂ)^(-s)) + s * discrepancyTail A N s)
          ((N : ℂ)^(1-s)/(s-1))).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (N : ℝ)⁻¹ + (2 + (N : ℝ)) * (N : ℝ)⁻¹ + 1 :=
      add_le_add (add_le_add hc (mul_le_mul hnorm htail (norm_nonneg _) (by positivity))) hpole
    _ ≤ 5 := by
      have hNi : (N : ℝ)*(N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN0.ne'
      have hile : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNR
      nlinarith

end JointDickman

end OAI
