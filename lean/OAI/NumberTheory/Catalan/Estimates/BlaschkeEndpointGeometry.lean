import OAI.NumberTheory.Catalan.Polynomial.BlaschkeDensityPolynomial

namespace OAI

noncomputable section

namespace InternalCatalan

section

open scoped BigOperators

theorem reciprocal_blaschkeFactor_endpoint_norm_le {x : ℝ} (hx : |x| < 1)
    {c w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    ‖(1 - (x : ℂ) * w) / (w - (x : ℂ))‖ ≤ 1 + 3 * ‖w - c‖ := by
  let d := ‖w - c‖
  let a := ‖c - (x : ℂ)‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have ha : 1 ≤ a := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, hci] using
      Complex.abs_im_le_norm (c - (x : ℂ))
  have hcenter : ‖1 - (x : ℂ) * c‖ = a := by
    have hr := blaschkeFactor_norm_eq_one hx hc
    unfold blaschkeFactor at hr
    rw [norm_div] at hr
    have heq := (div_eq_iff (norm_ne_zero_iff.mpr
      (blaschkeFactor_denominator_ne_zero hx hc.le))).mp hr
    simpa only [one_mul] using heq.symm
  have hdenlower : a - d ≤ ‖w - (x : ℂ)‖ := by
    have ht := norm_sub_norm_le (c - (x : ℂ)) (w - (x : ℂ))
    have heq : (c - (x : ℂ)) - (w - (x : ℂ)) = c - w := by ring
    rw [heq, norm_sub_rev c w] at ht
    change a - ‖w - (x : ℂ)‖ ≤ d at ht
    linarith
  have hdenpos : 0 < ‖w - (x : ℂ)‖ := by
    change d ≤ 1 / 4 at hd
    linarith
  have hnum : ‖1 - (x : ℂ) * w‖ ≤ a + d := by
    have heq : 1 - (x : ℂ) * w = (1 - (x : ℂ) * c) - (x : ℂ) * (w - c) := by ring
    rw [heq]
    calc
      _ ≤ ‖1 - (x : ℂ) * c‖ + ‖(x : ℂ) * (w - c)‖ := norm_sub_le _ _
      _ = a + |x| * d := by rw [hcenter, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ a + d := by nlinarith [mul_le_mul_of_nonneg_right hx.le hd0]
  rw [norm_div]
  apply (div_le_iff₀ hdenpos).mpr
  calc
    _ ≤ a + d := hnum
    _ ≤ (1 + 3 * d) * (a - d) := by
      have hprod := mul_nonneg hd0 (sub_nonneg.mpr ha)
      have hquad := mul_nonneg hd0 (sub_nonneg.mpr hd)
      nlinarith
    _ ≤ (1 + 3 * d) * ‖w - (x : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hdenlower (by positivity)

theorem blaschkeDensity_endpoint_norm_le_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (hx : ∀ i ∈ s, |x i| < 1) {c w : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    ‖blaschkeDensity s x D w‖ ≤
      Real.exp (((D : ℝ) + 3 * (s.card : ℝ)) * ‖w - c‖) := by
  let d := ‖w - c‖
  have hwp : ‖w‖ ≤ Real.exp d := by
    calc
      ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by simpa using norm_add_le (w - c) c
      _ = d + 1 := by rw [hc]
      _ ≤ Real.exp d := Real.add_one_le_exp d
  have hpow : ‖w‖ ^ D ≤ (Real.exp d) ^ D :=
    pow_le_pow_left₀ (norm_nonneg _) hwp _
  have hf (i : ι) (hi : i ∈ s) :
      ‖(1 - (x i : ℂ) * w) / (w - (x i : ℂ))‖ ≤ Real.exp (3 * d) :=
    (reciprocal_blaschkeFactor_endpoint_norm_le (hx i hi) hc hci hd).trans
      (by simpa only [add_comm] using Real.add_one_le_exp (3 * d))
  have hp := Finset.prod_le_prod₀ (fun i (_ : i ∈ s) =>
    norm_nonneg ((1 - (x i : ℂ) * w) / (w - (x i : ℂ)))) hf
  rw [blaschkeDensity_eq_product, norm_mul, norm_pow, norm_prod]
  calc
    _ ≤ (Real.exp d) ^ D * ∏ _i ∈ s, Real.exp (3 * d) :=
      mul_le_mul hpow hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = Real.exp (((D : ℝ) + 3 * (s.card : ℝ)) * d) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem blaschkeDensity_endpoint_norm_le_exp_twelve {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1)
    {c w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ 3 / (n : ℝ)) :
    ‖blaschkeDensity s x D w‖ ≤ Real.exp 12 := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hquarter : ‖w - c‖ ≤ (1 / 4 : ℝ) := hd.trans ((div_le_iff₀ hnpos).mpr (by linarith))
  apply (blaschkeDensity_endpoint_norm_le_exp s x D hx hc hci hquarter).trans
  apply Real.exp_le_exp.mpr
  have hDn : (D : ℝ) ≤ n := by exact_mod_cast hD
  have hcn : (s.card : ℝ) ≤ n := by exact_mod_cast hcard
  have hmul := (le_div_iff₀ hnpos).mp hd
  have h1 := mul_le_mul_of_nonneg_right hDn (norm_nonneg (w - c))
  have h2 := mul_le_mul_of_nonneg_right hcn (norm_nonneg (w - c))
  nlinarith

theorem blaschkeDensity_near_imaginary_units_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1) {w : ℂ}
    (hw : ‖w - Complex.I‖ ≤ 3 / (n : ℝ) ∨ ‖w + Complex.I‖ ≤ 3 / (n : ℝ)) :
    ‖blaschkeDensity s x D w‖ ≤ Real.exp 12 := by
  rcases hw with hw | hw
  · exact blaschkeDensity_endpoint_norm_le_exp_twelve s x D n hn hD hcard hx
      (c := Complex.I) (by simp) (by simp) hw
  · exact blaschkeDensity_endpoint_norm_le_exp_twelve s x D n hn hD hcard hx
      (c := -Complex.I) (by simp) (by simp) (by simpa only [sub_neg_eq_add] using hw)

end

theorem norm_ge_three_quarters_near_unit {c w : ℂ} (hc : ‖c‖ = 1)
    (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) : (3 / 4 : ℝ) ≤ ‖w‖ := by
  have ht := norm_sub_norm_le c w
  rw [hc, norm_sub_rev] at ht
  linarith

theorem blaschkeFactor_endpoint_norm_lower {x : ℝ} (hx : |x| < 1) {c w : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    (3 / 4 : ℝ) ≤ ‖w - (x : ℂ)‖ ∧ (3 / 4 : ℝ) ≤ ‖1 - (x : ℂ) * w‖ := by
  have ha : 1 ≤ ‖c - (x : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, hci] using
      Complex.abs_im_le_norm (c - (x : ℂ))
  have hcenter : ‖1 - (x : ℂ) * c‖ = ‖c - (x : ℂ)‖ := by
    have hr := blaschkeFactor_norm_eq_one hx hc
    unfold blaschkeFactor at hr
    rw [norm_div] at hr
    have heq := (div_eq_iff (norm_ne_zero_iff.mpr
      (blaschkeFactor_denominator_ne_zero hx hc.le))).mp hr
    simpa only [one_mul] using heq.symm
  constructor
  · have ht := norm_sub_norm_le (c - (x : ℂ)) (w - (x : ℂ))
    have heq : (c - (x : ℂ)) - (w - (x : ℂ)) = c - w := by ring
    rw [heq, norm_sub_rev c w] at ht
    linarith
  · have ht := norm_sub_norm_le (1 - (x : ℂ) * c) (1 - (x : ℂ) * w)
    have heq : (1 - (x : ℂ) * c) - (1 - (x : ℂ) * w) = (x : ℂ) * (w - c) := by ring
    rw [heq, hcenter, norm_mul, Complex.norm_real, Real.norm_eq_abs] at ht
    have hmul := mul_le_mul_of_nonneg_right hx.le (norm_nonneg (w - c))
    linarith

end InternalCatalan

end

end OAI
