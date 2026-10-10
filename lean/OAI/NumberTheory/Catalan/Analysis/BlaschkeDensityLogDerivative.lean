import Mathlib.Analysis.Calculus.LogDeriv
import OAI.NumberTheory.Catalan.Estimates.BlaschkeEndpointGeometry

namespace OAI

noncomputable section
open scoped BigOperators
namespace InternalCatalan

private theorem reciprocalFactor_hasDerivAt (x : ℝ) {w : ℂ} (hw : w - (x : ℂ) ≠ 0) :
    HasDerivAt (fun v : ℂ => (1 - (x : ℂ) * v) / (v - (x : ℂ)))
      (((x : ℂ) ^ 2 - 1) / (w - (x : ℂ)) ^ 2) w := by
  have hn : HasDerivAt (fun v : ℂ => 1 - (x : ℂ) * v) (-(x : ℂ)) w := by
    convert! HasDerivAt.const_sub 1 ((hasDerivAt_id w).const_mul (x : ℂ)) using 1
    simp only [mul_one]
  have hd : HasDerivAt (fun v : ℂ => v - (x : ℂ)) 1 w := (hasDerivAt_id w).sub_const _
  convert! hn.div hd hw using 1
  ring

private theorem reciprocalFactor_logDeriv (x : ℝ) {w : ℂ}
    (hn : 1 - (x : ℂ) * w ≠ 0) (hd : w - (x : ℂ) ≠ 0) :
    logDeriv (fun v : ℂ => (1 - (x : ℂ) * v) / (v - (x : ℂ))) w =
      -(x : ℂ) / (1 - (x : ℂ) * w) - 1 / (w - (x : ℂ)) := by
  rw [logDeriv_apply, (reciprocalFactor_hasDerivAt x hd).deriv]
  field_simp [hn, hd]
  ring

theorem blaschkeDensity_logDeriv {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D : ℕ)
    {w : ℂ} (hw : w ≠ 0)
    (hnum : ∀ i ∈ s, 1 - (x i : ℂ) * w ≠ 0)
    (hden : ∀ i ∈ s, w - (x i : ℂ) ≠ 0) :
    logDeriv (blaschkeDensity s x D) w = (D : ℂ) / w +
      ∑ i ∈ s, (-(x i : ℂ) / (1 - (x i : ℂ) * w) - 1 / (w - (x i : ℂ))) := by
  classical
  let f : ι → ℂ → ℂ := fun i v => (1 - (x i : ℂ) * v) / (v - (x i : ℂ))
  have hfn : ∀ i ∈ s, f i w ≠ 0 := fun i hi => div_ne_zero (hnum i hi) (hden i hi)
  have hfd : ∀ i ∈ s, DifferentiableAt ℂ (f i) w :=
    fun i hi => (reciprocalFactor_hasDerivAt (x i) (hden i hi)).differentiableAt
  have hpn : (∏ i ∈ s, f i w) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfn
  have hpd : DifferentiableAt ℂ (fun v => ∏ i ∈ s, f i v) w :=
    DifferentiableAt.fun_finsetProd hfd
  have hfun : blaschkeDensity s x D = fun v => v ^ D * ∏ i ∈ s, f i v :=
    funext (blaschkeDensity_eq_product s x D)
  have hmul : logDeriv (fun v : ℂ => v ^ D * ∏ i ∈ s, f i v) w =
      logDeriv (fun v : ℂ => v ^ D) w + logDeriv (fun v : ℂ => ∏ i ∈ s, f i v) w := by
    convert! logDeriv_fun_mul (f := fun v : ℂ => v ^ D)
      (g := fun v : ℂ => ∏ i ∈ s, f i v) w (pow_ne_zero D hw) hpn
      (differentiableAt_id.pow D) hpd using 1
  have hpow : logDeriv (fun v : ℂ => v ^ D) w = (D : ℂ) / w := by
    convert! logDeriv_pow w D using 1
  have hprod : logDeriv (fun v : ℂ => ∏ i ∈ s, f i v) w =
      ∑ i ∈ s, logDeriv (f i) w := by
    convert! logDeriv_fun_prod hfn hfd using 1
  rw [hfun, hmul, hpow, hprod]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact reciprocalFactor_logDeriv (x i) (hnum i hi) (hden i hi)

theorem blaschkeDensity_endpoint_ne_zero {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (hx : ∀ i ∈ s, |x i| < 1) {c w : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    blaschkeDensity s x D w ≠ 0 := by
  have hw : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num)
    (norm_ge_three_quarters_near_unit hc hd))
  rw [blaschkeDensity_eq_product]
  apply mul_ne_zero (pow_ne_zero D hw)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hh := blaschkeFactor_endpoint_norm_lower (hx i hi) hc hci hd
  exact div_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hh.2))
    (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hh.1))

theorem blaschkeDensity_endpoint_logDeriv_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hD : D ≤ n) (hcard : s.card ≤ n)
    (hx : ∀ i ∈ s, |x i| < 1) {c w : ℂ}
    (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
    ‖logDeriv (blaschkeDensity s x D) w‖ ≤ 4 * (n : ℝ) := by
  have hlow := norm_ge_three_quarters_near_unit hc hd
  have hwp : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hlow
  have hw : w ≠ 0 := norm_pos_iff.mp hwp
  have hlowi (i : ι) (hi : i ∈ s) := blaschkeFactor_endpoint_norm_lower (hx i hi) hc hci hd
  have hnum : ∀ i ∈ s, 1 - (x i : ℂ) * w ≠ 0 := fun i hi =>
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hlowi i hi).2)
  have hden : ∀ i ∈ s, w - (x i : ℂ) ≠ 0 := fun i hi =>
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) (hlowi i hi).1)
  have hp : ‖(D : ℂ) / w‖ ≤ (4 / 3 : ℝ) * (D : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    apply (div_le_iff₀ hwp).mpr
    have hm := mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg D)
    nlinarith
  have hf (i : ι) (hi : i ∈ s) :
      ‖-(x i : ℂ) / (1 - (x i : ℂ) * w) - 1 / (w - (x i : ℂ))‖ ≤ (8 / 3 : ℝ) := by
    have hnpos : 0 < ‖1 - (x i : ℂ) * w‖ := norm_pos_iff.mpr (hnum i hi)
    have hdpos : 0 < ‖w - (x i : ℂ)‖ := norm_pos_iff.mpr (hden i hi)
    have hn1 : |x i| / ‖1 - (x i : ℂ) * w‖ ≤ (4 / 3 : ℝ) := by
      apply (div_le_iff₀ hnpos).mpr
      nlinarith [(hlowi i hi).2, hx i hi]
    have hd1 : (1 : ℝ) / ‖w - (x i : ℂ)‖ ≤ (4 / 3 : ℝ) := by
      apply (div_le_iff₀ hdpos).mpr
      nlinarith [(hlowi i hi).1]
    calc
      _ ≤ ‖-(x i : ℂ) / (1 - (x i : ℂ) * w)‖ + ‖1 / (w - (x i : ℂ))‖ := norm_sub_le _ _
      _ ≤ (8 / 3 : ℝ) := by
        rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_one]
        linarith
  rw [blaschkeDensity_logDeriv s x D hw hnum hden]
  calc
    _ ≤ ‖(D : ℂ) / w‖ + ‖∑ i ∈ s,
        (-(x i : ℂ) / (1 - (x i : ℂ) * w) - 1 / (w - (x i : ℂ)))‖ := norm_add_le _ _
    _ ≤ (4 / 3 : ℝ) * (D : ℝ) + ∑ _i ∈ s, (8 / 3 : ℝ) :=
      add_le_add hp ((norm_sum_le _ _).trans (Finset.sum_le_sum hf))
    _ ≤ 4 * (n : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hDn : (D : ℝ) ≤ n := by exact_mod_cast hD
      have hcn : (s.card : ℝ) ≤ n := by exact_mod_cast hcard
      linarith

theorem blaschkeDensity_endpoint_deriv_norm_le {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (D n : ℕ) (hn : 48 ≤ n)
    (hD : D ≤ n) (hcard : s.card ≤ n) (hx : ∀ i ∈ s, |x i| < 1)
    {c w : ℂ} (hc : ‖c‖ = 1) (hci : |c.im| = 1) (hd : ‖w - c‖ ≤ 3 / (n : ℝ)) :
    ‖deriv (blaschkeDensity s x D) w‖ ≤ 4 * (n : ℝ) * Real.exp 12 := by
  have hnR : (48 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hquarter : ‖w - c‖ ≤ (1 / 4 : ℝ) := hd.trans ((div_le_iff₀ hnpos).mpr (by linarith))
  have hF := blaschkeDensity_endpoint_ne_zero s x D hx hc hci hquarter
  have heq : deriv (blaschkeDensity s x D) w =
      logDeriv (blaschkeDensity s x D) w * blaschkeDensity s x D w := by
    rw [logDeriv_apply, div_mul_cancel₀ _ hF]
  rw [heq, norm_mul]
  exact mul_le_mul (blaschkeDensity_endpoint_logDeriv_norm_le s x D n hD hcard hx hc hci hquarter)
    (blaschkeDensity_endpoint_norm_le_exp_twelve s x D n hn hD hcard hx hc hci hd)
    (norm_nonneg _) (by positivity)

end InternalCatalan

end

end OAI
