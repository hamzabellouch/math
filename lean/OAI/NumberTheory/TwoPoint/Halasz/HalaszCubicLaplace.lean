import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

namespace OAI

/-! The cubic Laplace estimate used to pass from the logarithmic
exponential-sum bound to the Vinogradov--Korobov zeta bound (Ford,
Proc. LMS 85 (2002), Section 7). Absolute constants are deliberately
weakened; only the exponents 3/2 and 2/3 matter for the application. -/
namespace TwoPointCorrelations

open MeasureTheory Set

lemma halasz_cubic_balance {δ x L : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) (hL : 0 < L) :
    δ*x-x^3/(1000*L^2) ≤
      1000*δ^(3/2:ℝ)*L-x^3/(2000*L^2) := by
  have hr : δ^(3/2:ℝ) = δ*Real.sqrt δ := by
    by_cases hz : δ=0
    · simp [hz]
    have hδ0 : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hδ0,Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hd : Real.sqrt δ^2 = δ := Real.sq_sqrt hδ
  have hl2 : 0 < L^2 := sq_pos_of_pos hL
  have hx3 : 0 ≤ x^3 := pow_nonneg hx _
  have he : x^3/(1000*L^2) = 2*(x^3/(2000*L^2)) := by
    field_simp
    ring
  rw [he,hr]
  by_cases hsmall : x ≤ 1000*Real.sqrt δ*L
  · have hh := mul_le_mul_of_nonneg_left hsmall hδ
    have hn : 0 ≤ x^3/(2000*L^2) := by positivity
    nlinarith only [hh,hn]
  · have hbig : 1000*Real.sqrt δ*L ≤ x := (lt_of_not_ge hsmall).le
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ 1000*Real.sqrt δ*L) hbig
    have hs' : 2000*δ*L^2 ≤ x^2 := by
      have hn : 0 ≤ δ*L^2 := by positivity
      nlinarith only [hs,hd,hn]
    have hc : δ*x ≤ x^3/(2000*L^2) := by
      apply (le_div_iff₀ (by positivity : 0 < 2000*L^2)).mpr
      have hh := mul_le_mul_of_nonneg_right hs' hx
      nlinarith only [hh]
    have hn : 0 ≤ 1000*(δ*Real.sqrt δ)*L := by positivity
    linarith only [hc,hn]

lemma halasz_cubic_kernel_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x : ℝ => Real.exp (-x^3/(2000*L^2))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 0) (p := 3) (b := 1/(2000*L^2)) (by norm_num) (by norm_num) (by positivity)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  norm_num only [Real.rpow_zero,one_mul,Real.rpow_ofNat]
  congr 1
  ring

lemma halasz_cubic_kernel_integral {L : ℝ} (hL : 0 < L) :
    (∫ x : ℝ in Ioi 0, Real.exp (-x^3/(2000*L^2))) =
      (2000:ℝ)^(1/3:ℝ)*Real.Gamma (4/3)*L^(2/3:ℝ) := by
  have h := integral_exp_neg_mul_rpow (p := 3) (b := 1/(2000*L^2))
    (by norm_num) (by positivity)
  have he : (1/(2000*L^2):ℝ)^(-1/3:ℝ) = (2000:ℝ)^(1/3:ℝ)*L^(2/3:ℝ) := by
    rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_neg (by positivity)]
    norm_num only [neg_div,neg_neg]
    rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_natCast_mul hL.le]
    norm_num
  rw [he] at h
  norm_num only [one_div,div_self,show (3:ℝ)≠0 by norm_num] at h
  calc
    _ = ∫ x : ℝ in Ioi 0, Real.exp (-(2000*L^2)⁻¹*x^(3:ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      norm_num only [Real.rpow_ofNat]
      congr 1
      ring
    _ = _ := by rw [h]; ring

theorem halasz_cubic_laplace_bound {δ L : ℝ} (hδ : 0 ≤ δ) (hL : 0 < L) :
    (∫ x : ℝ in Ioi 0, Real.exp (δ*x-x^3/(1000*L^2))) ≤
      ((2000:ℝ)^(1/3:ℝ)*Real.Gamma (4/3))*L^(2/3:ℝ)*
        Real.exp (1000*δ^(3/2:ℝ)*L) := by
  let A := Real.exp (1000*δ^(3/2:ℝ)*L)
  have hi := (halasz_cubic_kernel_integrable hL).const_mul A
  have hpoint (x : ℝ) (hx : x ∈ Ioi 0) :
      Real.exp (δ*x-x^3/(1000*L^2)) ≤ A*Real.exp (-x^3/(2000*L^2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simpa only [sub_eq_add_neg,neg_div] using halasz_cubic_balance hδ hx.le hL
  have hf : IntegrableOn (fun x : ℝ => Real.exp (δ*x-x^3/(1000*L^2))) (Ioi 0) := by
    apply hi.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hpoint x hx
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, A*Real.exp (-x^3/(2000*L^2)) :=
      setIntegral_mono_on hf hi measurableSet_Ioi hpoint
    _ = _ := by rw [integral_const_mul,halasz_cubic_kernel_integral hL]; dsimp only [A]; ring

end TwoPointCorrelations

end OAI
