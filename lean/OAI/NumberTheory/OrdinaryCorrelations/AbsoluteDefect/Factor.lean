import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter

namespace OrdinaryCorrelations.PretentiousEuler
open Finset

def factor (r : ℝ) (z : ℂ) : ℂ := (1-(r:ℂ)) * (1-(r:ℂ)*z)⁻¹

lemma factor_norm_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1/2) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖factor r z‖ ≤ Real.exp (-(r*(1-z.re)) + r^2) := by
  let w : ℂ := (r:ℂ)*z
  have hw : ‖w‖ ≤ r := by
    dsimp [w]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    nlinarith
  have hw1 : ‖w‖ < 1 := by linarith
  have hneq : 1-w ≠ 0 := by
    intro h
    have he : w = 1 := (sub_eq_zero.mp h).symm
    have : ‖w‖ = 1 := by rw [he,norm_one]
    linarith
  have herr : ‖Complex.log (1-w)⁻¹-w‖ ≤ r^2 := by
    refine (Complex.norm_log_one_sub_inv_sub_self_le hw1).trans ?_
    have hd : 0 < 2*(1-‖w‖) := by linarith
    calc
      ‖w‖^2 * (1-‖w‖)⁻¹ / 2 = ‖w‖^2 / (2*(1-‖w‖)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ ≤ r^2 := by
        apply (div_le_iff₀ hd).mpr
        have hsq : ‖w‖^2 ≤ r^2 := by nlinarith [norm_nonneg w]
        have hden : 1 ≤ 2*(1-‖w‖) := by linarith
        nlinarith [sq_nonneg r,mul_le_mul_of_nonneg_left hden (sq_nonneg r)]
  have hre : (Complex.log (1-w)⁻¹).re ≤ r*z.re+r^2 := by
    have hh := (Complex.re_le_norm (Complex.log (1-w)⁻¹-w)).trans herr
    simpa [w,Complex.sub_re,Complex.mul_re,add_comm] using hh
  have hinv : ‖(1-w)⁻¹‖ ≤ Real.exp (r*z.re+r^2) := by
    calc
      _ = ‖Complex.exp (Complex.log (1-w)⁻¹)‖ := by rw [Complex.exp_log (inv_ne_zero hneq)]
      _ = Real.exp (Complex.log (1-w)⁻¹).re := Complex.norm_exp _
      _ ≤ _ := Real.exp_le_exp.mpr hre
  have hnorm : ‖1-(r:ℂ)‖ = 1-r := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1-r)]
  calc
    ‖factor r z‖ = (1-r)*‖(1-w)⁻¹‖ := by rw [factor,norm_mul,hnorm]
    _ ≤ Real.exp (-r) * Real.exp (r*z.re+r^2) := by
      apply mul_le_mul
      · simpa only [neg_add_eq_sub,add_comm] using Real.add_one_le_exp (-r)
      · exact hinv
      · exact norm_nonneg _
      · exact (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

lemma product_norm_le {ι : Type*} (s : Finset ι) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i ∈ s, 0 ≤ r i) (hr1 : ∀ i ∈ s, r i ≤ 1/2)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) :
    ‖∏ i ∈ s, factor (r i) (z i)‖ ≤
      Real.exp (-(∑ i ∈ s, r i*(1-(z i).re)) + ∑ i ∈ s, (r i)^2) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i ∈ s, Real.exp (-(r i*(1-(z i).re))+(r i)^2) := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact norm_nonneg _
      · intro i hi; exact factor_norm_le (hr i hi) (hr1 i hi) (hz i hi)
    _ = _ := by rw [←Real.exp_sum]; congr 1; simp [sum_add_distrib]

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
