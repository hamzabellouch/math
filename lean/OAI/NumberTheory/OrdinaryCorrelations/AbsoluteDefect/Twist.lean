import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set

namespace OrdinaryArchimedeanTwist

def twist (f : ℕ → ℂ) (u : ℝ) (n : ℕ) : ℂ :=
  f n*Complex.exp (Complex.I*((u*Real.log n:ℝ):ℂ))

lemma norm_twist (f : ℕ → ℂ) (u : ℝ) (n : ℕ) : ‖twist f u n‖=‖f n‖ := by
  simp only [twist, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    sub_self, Real.exp_zero, mul_one]

lemma twist_mul (f : ℕ → ℂ) (u : ℝ)
    (hm : ∀ m n : ℕ, 0 < m → 0 < n → f (m*n)=f m*f n)
    {m n : ℕ} (hm0 : 0 < m) (hn0 : 0 < n) :
    twist f u (m*n)=twist f u m*twist f u n := by
  rw [twist,hm m n hm0 hn0,Nat.cast_mul,Real.log_mul (by positivity : (m:ℝ)≠0) (by positivity : (n:ℝ)≠0)]
  simp only [twist,mul_add,Complex.ofReal_add,Complex.ofReal_mul,Complex.exp_add]
  ring

lemma term_twist (f : ℕ → ℂ) (u : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (twist f u) s n=LSeries.term f (s-(u:ℂ)*Complex.I) n := by
  by_cases hn : n=0
  · simp [hn,LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn,LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_def_of_ne_zero (show (n:ℂ)≠0 by exact_mod_cast hn),
      Complex.cpow_def_of_ne_zero (show (n:ℂ)≠0 by exact_mod_cast hn)]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg n)]
    simp only [twist,div_eq_mul_inv,←Complex.exp_neg,mul_assoc,←Complex.exp_add]
    congr 2
    push_cast
    ring

lemma lseries_twist (f : ℕ → ℂ) (u : ℝ) (s : ℂ) :
    LSeries (twist f u) s=LSeries f (s-(u:ℂ)*Complex.I) :=
  tsum_congr (term_twist f u s)

lemma logMul_twist (f : ℕ → ℂ) (u : ℝ) :
    LSeries.logMul (twist f u)=twist (LSeries.logMul f) u := by
  ext n
  simp only [LSeries.logMul,twist,mul_assoc]

lemma derivative_twist (f : ℕ → ℂ) (hf : ∀n, ‖f n‖≤1)
    (u : ℝ) {s : ℂ} (hs : 1<s.re) :
    deriv (LSeries (twist f u)) s=deriv (LSeries f) (s-(u:ℂ)*Complex.I) := by
  have hh : LSeries.abscissaOfAbsConv f≤(1:ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hf n⟩
  have hht : LSeries.abscissaOfAbsConv (twist f u)≤(1:ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => (norm_twist f u n).le.trans (hf n)⟩
  have hs' : 1<(s-(u:ℂ)*Complex.I).re := by simpa using hs
  rw [LSeries_deriv (lt_of_le_of_lt hht (by exact_mod_cast hs)),
    LSeries_deriv (lt_of_le_of_lt hh (by exact_mod_cast hs')),
    logMul_twist,lseries_twist]

end OrdinaryArchimedeanTwist

end

end OAI
