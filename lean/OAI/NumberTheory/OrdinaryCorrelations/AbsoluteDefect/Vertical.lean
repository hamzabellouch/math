import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Riesz

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
open Set MeasureTheory Complex

namespace OrdinaryRieszPerron
open MeasureTheory Set Complex

def vertical (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I

def cutoffSeries (a : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑'n : ℕ, if n=0 then 0 else a n*riesz ((n:ℝ)/X)

def perronConstant : ℂ := ((1/(2*Real.pi):ℝ):ℂ)

lemma vertical_re (σ t : ℝ) : (vertical σ t).re=σ := by simp [vertical]

lemma term_norm_vertical (a : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term a (vertical σ t) n‖=‖LSeries.term a (σ:ℂ) n‖ := by
  simp only [LSeries.norm_term_eq,vertical_re,Complex.ofReal_re]

lemma continuous_vertical_kernel {σ : ℝ} (hσ : 1≤σ) :
    Continuous (fun t : ℝ => kernel (vertical σ t)) := by
  unfold kernel vertical
  apply Continuous.div continuous_const
  · fun_prop
  · intro t
    apply mul_ne_zero
    · intro h
      have hh := congrArg Complex.re h
      simp at hh
      linarith
    · intro h
      have hh := congrArg Complex.re h
      simp at hh
      linarith

lemma continuous_vertical_term (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a (vertical σ t) n) := by
  by_cases hn : n=0
  · simp only [hn,LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    apply continuous_const.div
    · apply Continuous.const_cpow
      · unfold vertical
        fun_prop
      · exact Or.inl (by exact_mod_cast hn)
    · exact fun t => Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))

lemma scaled_term (a : ℕ → ℂ) {X : ℝ} (hX : 0<X) (s : ℂ) {n : ℕ} (hn : n≠0) :
    (X:ℂ)^s*LSeries.term a s n = a n*((n:ℝ)/X:ℝ)^(-s) := by
  rw [LSeries.term_of_ne_zero hn,Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg n) hX.le,
    Complex.cpow_neg,Complex.cpow_neg]
  push_cast
  simp only [div_eq_mul_inv,inv_inv]
  ring

lemma norm_scaled_integrand (a : ℕ → ℂ) {X : ℝ} (hX : 0<X) (σ t : ℝ) (n : ℕ) :
    ‖(X:ℂ)^(vertical σ t)*LSeries.term a (vertical σ t) n*kernel (vertical σ t)‖ =
      (X^σ*‖LSeries.term a (σ:ℂ) n‖)*‖kernel (vertical σ t)‖ := by
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,vertical_re,term_norm_vertical]

lemma integrable_scaled_term (a : ℕ → ℂ) {X σ : ℝ} (hX : 0<X) (hσ : 1≤σ) (n : ℕ) :
    Integrable (fun t : ℝ => (X:ℂ)^(vertical σ t)*LSeries.term a (vertical σ t) n*kernel (vertical σ t)) := by
  apply Integrable.mono' (((integrable_kernel hσ).norm).const_mul (X^σ*‖LSeries.term a (σ:ℂ) n‖))
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul _ (continuous_vertical_kernel hσ)
    apply Continuous.mul _ (continuous_vertical_term a σ n)
    apply Continuous.const_cpow
    · unfold vertical
      fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr hX.ne')
  · exact Filter.Eventually.of_forall (fun t => (norm_scaled_integrand a hX σ t n).le)

lemma perron_term (a : ℕ → ℂ) {X σ : ℝ} (hX : 0<X) (hσ : 1≤σ) (n : ℕ) :
    perronConstant*(∫t : ℝ, (X:ℂ)^(vertical σ t)*LSeries.term a (vertical σ t) n*kernel (vertical σ t)) =
      if n=0 then 0 else a n*riesz ((n:ℝ)/X) := by
  by_cases hn : n=0
  · simp [hn,LSeries.term_zero]
  · rw [ite_eq_right hn]
    have hx : 0<(n:ℝ)/X := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hX
    have hk := kernel_inverse hσ hx
    change perronConstant*(∫t : ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-(vertical σ t))*kernel (vertical σ t)) =
      riesz ((n:ℝ)/X) at hk
    simp_rw [scaled_term a hX _ hn,mul_assoc,MeasureTheory.integral_const_mul]
    calc
      perronConstant*(a n*(∫t : ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-(vertical σ t))*kernel (vertical σ t))) =
        a n*(perronConstant*(∫t : ℝ, (((n:ℝ)/X:ℝ):ℂ)^(-(vertical σ t))*kernel (vertical σ t))) := by ring
      _ = _ := by rw [hk]

theorem cutoffSeries_perron (a : ℕ → ℂ) {X σ : ℝ} (hX : 0<X) (hσ : 1≤σ)
    (ha : LSeriesSummable a (σ:ℂ)) :
    cutoffSeries a X = perronConstant*(∫t : ℝ,
      (X:ℂ)^(vertical σ t)*LSeries a (vertical σ t)*kernel (vertical σ t)) := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    (X:ℂ)^(vertical σ t)*LSeries.term a (vertical σ t) n*kernel (vertical σ t)
  have hi (n : ℕ) : Integrable (F n) := integrable_scaled_term a hX hσ n
  have hs : Summable (fun n => ∫t : ℝ, ‖F n t‖) := by
    have he (n : ℕ) : (∫t : ℝ, ‖F n t‖)=
        (X^σ*(∫t : ℝ, ‖kernel (vertical σ t)‖))*‖LSeries.term a (σ:ℂ) n‖ := by
      simp only [F,norm_scaled_integrand a hX,MeasureTheory.integral_const_mul]
      ring
    simpa only [he] using ha.norm.mul_left (X^σ*(∫t : ℝ, ‖kernel (vertical σ t)‖))
  have he (t : ℝ) : (∑'n, F n t) = (X:ℂ)^(vertical σ t)*LSeries a (vertical σ t)*kernel (vertical σ t) := by
    simp only [F,tsum_mul_right,tsum_mul_left,LSeries]
  calc
    cutoffSeries a X = ∑'n, perronConstant*(∫t : ℝ, F n t) := by
      exact tsum_congr (fun n => (perron_term a hX hσ n).symm)
    _ = perronConstant*(∑'n, ∫t : ℝ, F n t) := tsum_mul_left
    _ = perronConstant*(∫t : ℝ, ∑'n, F n t) := by rw [integral_tsum_of_summable_integral_norm hi hs]
    _ = _ := by simp only [he]

end OrdinaryRieszPerron

end

end OAI
