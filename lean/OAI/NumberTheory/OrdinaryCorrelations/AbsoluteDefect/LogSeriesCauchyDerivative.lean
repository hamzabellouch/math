import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CompactUnweightedDerivativeSmall
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CutoffSeriesEqSum

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

namespace OrdinaryCorrelations.PretentiousEuler
open MeasureTheory Set OrdinaryRieszPerron OrdinaryHorizontalHalasz Completion

lemma logSeries_cauchy_derivative {f : ℕ → ℂ} (hf : OneBounded f)
    {δ : ℝ} (hδ : 0<δ) :
    (∫t : ℝ, (1+t^2)⁻¹*‖LSeries (LSeries.logMul (complete f)) (vertical (1+δ) t)‖) =
      (∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries (complete f)) (line δ t)‖) := by
  have hab : LSeries.abscissaOfAbsConv (complete f)≤(1:ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => complete_oneBounded hf n⟩
  have he (t : ℝ) : ‖LSeries (LSeries.logMul (complete f)) (vertical (1+δ) t)‖=
      ‖deriv (LSeries (complete f)) (line δ (-t))‖ := by
    have hl : line δ (-t)=vertical (1+δ) t := by unfold line vertical; push_cast; ring
    rw [hl,LSeries_deriv (lt_of_le_of_lt hab (by exact_mod_cast (show 1<(vertical (1+δ) t).re by rw [vertical_re]; linarith))),norm_neg]
  simp only [he]
  have hi := integral_neg_eq_self (fun t : ℝ => (1+t^2)⁻¹*‖deriv (LSeries (complete f)) (line δ t)‖) volume
  simpa only [neg_sq] using hi

lemma rpow_one_add_inv_log {X : ℝ} (hX : 1<X) :
    X^(1+(Real.log X)⁻¹)=X*Real.exp 1 := by
  have hx : 0<X := lt_trans zero_lt_one hX
  have hl : Real.log X≠0 := (Real.log_pos hX).ne'
  rw [Real.rpow_def_of_pos hx,mul_add,mul_one,mul_inv_cancel₀ hl,Real.exp_add,Real.exp_log hx]

theorem logcutoff_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (ε : ℝ) (hε : 0<ε) :
    ∃M : ℝ, 1<M ∧ ∀X : ℝ, M≤X →
      ‖cutoffSeries (LSeries.logMul (complete f)) X‖ ≤ ε*X*Real.log X := by
  let c : ℝ := 1/(2*Real.pi)*Real.exp 1
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨η,hη,hsmall⟩ := global_derivative_small hf hNP (ε/c) (div_pos hε hc)
  let R : ℝ := max 1 η⁻¹
  let M : ℝ := Real.exp R
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM : 1<M := by dsimp [M]; exact Real.one_lt_exp_iff.mpr hR
  refine ⟨M,hM,?_⟩
  intro X hMX
  have hX : 1<X := lt_of_lt_of_le hM hMX
  have hx : 0<X := lt_trans zero_lt_one hX
  have hl : 0<Real.log X := Real.log_pos hX
  have hRlog : R≤Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos R) hMX
    simpa only [M,Real.log_exp] using hh
  have hηlog : η⁻¹≤Real.log X := le_trans (le_max_right _ _) hRlog
  let δ : ℝ := (Real.log X)⁻¹
  have hδ : 0<δ := inv_pos.mpr hl
  have hδη : δ≤η := by
    have hh := (inv_le_inv₀ hl (inv_pos.mpr hη)).mpr hηlog
    simpa only [inv_inv] using hh
  have hab : LSeries.abscissaOfAbsConv (LSeries.logMul (complete f))<(1+δ:ℝ) := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => complete_oneBounded hf n⟩)
      (by exact_mod_cast (show (1:ℝ)<1+δ by linarith))
  have hh := cutoffSeries_norm_le (LSeries.logMul (complete f)) hx (show 1≤1+δ by linarith) hab
  rw [logSeries_cauchy_derivative hf hδ] at hh
  have hr : X^(1+δ)=X*Real.exp 1 := rpow_one_add_inv_log hX
  rw [hr] at hh
  have hs := hsmall δ hδ hδη
  have hsi : (∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries (complete f)) (line δ t)‖) ≤ (ε/c)*Real.log X := by
    have hh' := mul_le_mul_of_nonneg_right hs hl.le
    have hid : δ*(Real.log X)=1 := inv_mul_cancel₀ hl.ne'
    rw [mul_right_comm δ, hid, one_mul] at hh'
    exact hh'
  calc
    ‖cutoffSeries (LSeries.logMul (complete f)) X‖ ≤
        (1/(2*Real.pi))*(X*Real.exp 1)*(∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries (complete f)) (line δ t)‖) := hh
    _ ≤ (1/(2*Real.pi))*(X*Real.exp 1)*((ε/c)*Real.log X) :=
      mul_le_mul_of_nonneg_left hsi (by positivity)
    _ = ε*X*Real.log X := by
      dsimp [c]
      field_simp

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
