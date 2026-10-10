import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogSeriesCauchyDerivative
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RieszCoeffNorm
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MovingCompactUnweightedSmall

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
open Set

namespace OrdinaryCorrelations.PretentiousEuler
open MeasureTheory Set Completion OrdinaryRieszPerron OrdinaryHorizontalHalasz

lemma bounded_logSeries_cauchy_derivative {g : ℕ → ℂ} (hg : ∀n, ‖g n‖≤1)
    {δ : ℝ} (hδ : 0<δ) :
    (∫t : ℝ, (1+t^2)⁻¹*‖LSeries (LSeries.logMul g) (vertical (1+δ) t)‖) =
      (∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries g) (line δ t)‖) := by
  have hab : LSeries.abscissaOfAbsConv g≤(1:ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hg n⟩
  have he (t : ℝ) : ‖LSeries (LSeries.logMul g) (vertical (1+δ) t)‖=
      ‖deriv (LSeries g) (line δ (-t))‖ := by
    have hl : line δ (-t)=vertical (1+δ) t := by unfold line vertical; push_cast; ring
    rw [hl,LSeries_deriv (lt_of_le_of_lt hab (by exact_mod_cast (show 1<(vertical (1+δ) t).re by rw [vertical_re]; linarith))),norm_neg]
  simp only [he]
  have hi := integral_neg_eq_self (fun t : ℝ => (1+t^2)⁻¹*‖deriv (LSeries g) (line δ t)‖) volume
  simpa only [neg_sq] using hi

theorem moving_logcutoff_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀τ : ℝ, |τ|≤(N:ℝ)/2 →
      ‖cutoffSeries (LSeries.logMul (OrdinaryArchimedeanTwist.twist (complete f) τ)) (N:ℝ)‖
        ≤ε*(N:ℝ)*Real.log N := by
  let c : ℝ := 1/(2*Real.pi)*Real.exp 1
  have hc : 0<c := by dsimp [c]; positivity
  filter_upwards [moving_global_derivative_small hf hNP (ε/c) (div_pos hε hc),
    eventually_ge_atTop (2:ℕ)] with N hsmall hN
  intro τ hτ
  let g := OrdinaryArchimedeanTwist.twist (complete f) τ
  have hg (n : ℕ) : ‖g n‖≤1 := by
    simpa only [g,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded hf n
  have hX : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hx : 0<(N:ℝ) := lt_trans zero_lt_one hX
  have hl : 0<Real.log N := Real.log_pos hX
  let δ : ℝ := (Real.log (N:ℝ))⁻¹
  have hδ : 0<δ := inv_pos.mpr hl
  have hab : LSeries.abscissaOfAbsConv (LSeries.logMul g)<((1+δ:ℝ):EReal) := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hg n⟩)
      (by exact_mod_cast (show (1:ℝ)<1+δ by linarith))
  have hh := cutoffSeries_norm_le (LSeries.logMul g) hx (show 1≤1+δ by linarith) hab
  rw [bounded_logSeries_cauchy_derivative hg hδ, rpow_one_add_inv_log hX] at hh
  have hs := hsmall τ hτ
  have hsi : (∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries g) (line δ t)‖) ≤ (ε/c)*Real.log N := by
    have hh' := mul_le_mul_of_nonneg_right hs hl.le
    have hid : δ*Real.log N=1 := inv_mul_cancel₀ hl.ne'
    change δ*(∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries g) (line δ t)‖)*Real.log N≤_ at hh'
    rw [mul_right_comm δ, hid, one_mul] at hh'
    exact hh'
  calc
    ‖cutoffSeries (LSeries.logMul g) (N:ℝ)‖ ≤
        (1/(2*Real.pi))*((N:ℝ)*Real.exp 1)*(∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries g) (line δ t)‖) := hh
    _ ≤ (1/(2*Real.pi))*((N:ℝ)*Real.exp 1)*((ε/c)*Real.log N) :=
      mul_le_mul_of_nonneg_left hsi (by positivity)
    _ = ε*(N:ℝ)*Real.log N := by
      dsimp [c]
      field_simp

theorem moving_cutoff_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀τ : ℝ, |τ|≤(N:ℝ)/2 →
      ‖cutoffSeries (OrdinaryArchimedeanTwist.twist (complete f) τ) (N:ℝ)‖≤ε*(N:ℝ) := by
  let R : ℝ := 1+3/ε
  have hR : 1≤R := by dsimp [R]; linarith [div_pos (by norm_num : (0:ℝ)<3) hε]
  have hR0 : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hdiv : 1/R≤ε/3 := by
    apply (div_le_iff₀ hR0).2
    dsimp [R]
    have hh : ε/3*(3/ε)=1 := by field_simp
    nlinarith
  have hloglim : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [moving_logcutoff_small hf hNP (ε/3) (by positivity),
    hloglim.eventually (eventually_ge_atTop (3*Real.log R/ε)),
    eventually_ge_atTop (2:ℕ)] with N hsmall hlog hN
  intro τ hτ
  let g := OrdinaryArchimedeanTwist.twist (complete f) τ
  have hg (n : ℕ) : ‖g n‖≤1 := by
    simpa only [g,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded hf n
  have hX : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hx : 0<(N:ℝ) := lt_trans zero_lt_one hX
  have hl : 0<Real.log N := Real.log_pos hX
  have hlogR : Real.log R≤(ε/3)*Real.log N := by
    have hh := (div_le_iff₀ hε).1 hlog
    nlinarith
  have hdivX : (N:ℝ)/R≤(ε/3)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hdiv hx.le
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm (R⁻¹) (N:ℝ)] using hh
  have hh := cutoff_norm_le_logcutoff_add g hX.le hR hg
  have hs := hsmall τ hτ
  have herr1 := mul_le_mul_of_nonneg_right hdivX hl.le
  have herror2 := mul_le_mul_of_nonneg_left hlogR hx.le
  have htotal : Real.log N*‖cutoffSeries g (N:ℝ)‖≤Real.log N*(ε*(N:ℝ)) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hl).1 htotal

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
