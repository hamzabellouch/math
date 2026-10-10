import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogSeriesCauchyDerivative
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RieszCoeffNorm

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
open OrdinaryRieszPerron Completion

theorem cutoff_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (ε : ℝ) (hε : 0<ε) :
    ∃M : ℝ, 1<M ∧ ∀X : ℝ, M≤X → ‖cutoffSeries (complete f) X‖≤ε*X := by
  obtain ⟨M₀,hM₀,hsmall⟩ := logcutoff_small hf hNP (ε/3) (by positivity)
  let R : ℝ := 1+3/ε
  have hR : 1≤R := by dsimp [R]; linarith [div_pos (by norm_num : (0:ℝ)<3) hε]
  have hR0 : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hdiv : 1/R≤ε/3 := by
    apply (div_le_iff₀ hR0).2
    dsimp [R]
    have hh : ε/3*(3/ε)=1 := by field_simp
    nlinarith
  let M : ℝ := max M₀ (Real.exp (3*Real.log R/ε))
  have hM : 1<M := lt_of_lt_of_le hM₀ (le_max_left _ _)
  refine ⟨M,hM,?_⟩
  intro X hMX
  have hX : 1<X := lt_of_lt_of_le hM hMX
  have hx : 0<X := lt_trans zero_lt_one hX
  have hl : 0<Real.log X := Real.log_pos hX
  have hX0 : M₀≤X := le_trans (le_max_left _ _) hMX
  have hXe : Real.exp (3*Real.log R/ε)≤X := le_trans (le_max_right _ _) hMX
  have hlog : 3*Real.log R/ε≤Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hXe
  have hlogR : Real.log R≤(ε/3)*Real.log X := by
    have hh := (div_le_iff₀ hε).1 hlog
    nlinarith
  have hdivX : X/R≤(ε/3)*X := by
    have hh := mul_le_mul_of_nonneg_right hdiv hx.le
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm (R⁻¹) X] using hh
  have hh := cutoff_norm_le_logcutoff_add (complete f) hX.le hR (complete_oneBounded hf)
  have hs := hsmall X hX0
  have herr1 := mul_le_mul_of_nonneg_right hdivX hl.le
  have herror2 := mul_le_mul_of_nonneg_left hlogR hx.le
  have htotal : Real.log X*‖cutoffSeries (complete f) X‖≤Real.log X*(ε*X) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hl).1 htotal

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
