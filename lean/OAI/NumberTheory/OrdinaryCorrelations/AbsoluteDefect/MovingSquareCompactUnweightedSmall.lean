import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ContinuousDerivativeVertical
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DerivativeVerticalBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Box
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MovingSquareCompactWeightedSmall

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
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
open MeasureTheory Set Completion OrdinaryHorizontalHalasz OrdinaryDirichletMeanSquare

lemma moving_square_compact_unweighted_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (T ζ : ℝ) (hζ : 0<ζ) :
    ∀ᶠ N : ℕ in atTop, ∀τ : ℝ, |τ|≤(N:ℝ)^2/2 →
      (∫t in Icc (-T) T, (Real.log (N:ℝ))⁻¹*
        ‖deriv (LSeries (OrdinaryArchimedeanTwist.twist (complete f) τ))
          (line ((Real.log (N:ℝ))⁻¹) t)‖)≤ζ := by
  filter_upwards [moving_square_compact_weighted_small hf hNP T (ζ/Real.exp (T^2))
    (by positivity), eventually_ge_atTop (2:ℕ)] with N hsmall hN
  intro τ hτ
  let δ := (Real.log (N:ℝ))⁻¹
  let g := OrdinaryArchimedeanTwist.twist (complete f) τ
  have hδ : 0<δ := inv_pos.mpr (Real.log_pos (by exact_mod_cast (show 1<N by omega)))
  have hg (n : ℕ) : ‖g n‖≤1 := by
    simpa only [g,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded hf n
  have hc := continuous_derivative_vertical hg hδ
  have hi : IntegrableOn (fun t : ℝ => δ*‖deriv (LSeries g) (line δ t)‖) (Icc (-T) T) :=
    (hc.norm.const_mul δ).continuousOn.integrableOn_Icc
  have hwi : IntegrableOn (fun t : ℝ => gaussian t*‖deriv (LSeries g) (line δ t)‖) (Icc (-T) T) :=
    (derivative_gaussian_integrable hg hδ).integrableOn
  have hb (t : ℝ) (ht : t∈Icc (-T) T) : 1≤Real.exp (T^2)*gaussian t := by
    have ht2 : t^2≤T^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (show 0≤T+t by linarith [ht.1])]
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (T^2+-t^2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_add _ _
  have hh : (∫t in Icc (-T) T, δ*‖deriv (LSeries g) (line δ t)‖) ≤
      Real.exp (T^2)*(δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries g) (line δ t)‖)) := by
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_mono_ae hi ((hwi.const_mul δ).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    nlinarith [mul_le_mul_of_nonneg_right (hb t ht) (mul_nonneg hδ.le (norm_nonneg (deriv (LSeries g) (line δ t))))]
  exact hh.trans (by
    have he := mul_le_mul_of_nonneg_left (hsmall τ hτ) (Real.exp_pos (T^2)).le
    simpa only [mul_div_cancel₀ ζ (Real.exp_ne_zero (T^2))] using he)

theorem moving_square_global_derivative_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (ζ : ℝ) (hζ : 0<ζ) :
    ∀ᶠ N : ℕ in atTop, ∀τ : ℝ, |τ|≤(N:ℝ)^2/2 →
      (Real.log (N:ℝ))⁻¹*(∫t : ℝ, (1+t^2)⁻¹*
        ‖deriv (LSeries (OrdinaryArchimedeanTwist.twist (complete f) τ))
          (line ((Real.log (N:ℝ))⁻¹) t)‖)≤ζ := by
  let K := Real.exp 1*derivativeConstant
  have hK0 : 0≤K := mul_nonneg (Real.exp_pos 1).le derivativeConstant_nonneg
  have heps : 0<ζ/(3*(K+1)) := by positivity
  have he := OrdinaryCauchyTail.tendsto_tail_integral.eventually (eventually_lt_nhds heps)
  obtain ⟨R,hR,hRi⟩ := (he.and (eventually_ge_atTop (1:ℝ))).exists
  filter_upwards [moving_square_compact_unweighted_small hf hNP (R+1) (ζ/2) (by positivity),
    logarithmic_delta_tendsto.eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (2:ℕ)] with N hsmall hd1 hN
  intro τ hτ
  let δ := (Real.log (N:ℝ))⁻¹
  let b := OrdinaryArchimedeanTwist.twist (complete f) τ
  let g := fun t : ℝ => δ*‖deriv (LSeries b) (line δ t)‖
  have hδ : 0<δ := inv_pos.mpr (Real.log_pos (by exact_mod_cast (show 1<N by omega)))
  have hδ1 : δ≤1 := hd1.le
  have hb (n : ℕ) : ‖b n‖≤1 := by
    simpa only [b,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded hf n
  have hbm : OrdinaryLogDerivative.Complete b := fun m n hm hn =>
    OrdinaryArchimedeanTwist.twist_mul (complete f) τ (complete_isComplete f) hm hn
  have hg : Continuous g := (continuous_derivative_vertical hb hδ).norm.const_mul δ
  have hg0 (t : ℝ) : 0≤g t := mul_nonneg hδ.le (norm_nonneg _)
  obtain ⟨B,hBB⟩ := derivative_vertical_bounded hb hδ
  have hB (t : ℝ) : ‖g t‖≤δ*B := by
    rw [Real.norm_of_nonneg (hg0 t)]
    exact mul_le_mul_of_nonneg_left (hBB t) hδ.le
  have hlocal (u : ℝ) : (∫t in Icc (-1:ℝ) 1, g (t+u))≤K := by
    simp only [g,integral_const_mul]
    exact shifted_derivative_bound hb hbm hδ hδ1 u
  have htail := OrdinaryCauchyTail.tail_bound hg hg0 hB hlocal R
  have htail0 : 0≤∫u : ℝ, OrdinaryCauchyTail.tailWeight R u :=
    integral_nonneg (OrdinaryCauchyTail.tail_nonneg R)
  have htail' : (∫t : ℝ, OrdinaryCauchyTail.tailWeight (R+1) t*g t)≤ζ/2 := by
    have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<3*(K+1))).mp hR
    nlinarith
  have hi : IntegrableOn g (Icc (-(R+1)) (R+1)) := hg.continuousOn.integrableOn_Icc
  have hci := (OrdinaryCauchyTail.cauchy_integrable.mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall hB)).integrableOn (s:=Icc (-(R+1)) (R+1))
  have hc : (∫t in Icc (-(R+1)) (R+1), OrdinaryCauchyTail.cauchy t*g t)≤ζ/2 := by
    apply (integral_mono_ae hci hi _).trans (hsmall τ hτ)
    exact Eventually.of_forall (fun t => by
      nlinarith [mul_le_mul_of_nonneg_right (OrdinaryCauchyTail.cauchy_le_one t) (hg0 t)])
  have hh : (∫t : ℝ, OrdinaryCauchyTail.cauchy t*g t)≤ζ := by
    rw [OrdinaryCauchyTail.tail_decomposition hg hB (R+1)]
    linarith
  simpa only [OrdinaryCauchyTail.cauchy,g,mul_left_comm _ δ,integral_const_mul] using hh

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
