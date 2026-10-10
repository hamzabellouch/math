import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CompactDerivativeSmall
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ContinuousDerivativeVertical
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DerivativeVerticalBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Box

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

namespace OrdinaryCorrelations.PretentiousEuler
open MeasureTheory Set Completion OrdinaryHorizontalHalasz OrdinaryDirichletMeanSquare

lemma compact_unweighted_derivative_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (T ζ : ℝ) (hζ : 0<ζ) :
    ∃η : ℝ, 0<η ∧ ∀δ : ℝ, 0<δ → δ≤η →
      (∫t in Icc (-T) T, δ*‖deriv (LSeries (complete f)) (line δ t)‖)≤ζ := by
  obtain ⟨η,hη,hsmall⟩ := compact_derivative_small hf hNP T (ζ:=ζ/Real.exp (T^2)) (by positivity)
  refine ⟨η,hη,?_⟩
  intro δ hδ hδη
  have hc := continuous_derivative_vertical (complete_oneBounded hf) hδ
  have hi : IntegrableOn (fun t : ℝ => δ*‖deriv (LSeries (complete f)) (line δ t)‖) (Icc (-T) T) :=
    (hc.norm.const_mul δ).continuousOn.integrableOn_Icc
  have hwi : IntegrableOn (fun t : ℝ => gaussian t*‖deriv (LSeries (complete f)) (line δ t)‖) (Icc (-T) T) :=
    (derivative_gaussian_integrable (complete_oneBounded hf) hδ).integrableOn
  have hb (t : ℝ) (ht : t∈Icc (-T) T) : 1≤Real.exp (T^2)*gaussian t := by
    have ht2 : t^2≤T^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (show 0≤T+t by linarith [ht.1])]
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (T^2+-t^2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_add _ _
  have hh : (∫t in Icc (-T) T, δ*‖deriv (LSeries (complete f)) (line δ t)‖) ≤
      Real.exp (T^2)*(δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries (complete f)) (line δ t)‖)) := by
    rw [←MeasureTheory.integral_const_mul,←MeasureTheory.integral_const_mul]
    apply integral_mono_ae hi ((hwi.const_mul δ).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    nlinarith [mul_le_mul_of_nonneg_right (hb t ht) (mul_nonneg hδ.le (norm_nonneg (deriv (LSeries (complete f)) (line δ t))))]
  exact hh.trans (by
    have he := mul_le_mul_of_nonneg_left (hsmall δ hδ hδη) (Real.exp_pos (T^2)).le
    simpa only [mul_div_cancel₀ ζ (Real.exp_ne_zero (T^2))] using he)

theorem global_derivative_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (ζ : ℝ) (hζ : 0<ζ) :
    ∃η : ℝ, 0<η ∧ ∀δ : ℝ, 0<δ → δ≤η →
      δ*(∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries (complete f)) (line δ t)‖)≤ζ := by
  have hK : 0≤Real.exp 1*derivativeConstant := mul_nonneg (Real.exp_pos 1).le derivativeConstant_nonneg
  have hc (δ : ℝ) (hδ : 0<δ) : Continuous (fun t : ℝ => δ*‖deriv (LSeries (complete f)) (line δ t)‖) :=
    (continuous_derivative_vertical (complete_oneBounded hf) hδ).norm.const_mul δ
  have hB (δ : ℝ) (hδ : 0<δ) : ∃B : ℝ, ∀t : ℝ,
      ‖δ*‖deriv (LSeries (complete f)) (line δ t)‖‖≤B := by
    obtain ⟨B,hB⟩ := derivative_vertical_bounded (complete_oneBounded hf) hδ
    refine ⟨δ*B,fun t => ?_⟩
    rw [Real.norm_of_nonneg (mul_nonneg hδ.le (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hB t) hδ.le
  have hL (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (u : ℝ) :
      (∫t in Icc (-1:ℝ) 1, δ*‖deriv (LSeries (complete f)) (line δ (t+u))‖)≤Real.exp 1*derivativeConstant := by
    rw [MeasureTheory.integral_const_mul]
    exact shifted_derivative_bound (complete_oneBounded hf) (complete_isComplete f) hδ hδ1 u
  obtain ⟨η,hη,hsmall⟩ := OrdinaryCauchyTail.small_of_compact hK hc
    (fun δ t hδ => mul_nonneg hδ.le (norm_nonneg _)) hB hL
    (compact_unweighted_derivative_small hf hNP) ζ hζ
  refine ⟨η,hη,fun δ hδ hδη => ?_⟩
  have hh := hsmall δ hδ hδη
  simp only [OrdinaryCauchyTail.cauchy,mul_left_comm _ δ,MeasureTheory.integral_const_mul] at hh
  exact hh

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
