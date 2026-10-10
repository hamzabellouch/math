import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DerivativeConstant
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Twist

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

namespace OrdinaryHorizontalHalasz
open MeasureTheory Set OrdinaryLogDerivative OrdinaryDirichletMeanSquare
open OrdinaryArchimedeanTwist

lemma continuous_derivative_vertical {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) : Continuous (fun t => deriv (LSeries f) (line δ t)) := by
  have hab : LSeries.abscissaOfAbsConv f ≤ (1:ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hf n⟩
  have he : (fun t : ℝ => deriv (LSeries f) (line δ t)) =
      fun t => -LSeries (LSeries.logMul f) (line δ t) := by
    funext t
    exact LSeries_deriv (lt_of_le_of_lt hab (by exact_mod_cast (show 1<(line δ t).re by simp; linarith)))
  rw [he]
  exact (continuous_vertical (by simpa only [LSeries.abscissaOfAbsConv_logMul] using hab) hδ).neg

lemma line_twist (δ t u : ℝ) : line δ t-(u:ℂ)*Complex.I=line δ (t+u) := by
  unfold line
  push_cast
  ring

lemma shifted_derivative_bound {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hm : Complete f) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (u : ℝ) :
    δ*(∫ t in Icc (-1:ℝ) 1, ‖deriv (LSeries f) (line δ (t+u))‖) ≤
      Real.exp 1*derivativeConstant := by
  let f' := twist f u
  have hf' (n : ℕ) : ‖f' n‖≤1 := by simpa only [f',norm_twist] using hf n
  have hm' : Complete f' := fun m n hm0 hn0 => twist_mul f u hm hm0 hn0
  have hd (t : ℝ) : deriv (LSeries f') (line δ t)=deriv (LSeries f) (line δ (t+u)) := by
    rw [derivative_twist f hf u (by simp; linarith),line_twist]
  have hb := uniform_derivative_bound hf' hm' hδ hδ1 (-1) 1
  simp only [hd] at hb
  have hc : Continuous (fun t : ℝ => deriv (LSeries f) (line δ (t+u))) :=
    (continuous_derivative_vertical hf hδ).comp (continuous_id.add continuous_const)
  have hi : IntegrableOn (fun t : ℝ => ‖deriv (LSeries f) (line δ (t+u))‖) (Icc (-1:ℝ) 1) :=
    hc.norm.continuousOn.integrableOn_Icc
  have hw : IntegrableOn (fun t : ℝ => gaussian t*‖deriv (LSeries f) (line δ (t+u))‖) (Icc (-1) 1) :=
    ((by unfold gaussian; fun_prop : Continuous gaussian).mul hc.norm).continuousOn.integrableOn_Icc
  have he (t : ℝ) (ht : t∈Icc (-1:ℝ) 1) : (1:ℝ)≤Real.exp 1*gaussian t := by
    unfold gaussian
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (1+-t^2) := Real.exp_le_exp.mpr (by nlinarith [ht.1,ht.2])
      _ = _ := Real.exp_add _ _
  have hcmp : (∫ t in Icc (-1:ℝ) 1, ‖deriv (LSeries f) (line δ (t+u))‖) ≤
      Real.exp 1*(∫ t in Icc (-1:ℝ) 1, gaussian t*‖deriv (LSeries f) (line δ (t+u))‖) := by
    rw [←MeasureTheory.integral_const_mul]
    apply integral_mono_ae hi (hw.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    nlinarith [mul_le_mul_of_nonneg_right (he t ht) (norm_nonneg (deriv (LSeries f) (line δ (t+u))))]
  exact (mul_le_mul_of_nonneg_left hcmp hδ.le).trans
    (by simpa only [mul_left_comm δ (Real.exp 1)] using mul_le_mul_of_nonneg_left hb (Real.exp_pos 1).le)

end OrdinaryHorizontalHalasz

end

end OAI
