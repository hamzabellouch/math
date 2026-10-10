import OAI.NumberTheory.Jacobsthal.Analysis.CompactTestMeasurable
import OAI.NumberTheory.Jacobsthal.Renewal.ContinuousCompletedOccupation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SignedCompletedPowers

open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open CemeteryKernel CompactTestMeasurable

variable {α : Type*} [MeasurableSpace α]

theorem finite_kernel_power (K : Kernel α α) [IsFiniteKernel K] (n : ℕ) : IsFiniteKernel (K^n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel α α); infer_instance
  | succ n ih =>
    let := ih
    have hp : K^(n+1) = (K^n) ∘ₖ K := pow_succ _ _
    rw [hp]
    infer_instance

noncomputable def liftReal (F : α → ℝ) : Space α → ℝ := Sum.elim F (fun _ => 0)

theorem liftReal_measurable {F : α → ℝ} (hF : Measurable F) : Measurable (liftReal F) := hF.sumElim measurable_const

theorem real_power_lift (K : Kernel α α) (n : ℕ) (x : α)
    [IsFiniteMeasure (((complete K)^n) (.inl x))] [IsFiniteMeasure ((K^n) x)]
    {F : α → ℝ} (hF : Measurable F) {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y,|F y| ≤ A) :
    (∫ y,liftReal F y ∂((complete K)^n) (.inl x)) = ∫ y,F y ∂(K^n) x := by
  have hL : ∀ y : Space α,|liftReal F y| ≤ A := by
    intro y
    cases y with
    | inl a => exact hbound a
    | inr u => simpa only [liftReal,Sum.elim_inr,abs_zero] using hA
  have hIl : Integrable (liftReal F) (((complete K)^n) (.inl x)) := bounded_integrable (liftReal_measurable hF) hL
  have hIr : Integrable F ((K^n) x) := bounded_integrable hF hbound
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIl,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIr]
  have hp : (fun y : Space α => ENNReal.ofReal (liftReal F y)) = CemeteryPowers.liftReward (fun y => ENNReal.ofReal (F y)) := by
    funext y
    cases y <;> simp [liftReal,CemeteryPowers.liftReward]
  have hn : (fun y : Space α => ENNReal.ofReal (-liftReal F y)) = CemeteryPowers.liftReward (fun y => ENNReal.ofReal (-F y)) := by
    funext y
    cases y <;> simp [liftReal,CemeteryPowers.liftReward]
  rw [hp,hn,CemeteryPowers.power_lift K (F:=fun y => ENNReal.ofReal (F y)) (ENNReal.measurable_ofReal.comp hF),
    CemeteryPowers.power_lift K (F:=fun y => ENNReal.ofReal (-F y)) (ENNReal.measurable_ofReal.comp hF.neg)]
  rfl

open FinitePathMeasures ContinuousKilledBins LowStateHorizon

theorem continuous_signed_power (v ell S : ℝ) (n : ℕ) (z : CostState)
    {F : CostState → ℝ} (hF : Measurable F) {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y,|F y| ≤ A) :
    (∫ y,liftReal F y ∂((continuousChain v ell S)^n) (.inl z)) =
      ∫ y,F y ∂((lowKernel costKernel v ell S)^n) z := by
  let : IsFiniteKernel (lowKernel costKernel v ell S) := by unfold lowKernel; infer_instance
  let := finite_kernel_power (lowKernel costKernel v ell S) n
  let := finite_kernel_power (continuousChain v ell S) n
  let : IsFiniteMeasure (((complete (lowKernel costKernel v ell S))^n) (.inl z)) := by
    change IsFiniteMeasure (((continuousChain v ell S)^n) (.inl z))
    infer_instance
  exact real_power_lift (lowKernel costKernel v ell S) n z hF hA hbound

end NumberTheoryLean.SignedCompletedPowers

end

end Erdos970

end OAI
