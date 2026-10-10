import Mathlib
import OAI.Analysis.Commutator.ScalarIndicator

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ]

omit [CompleteSpace H] in
lemma field_inner_integrable (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (ξ η : H) :
    Integrable (fun a => inner ℂ (T a ξ) η) μ := by
  apply (integrable_const (b*‖ξ‖*‖η‖)).mono' ((hm ξ).inner aestronglyMeasurable_const)
  filter_upwards [hb] with a ha
  exact (norm_inner_le_norm (T a ξ) η).trans
    (mul_le_mul_of_nonneg_right (((T a).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right ha (norm_nonneg ξ))) (norm_nonneg η))

omit [CompleteSpace H] in
lemma field_inner_right_integrable (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (ξ η : H) :
    Integrable (fun a => inner ℂ ξ (T a η)) μ := by
  apply (integrable_const (‖ξ‖*(b*‖η‖))).mono' (aestronglyMeasurable_const.inner (hm η))
  filter_upwards [hb] with a ha
  exact (norm_inner_le_norm ξ (T a η)).trans
    (mul_le_mul_of_nonneg_left (((T a).le_opNorm η).trans
      (mul_le_mul_of_nonneg_right ha (norm_nonneg η))) (norm_nonneg ξ))

omit [CompleteSpace H] in
lemma operator_const_inner_indicator (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (ξ η : H) (s : Set Ω) (hs : MeasurableSet s) :
    inner ℂ (operator μ T hm hb (Lp.const 2 μ ξ))
      (indicatorOperator μ s hs (Lp.const 2 μ η))=∫ a in s,inner ℂ (T a ξ) η ∂μ := by
  classical
  rw [L2.inner_def,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [operator_ae μ T hm hb (Lp.const 2 μ ξ),
    Lp.coeFn_const 2 μ ξ,Lp.coeFn_const 2 μ η,
    indicatorOperator_ae μ s hs (Lp.const 2 μ η)] with a h1 h2 h3 h4
  rw [h1,h2,h4]
  by_cases ha : a∈s
  · simp only [Set.indicator_of_mem ha,h3,Function.const_apply]
  · simp [ha]

omit [CompleteSpace H] in
lemma const_inner_operator_indicator (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (ξ η : H) (s : Set Ω) (hs : MeasurableSet s) :
    inner ℂ (Lp.const 2 μ ξ)
      (operator μ T hm hb (indicatorOperator μ s hs (Lp.const 2 μ η)))=
      ∫ a in s,inner ℂ ξ (T a η) ∂μ := by
  classical
  rw [L2.inner_def,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [operator_ae μ T hm hb (indicatorOperator μ s hs (Lp.const 2 μ η)),
    Lp.coeFn_const 2 μ ξ,Lp.coeFn_const 2 μ η,
    indicatorOperator_ae μ s hs (Lp.const 2 μ η)] with a h1 h2 h3 h4
  rw [h1,h2,h4]
  by_cases ha : a∈s
  · simp only [Set.indicator_of_mem ha,h3,Function.const_apply]
  · simp [ha]

theorem adjoint_ae [TopologicalSpace.SeparableSpace H]
    (T U : Ω → H →L[ℂ] H)
    (hT : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    (hU : ∀ ξ,AEStronglyMeasurable (fun a => U a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖U a‖≤c)
    (h : operator μ U hU hc=(operator μ T hT hb).adjoint) :
    ∀ᵐ a ∂μ,U a=(T a).adjoint := by
  have hp (ξ η : H) : ∀ᵐ a ∂μ,inner ℂ (U a ξ) η=inner ℂ ξ (T a η) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (field_inner_integrable μ U hU hc ξ η)
      (field_inner_right_integrable μ T hT hb ξ η)
    intro s hs _
    rw [←operator_const_inner_indicator μ U hU hc ξ η s hs,
      ←const_inner_operator_indicator μ T hT hb ξ η s hs,h]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  let v : ℕ → H := TopologicalSpace.denseSeq H
  have hv : DenseRange v := TopologicalSpace.denseRange_denseSeq H
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hp (v i) (v j)))]
    with a ha
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℂ
  intro η
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact hv.induction_on ξ
    (isClosed_eq ((U a).continuous.inner continuous_const)
      (continuous_id.inner continuous_const))
    (fun i => hv.induction_on η
      (isClosed_eq (continuous_const.inner continuous_id)
        (continuous_const.inner (T a).continuous)) (ha i))

end Kadison.Decomposable

end

end
end

end OAI
