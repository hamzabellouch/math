import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.TimeChainOn
import OAI.Probability.SKBarriers.Hierarchy.TimeChainExactPenalty
import OAI.Probability.SKBarriers.Scalar.SuffixPartitionSusceptibility
import OAI.Probability.SKBarriers.Parisi.CDFCramer

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem TimeChainOn.sub_nonneg {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) : 0 ≤ t-s := by
  rw [← l.duration]; positivity

theorem TimeChainOn.nn_duration {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) :
    chainDuration l.chain=Real.toNNReal (t-s) := by
  apply NNReal.coe_injective
  rw [l.duration,Real.coe_toNNReal _ l.sub_nonneg]

theorem TimeChainOn.nn_le_one {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) (h : t-s≤1) :
    Real.toNNReal (t-s)≤1 := by
  rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ l.sub_nonneg,NNReal.coe_one]; exact h

theorem TimeChainOn.scalar_operator (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) {f : ℝ → ℝ} (hf : BoundedDerivs f) {K : ℝ≥0} (hfK : LipschitzWith K f) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) f=
      scalarCDFOperator β α s (Real.toNNReal (t-s)) f := by
  rw [scalarIncrementChain_rawTimeChain]
  funext x
  exact (scalarCDFOperator_eq_chain hf hfK β ha hm l.chain l.mass s _ (l.nn_le_one h) l.nn_duration l.models x).symm

theorem TimeChainOn.scalar_value (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) scalarSpinTerminal=
      scalarCDFValue β α s (Real.toNNReal (t-s)) :=
  l.scalar_operator β ha hm h scalarSpinTerminal_regular scalarSpinTerminal_lipschitz

theorem TimeChainOn.scalar_hessian (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) :
    rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) scalarSpinTerminal)=
      scalarCDFHessian β α s (Real.toNNReal (t-s)) := by
  rw [l.scalar_value β ha hm h,scalarCDFValue_rootHessian β ha hm s _ (l.nn_le_one h)]

theorem TimeChainOn.scalar_average (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l.chain)) f g=
      scalarCDFAverage β α s (Real.toNNReal (t-s)) f g := by
  rw [scalarIncrementAverage_rawTimeChain]
  funext x
  exact (scalarCDFAverage_eq_chainAverage_lipschitz hf hfK hgL hB β ha hm l.chain l.mass s _
    (l.nn_le_one h) l.nn_duration l.models x).symm

theorem TimeChainOn.scalar_susceptibility (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {q : ℝ} (hq : q∈Icc (0:ℝ) 1)
    (l : TimeChainOn α 0 q) (r : TimeChainOn α q 1) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l.chain))
      (scalarIncrementChain (scaleIncrementChain β (rawTimeChain r.chain)) scalarSpinTerminal)
      (rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (rawTimeChain r.chain)) scalarSpinTerminal)) 0=
      scalarCDFSusceptibilityAverage β α q := by
  have h : 1-q≤1 := by linarith [hq.1]
  rw [r.scalar_hessian β ha hm h,r.scalar_value β ha hm h]
  rw [l.scalar_average β ha hm (by linarith [hq.2])
    (scalarCDFValue_regular β ha hm q _ (r.nn_le_one h))
    (scalarCDFValue_lipschitz β ha hm q _ (r.nn_le_one h))
    (scalarCDFHessian_lipschitz β ha hm q _ (r.nn_le_one h))
    (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ (r.nn_le_one h))]
  simp only [sub_zero,scalarCDFSusceptibilityAverage]

theorem TimeChainOn.area {α : ℝ → ℝ} (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    rawArea (rawTimeChain l.chain)=∫ x in s..t,α x := by
  rw [rawArea_rawTimeChain,l.models.area hm,l.duration,add_sub_cancel]

theorem TimeChainOn.penalty {α : ℝ → ℝ} (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    rawPenalty (rawTimeChain l.chain) s=2*∫ x in s..t,x*α x := by
  rw [rawPenalty_rawTimeChain,l.models.quadraticPenalty hm,l.duration,add_sub_cancel]

end SK.Analytic

end
end

end OAI
