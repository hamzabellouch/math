import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOverlapConvergence
import OAI.Probability.SKBarriers.Parisi.CDFSemigroup
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyCramer
import OAI.Probability.SKBarriers.Parisi.CDFEndpoint

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarCDFValue_rootGradient (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    rootGradient 0 (scalarCDFValue β α s t)=scalarCDFGradient β α s t := by
  funext x
  exact ((scalarCDFValue_regular β ha hm s t ht).1.differentiable (by norm_num) x |>.hasDerivAt).unique
    (scalarCDFValue_hasDerivAt β ha hm s t ht x)

theorem scalarCDFValue_rootHessian (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    rootHessian 0 (scalarCDFValue β α s t)=scalarCDFHessian β α s t := by
  funext x
  have H : HasDerivAt (rootGradient 0 (scalarCDFValue β α s t))
      (rootHessian 0 (scalarCDFValue β α s t) x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using
      rootGradientLine_hasDerivAt 0 (scalarCDFValue_regular β ha hm s t ht) 0 x
  rw [scalarCDFValue_rootGradient β ha hm s t ht] at H
  exact H.unique (scalarCDFGradient_hasDerivAt β ha hm s t ht x)

theorem scalarCDFValue_spinConvex (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : ScalarSpinConvex (scalarCDFValue β α s t) := by
  intro x
  rw [scalarCDFValue_rootGradient β ha hm s t ht,scalarCDFValue_rootHessian β ha hm s t ht]
  exact (scalarCDF_derivative_bounds β ha hm s t ht x).2

theorem chain_coefficients_variance (β : ℝ) (l : List (ℝ × ℝ≥0)) :
    (∑ i : Fin l.length, (β*Real.sqrt ((l.get i).2:ℝ))^2)=β^2*(chainDuration l:ℝ) := by
  simp only [mul_pow,Real.sq_sqrt (NNReal.coe_nonneg _),← Finset.mul_sum]
  congr 1
  induction l with
  | nil => simp [chainDuration]
  | cons p l ih => simpa [Fin.sum_univ_succ,chainDuration] using congrArg ((p.2:ℝ)+·) ih

theorem scalarTimeChain_cramer {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hc : ScalarSpinConvex f) (β : ℝ) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1) (x : ℝ) :
    let V := scalarTimeChainAverage β l f (fun y => (rootGradient 0 f y)^2) x-
      (rootGradient 0 (scalarTimeChain β l f) x)^2
    β^2*(chainDuration l:ℝ)*(max (rootHessian 0 (scalarTimeChain β l f) x-V) 0)^2 ≤ V := by
  have H := scalarHierarchy_cramer hf hc l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) (fun i => hm _ (List.get_mem _ _)) x
  dsimp only at H ⊢
  rw [chain_coefficients_variance] at H
  simpa only [scalarTimeChainAverage,scalarTimeChain_eq_hierarchy] using H

theorem scalarCDFOverlap_cramer_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    β^2*q*(max (scalarCDFHessian β (quantileCDF k Q) 0 1 0-scalarCDFOverlap β (quantileCDF k Q) q) 0)^2 ≤
      scalarCDFOverlap β (quantileCDF k Q) q := by
  let α := quantileCDF k Q
  have ha := quantileCDF_bounds k Q
  have hm := quantileCDF_monotone k Q
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal q hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)
  have ht1 : t ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr hq.2
  have hr1 : r ≤ 1 := Real.toNNReal_le_iff_le_coe.mpr (by simp only [NNReal.coe_one]; linarith [hq.1])
  obtain ⟨l,hd,hl,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have htr : chainDuration l=t+r := by
    rw [hd]; apply NNReal.coe_injective
    rw [NNReal.coe_add,ht,hr,NNReal.coe_one]; ring
  obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,hs₁,hs₂,he⟩ := scalarTimeChain_split_at β α l hl 0 hmodel t r htr
  let f := scalarCDFValue β α q r
  have hf : BoundedDerivs f := scalarCDFValue_regular β ha hm q r hr1
  have hfc : ScalarSpinConvex f := scalarCDFValue_spinConvex β ha hm q r hr1
  have hLip := scalarCDFValue_lipschitz β ha hm q r hr1
  have hroot : scalarTimeChain β l₁ f=scalarCDFValue β α 0 1 := by
    funext x
    rw [← scalarCDFOperator_eq_chain hf hLip β ha hm l₁ hm₁ 0 t ht1 h₁ hs₁ x]
    exact (congrFun (scalarCDFValue_semigroup_quantile β Q hQ hq) x).symm
  have htest := scalarCDFGradient_sq_regular β ha hm q r hr1
  have hav : scalarTimeChainAverage β l₁ f (fun y => (rootGradient 0 f y)^2) 0=
      scalarCDFOverlap β α q := by
    change scalarTimeChainAverage β l₁ (scalarCDFValue β α q r) _ 0=_
    rw [scalarCDFValue_rootGradient β ha hm q r hr1]
    exact (scalarCDFAverage_eq_chainAverage hf htest.1 htest.2.1 hLip
      (B:=1) htest.2.2.1 (C:=2) htest.2.2.2 β ha hm l₁ hm₁ 0 t ht1 h₁ hs₁ 0).symm
  have H := scalarTimeChain_cramer hf hfc β l₁ hm₁ 0
  dsimp only at H
  rw [h₁,ht,hav,hroot,scalarCDFValue_rootGradient β ha hm 0 1 le_rfl,
    scalarCDFValue_rootHessian β ha hm 0 1 le_rfl,scalarCDFGradient_zero β ha hm 0 1 le_rfl,
    zero_pow (by decide : 2≠0),sub_zero] at H
  exact H

theorem scalarCDFOverlap_cramer (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    β^2*q*(max (scalarCDFHessian β α 0 1 0-scalarCDFOverlap β α q) 0)^2 ≤ scalarCDFOverlap β α q := by
  let a (n : ℕ) := quantileCDF n (uniformCDFQuantiles n α)
  have hn (n : ℕ) := quantileCDF_bounds n (uniformCDFQuantiles n α)
  have hnm (n : ℕ) := quantileCDF_monotone n (uniformCDFQuantiles n α)
  have hD := uniformCDFQuantiles_L1_tendsto α ha h1
  have Hχ := (scalarCDFHessian_tendstoUniformly β ha α.mono hn hnm hD).tendsto_at 0
  have HΓ := (scalarCDFOverlap_tendstoUniformlyOn β ha α.mono hn hnm hD).tendsto_at hq
  have HL := ((Hχ.sub HΓ).max (tendsto_const_nhds (x := (0:ℝ)))).pow 2 |>.const_mul (β^2*q)
  exact le_of_tendsto_of_tendsto HL HΓ (Eventually.of_forall (fun n =>
    scalarCDFOverlap_cramer_quantile β (uniformCDFQuantiles n α) (uniformCDFQuantiles_admissible n α h1) hq))

end SK.Analytic

end
end

end OAI
