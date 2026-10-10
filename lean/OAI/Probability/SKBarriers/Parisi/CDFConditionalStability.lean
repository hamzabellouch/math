import Mathlib
import OAI.Probability.SKBarriers.Scalar.PositiveTimeChain
import OAI.Probability.SKBarriers.Replicas.TripleScaleStats
import OAI.Probability.SKBarriers.Hierarchy.TimeIncrementBridge
import OAI.Probability.SKBarriers.Parisi.CDFCramer
import OAI.Probability.SKBarriers.Parisi.CDFSquareSusceptibility
import OAI.Probability.SKBarriers.Scalar.ScalarConditionalStability

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarTimeChainAverage_hessian_square_cramer (β : ℝ) (l j : List (ℝ × ℝ≥0))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hc : ScalarSpinConvex f)
    (hj : ∀ p∈j,p.1∈Icc (0:ℝ) 1) :
    let H := scalarTimeChain β j f
    β^2*(chainDuration j:ℝ)*scalarTimeChainAverage β l H (fun x => (rootHessian 0 H x)^2) 0 ≤
      (1+2*(β^2*(chainDuration j:ℝ)))*(scalarTimeChainAverage β (l++j) f (fun x => (rootGradient 0 f x)^2) 0-
        scalarTimeChainAverage β l H (fun x => (rootGradient 0 H x)^2) 0) := by
  have G := scalarIncrementAverage_hessian_square_cramer
    (scaleIncrementChain β (rawTimeChain l)) (scaleIncrementChain β (rawTimeChain j)) hf hc
    (scaleIncrementChain_mass β _ (rawTimeChain_mass _ hj))
  dsimp only at G ⊢
  rw [← scaleIncrementChain_append,← rawTimeChain_append] at G
  simpa only [rawVariance_scale,rawVariance_rawTimeChain,scalarIncrementChain_rawTimeChain,
    scalarIncrementAverage_rawTimeChain] using G

theorem scalarCDF_conditional_stability_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {r q : ℝ} (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    β^2*(q-r)*scalarCDFSusceptibilitySquareAverage β (quantileCDF k Q) r ≤
      (1+2*(β^2*(q-r)))*(scalarCDFOverlap β (quantileCDF k Q) q-
        scalarCDFOverlap β (quantileCDF k Q) r) := by
  let α := quantileCDF k Q
  have ha := quantileCDF_bounds k Q
  have hm := quantileCDF_monotone k Q
  let sr := Real.toNNReal (1-r)
  let sq := Real.toNNReal (1-q)
  let tq := Real.toNNReal q
  let tr := Real.toNNReal r
  let tj := Real.toNNReal (q-r)
  have hsr : (sr:ℝ)=1-r := Real.coe_toNNReal _ (by linarith)
  have hsq : (sq:ℝ)=1-q := Real.coe_toNNReal _ (by linarith)
  have htq : (tq:ℝ)=q := Real.coe_toNNReal _ (by linarith)
  have htr : (tr:ℝ)=r := Real.coe_toNNReal _ hr
  have htj : (tj:ℝ)=q-r := Real.coe_toNNReal _ (sub_nonneg.mpr hrq)
  have hsr1 : sr≤1 := by rw [← NNReal.coe_le_coe,hsr,NNReal.coe_one]; linarith
  have hsq1 : sq≤1 := by rw [← NNReal.coe_le_coe,hsq,NNReal.coe_one]; linarith
  have htr1 : tr≤1 := by rw [← NNReal.coe_le_coe,htr,NNReal.coe_one]; linarith
  have htq1 : tq≤1 := by rw [← NNReal.coe_le_coe,htq,NNReal.coe_one]; exact hq
  have htj1 : tj≤1 := by rw [← NNReal.coe_le_coe,htj,NNReal.coe_one]; linarith
  obtain ⟨l,hdl,hml,_,hmodelL⟩ := quantile_interval_chain β Q hQ (s:=0) (t:=r) le_rfl hr (hrq.trans hq)
  obtain ⟨j,hdj,hmj,_,hmodelJ⟩ := quantile_interval_chain β Q hQ hr hrq hq
  have hdl' : chainDuration l=tr := NNReal.coe_injective (by rw [htr,hdl,sub_zero])
  have hdj' : chainDuration j=tj := NNReal.coe_injective (by rw [htj,hdj])
  have hdlj : chainDuration (l++j)=tq := by
    apply NNReal.coe_injective
    rw [chainDuration_append,NNReal.coe_add,hdl,hdj,htq]; ring
  have hmlj : ∀ p∈l++j,p.1∈Icc (0:ℝ) 1 := by
    intro p hp; exact (List.mem_append.mp hp).elim (hml p) (hmj p)
  have hmodelLJ : TimeChainModels α 0 (l++j) := hmodelL.append (by simpa only [hdl,zero_add,sub_zero] using hmodelJ)
  let F := scalarCDFValue β α q sq
  let H := scalarCDFValue β α r sr
  have hF : BoundedDerivs F := scalarCDFValue_regular β ha hm q sq hsq1
  have hH : BoundedDerivs H := scalarCDFValue_regular β ha hm r sr hsr1
  have hFc : ScalarSpinConvex F := scalarCDFValue_spinConvex β ha hm q sq hsq1
  have he : scalarTimeChain β j F=H := by
    funext x
    rw [← scalarCDFOperator_eq_chain hF (scalarCDFValue_lipschitz β ha hm q sq hsq1)
      β ha hm j hmj r tj htj1 hdj' hmodelJ x]
    exact (congrFun (scalarCDFValue_suffix_semigroup_quantile β Q hQ hr hrq hq) x).symm
  have havr : scalarTimeChainAverage β l H (fun x => (rootGradient 0 H x)^2) 0=scalarCDFOverlap β α r := by
    have ht := scalarCDFGradient_sq_regular β ha hm r sr hsr1
    change scalarTimeChainAverage β l (scalarCDFValue β α r sr) _ 0=_
    rw [scalarCDFValue_rootGradient β ha hm r sr hsr1]
    exact (scalarCDFAverage_eq_chainAverage hH ht.1 ht.2.1
      (scalarCDFValue_lipschitz β ha hm r sr hsr1) (B:=1) ht.2.2.1 (C:=2) ht.2.2.2
      β ha hm l hml 0 tr htr1 hdl' hmodelL 0).symm
  have havq : scalarTimeChainAverage β (l++j) F (fun x => (rootGradient 0 F x)^2) 0=scalarCDFOverlap β α q := by
    have ht := scalarCDFGradient_sq_regular β ha hm q sq hsq1
    change scalarTimeChainAverage β (l++j) (scalarCDFValue β α q sq) _ 0=_
    rw [scalarCDFValue_rootGradient β ha hm q sq hsq1]
    exact (scalarCDFAverage_eq_chainAverage hF ht.1 ht.2.1
      (scalarCDFValue_lipschitz β ha hm q sq hsq1) (B:=1) ht.2.2.1 (C:=2) ht.2.2.2
      β ha hm (l++j) hmlj 0 tq htq1 hdlj hmodelLJ 0).symm
  have havχ : scalarTimeChainAverage β l H (fun x => (rootHessian 0 H x)^2) 0=
      scalarCDFSusceptibilitySquareAverage β α r := by
    change scalarTimeChainAverage β l (scalarCDFValue β α r sr) _ 0=_
    rw [scalarCDFValue_rootHessian β ha hm r sr hsr1]
    exact (scalarCDFAverage_eq_chainAverage_lipschitz hH
      (scalarCDFValue_lipschitz β ha hm r sr hsr1)
      (scalarCDFHessian_square_lipschitz β ha hm r sr hsr1)
      (B:=1) (scalarCDFHessian_square_bound β ha hm r sr hsr1)
      β ha hm l hml 0 tr htr1 hdl' hmodelL 0).symm
  have G := scalarTimeChainAverage_hessian_square_cramer β l j hF hFc hmj
  dsimp only at G
  rw [he,hdj,havr,havq,havχ] at G
  exact G

theorem scalarCDF_conditional_stability (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {r q : ℝ}
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1) :
    β^2*(q-r)*scalarCDFSusceptibilitySquareAverage β α r ≤
      (1+2*(β^2*(q-r)))*(scalarCDFOverlap β α q-scalarCDFOverlap β α r) := by
  let a (n : ℕ) := quantileCDF n (uniformCDFQuantiles n α)
  have hn (n : ℕ) := quantileCDF_bounds n (uniformCDFQuantiles n α)
  have hnm (n : ℕ) := quantileCDF_monotone n (uniformCDFQuantiles n α)
  have hD := uniformCDFQuantiles_L1_tendsto α ha h1
  have Hχ := scalarCDFSusceptibilitySquareAverage_tendsto β ha α.mono hn hnm hD ⟨hr,hrq.trans hq⟩
  have HΓ := scalarCDFOverlap_tendstoUniformlyOn β ha α.mono hn hnm hD
  have HL := Hχ.const_mul (β^2*(q-r))
  have HR := ((HΓ.tendsto_at ⟨hr.trans hrq,hq⟩).sub (HΓ.tendsto_at ⟨hr,hrq.trans hq⟩)).const_mul (1+2*(β^2*(q-r)))
  exact le_of_tendsto_of_tendsto HL HR (Eventually.of_forall (fun n =>
    scalarCDF_conditional_stability_quantile β (uniformCDFQuantiles n α)
      (uniformCDFQuantiles_admissible n α h1) hr hrq hq))

end SK.Analytic

end
end

end OAI
