import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeResidual

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def bridgePrefix (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) := centerMap.comp (prefixMap u)
@[simp] lemma bridgePrefix_apply (u : Time) (f : C(Time,ℝ)) (s : Time) :
    bridgePrefix u f s=f (prefixTime u s)-(s:ℝ)*f u := by
  simp only [bridgePrefix,ContinuousLinearMap.comp_apply,centerMap_apply,prefixMap_apply]
  congr 2
  congr 1
  apply Subtype.ext
  simp [prefixTime]

lemma bridgePrefix_eq (u : Time) (ω : Noise) :
    bridgePrefix u (bridge ω)=centerMap (prefixMap u (path ω)) := by
  ext s
  simp only [bridgePrefix_apply,bridge_apply,centerMap_apply,prefixMap_apply]
  have he : prefixTime u 1=u := by ext; simp [prefixTime]
  rw [he]
  change path ω (prefixTime u s)-((u:ℝ)*(s:ℝ))*path ω 1-
    (s:ℝ)*(path ω u-(u:ℝ)*path ω 1)=_
  ring

lemma bridgePrefix_law (u : Time) :
    law.map (fun ω ↦ bridgePrefix u (bridge ω))=
      bridgeLaw.map (fun β ↦ Real.sqrt (u:ℝ) • β) := by
  calc
    _ = (law.map (fun ω ↦ prefixMap u (path ω))).map centerMap := by
      rw [Measure.map_map (f:=fun ω ↦ prefixMap u (path ω)) centerMap.continuous.measurable
        ((prefixMap u).continuous.measurable.comp measurable_path)]
      congr 1
      funext ω
      exact bridgePrefix_eq u ω
    _ = _ := by
      rw [prefix_law,Measure.map_map (f:=fun ω ↦ Real.sqrt (u:ℝ) • path ω) centerMap.continuous.measurable ((show Continuous (fun w : C(Time,ℝ) ↦ Real.sqrt (u:ℝ) • w) from by fun_prop).measurable.comp measurable_path),
        bridgeLaw,Measure.map_map (by fun_prop) measurable_bridge]
      congr 1
      funext ω
      exact (centerMap.map_smul _ _).trans (congrArg (fun β ↦ Real.sqrt (u:ℝ) • β) (centerMap_path ω))

lemma prefixRemainder_gaussian (u : Time) :
    IsGaussianProcess (Sum.elim (fun s ω ↦ prefixMap u (bridge ω) s)
      (fun s ω ↦ bridgeRemainder u (bridge ω) s)) law := by
  classical
  constructor
  intro I
  let loc : Option I → Time := fun i ↦ i.elim u
    (fun j ↦ j.val.elim (prefixTime u) (suffixTime u))
  let ev (i : Option I) : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let L : (Option I → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
    (fun j ↦ match j.val with
      | .inl _ => ev (some j)
      | .inr s => ev (some j) - (1-(s:ℝ)) • ev none)
  convert! (finite_bridge_gaussian loc).map_fun L using 1
  funext ω j
  cases hj : j.val <;> simp [L,loc,ev,hj]

lemma prefixRemainder_independent (u : Time) :
    IndepFun (fun ω ↦ prefixMap u (bridge ω)) (fun ω ↦ bridgeRemainder u (bridge ω)) law := by
  have hc (a s : Time) :
      cov[fun ω ↦ prefixMap u (bridge ω) a,fun ω ↦ bridgeRemainder u (bridge ω) s;law]=0 := by
    simp only [prefixMap_apply,bridgeRemainder_apply]
    rw [covariance_fun_sub_right (bridge_eval_law _).hasGaussianLaw.memLp_two
      (bridge_eval_law _).hasGaussianLaw.memLp_two ((bridge_eval_law u).hasGaussianLaw.memLp_two.const_mul _),
      covariance_const_mul_right,bridge_covariance,bridge_covariance,
      min_eq_left ((prefixTime_le u a).trans (le_suffixTime u s)),min_eq_left (prefixTime_le u a)]
    change (u:ℝ)*(a:ℝ)-((u:ℝ)*(a:ℝ))*((u:ℝ)+(1-(u:ℝ))*(s:ℝ))-
      (1-(s:ℝ))*((u:ℝ)*(a:ℝ)-((u:ℝ)*(a:ℝ))*(u:ℝ))=0
    ring
  have hi := (prefixRemainder_gaussian u).indepFun_of_covariance_eq_zero
    (fun s ↦ ((continuous_eval_const s).measurable.comp ((prefixMap u).continuous.measurable.comp measurable_bridge)).aemeasurable)
    (fun s ↦ ((continuous_eval_const s).measurable.comp ((bridgeRemainder u).continuous.measurable.comp measurable_bridge)).aemeasurable) hc
  have hid := hi.comp
    (Measurable.of_eval fun n ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time n))
    (Measurable.of_eval fun n ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time n))
  have hh := hid.comp denseEval_embedding.measurable_invFun denseEval_embedding.measurable_invFun
  convert hh using 1 <;> funext ω <;> exact (denseEval_embedding.leftInverse_invFun _).symm

lemma prefixValue_gaussian (u : Time) :
    IsGaussianProcess (Sum.elim (fun _ : Unit ↦ fun ω ↦ bridge ω u)
      (fun s ω ↦ bridgePrefix u (bridge ω) s)) law := by
  classical
  constructor
  intro I
  let loc : Option I → Time := fun i ↦ i.elim u
    (fun j ↦ j.val.elim (fun _ ↦ u) (prefixTime u))
  let ev (i : Option I) : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let L : (Option I → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
    (fun j ↦ match j.val with
      | .inl _ => ev (some j)
      | .inr s => ev (some j) - (s:ℝ) • ev none)
  convert! (finite_bridge_gaussian loc).map_fun L using 1
  funext ω j
  cases hj : j.val <;> simp [L,loc,ev,hj]

lemma prefixValue_independent (u : Time) :
    IndepFun (fun ω ↦ bridge ω u) (fun ω ↦ bridgePrefix u (bridge ω)) law := by
  have hc (_ : Unit) (s : Time) :
      cov[fun ω ↦ bridge ω u,fun ω ↦ bridgePrefix u (bridge ω) s;law]=0 := by
    simp only [bridgePrefix_apply]
    rw [covariance_fun_sub_right (bridge_eval_law _).hasGaussianLaw.memLp_two
      (bridge_eval_law _).hasGaussianLaw.memLp_two ((bridge_eval_law u).hasGaussianLaw.memLp_two.const_mul _),
      covariance_const_mul_right,bridge_covariance,bridge_covariance,
      min_eq_right (prefixTime_le u s),min_self]
    change (u:ℝ)*(s:ℝ)-(u:ℝ)*((u:ℝ)*(s:ℝ))-
      (s:ℝ)*((u:ℝ)-(u:ℝ)*(u:ℝ))=0
    ring
  have hi := (prefixValue_gaussian u).indepFun_of_covariance_eq_zero
    (fun _ ↦ ((continuous_eval_const u).measurable.comp measurable_bridge).aemeasurable)
    (fun s ↦ ((continuous_eval_const s).measurable.comp ((bridgePrefix u).continuous.measurable.comp measurable_bridge)).aemeasurable) hc
  have hid := hi.comp (measurable_pi_apply ())
    (Measurable.of_eval fun n ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time n))
  have hh := hid.comp measurable_id denseEval_embedding.measurable_invFun
  convert hh using 1
  · rfl
  · funext ω
    exact (denseEval_embedding.leftInverse_invFun _).symm

lemma bridge_three_law (u : Time) :
    bridgeLaw.map (fun β ↦ ((β u,bridgePrefix u β),bridgeRemainder u β))=
      ((gaussianReal 0 (Real.toNNReal ((u:ℝ)-(u:ℝ)^2))).prod
        (bridgeLaw.map (fun β ↦ Real.sqrt (u:ℝ) • β))).prod
        (bridgeLaw.map (fun β ↦ Real.sqrt (1-(u:ℝ)) • β)) := by
  have hi := (prefixRemainder_independent u).comp
    (show Measurable (fun f : C(Time,ℝ) ↦ (f 1,centerMap f)) from by fun_prop) measurable_id
  have he : (fun ω ↦ (prefixMap u (bridge ω) 1,centerMap (prefixMap u (bridge ω))))=
      (fun ω ↦ (bridge ω u,bridgePrefix u (bridge ω))) := by
    funext ω
    apply Prod.ext
    · simp only [prefixMap_apply]
      congr 1
      apply Subtype.ext
      simp [prefixTime]
    · rfl
  simp only [Function.comp_def,id_eq] at hi
  rw [he] at hi
  rw [bridgeLaw,Measure.map_map (by fun_prop) measurable_bridge]
  simp only [Function.comp_def]
  have hh := hi.map_prod_eq_prod_map_map
    ((((continuous_eval_const u).measurable.comp measurable_bridge).prodMk
      ((bridgePrefix u).continuous.measurable.comp measurable_bridge)).aemeasurable)
    (((bridgeRemainder u).continuous.measurable.comp measurable_bridge).aemeasurable)
  simp only [Function.comp_def] at hh
  rw [hh]
  have hp := (prefixValue_independent u).map_prod_eq_prod_map_map
    ((continuous_eval_const u).measurable.comp measurable_bridge).aemeasurable
    ((bridgePrefix u).continuous.measurable.comp measurable_bridge).aemeasurable
  simp only [Function.comp_def] at hp
  rw [hp,(bridge_eval_law u).map_eq,bridgePrefix_law,bridgeRemainder_law]
  rfl

end HardSphere.Wiener

end
end

end

end OAI
