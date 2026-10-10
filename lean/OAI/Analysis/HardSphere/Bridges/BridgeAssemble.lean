import Mathlib
import OAI.Analysis.HardSphere.Bridges.GaussianMixture
import OAI.Analysis.HardSphere.Bridges.BridgeSplit

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener
open Bridge (leftTime rightTime midpointTime leftTime_continuous rightTime_continuous)

def assembleBridge (p : (ℝ×C(Time,ℝ))×C(Time,ℝ)) : C(Time,ℝ) :=
  ⟨fun s ↦ ((leftTime s:ℝ)-(rightTime s:ℝ))*p.1.1+
    p.1.2 (leftTime s)+p.2 (rightTime s),by
    have hl := leftTime_continuous
    have hr := rightTime_continuous
    fun_prop⟩

lemma assembleBridge_continuous : Continuous assembleBridge := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ((ℝ×C(Time,ℝ))×C(Time,ℝ))×Time ↦
    ((leftTime p.2:ℝ)-(rightTime p.2:ℝ))*p.1.1.1+
      p.1.1.2 (leftTime p.2)+p.1.2 (rightTime p.2))
  have hl := leftTime_continuous
  have hr := rightTime_continuous
  fun_prop

lemma assembleBridge_split (β : C(Time,ℝ)) (h0 : β 0=0) (h1 : β 1=0) :
    assembleBridge ((β midpointTime,bridgePrefix midpointTime β),bridgeRemainder midpointTime β)=β := by
  ext s
  simp only [assembleBridge,ContinuousMap.coe_mk,bridgePrefix_apply,bridgeRemainder_apply]
  by_cases hs0 : s=0
  · subst s
    simp [leftTime,rightTime,prefixTime,suffixTime,h0]
  by_cases hs1 : s=1
  · subst s
    norm_num [leftTime,rightTime,prefixTime,suffixTime,midpointTime,h1]
  by_cases hs : (s:ℝ)≤1/2
  · have hr : rightTime s=0 := by apply Subtype.ext; simp only [rightTime]; exact max_eq_right (by linarith)
    have hl : (leftTime s:ℝ)=2*(s:ℝ) := min_eq_left (by linarith)
    have hp : prefixTime midpointTime (leftTime s)=s := by apply Subtype.ext; change (1/2:ℝ)*(leftTime s:ℝ)=(s:ℝ); rw [hl]; ring
    have he : suffixTime midpointTime (0:Time)=midpointTime := by apply Subtype.ext; simp [suffixTime]
    rw [hr,hp,he]
    change _+_+(β midpointTime-(1-(0:ℝ))*β midpointTime)=_
    simp only [show ((0:Time):ℝ)=0 from rfl]
    ring
  · have hl : leftTime s=1 := by apply Subtype.ext; simp only [leftTime]; exact min_eq_right (by linarith)
    have hr : (rightTime s:ℝ)=2*(s:ℝ)-1 := max_eq_left (by linarith)
    have hp : prefixTime midpointTime (1:Time)=midpointTime := by apply Subtype.ext; simp [prefixTime]
    have he : suffixTime midpointTime (rightTime s)=s := by
      apply Subtype.ext
      change (1/2:ℝ)+(1-1/2)*(rightTime s:ℝ)=(s:ℝ)
      rw [hr]
      ring
    rw [hl,hp,he]
    change ((1:ℝ)-(rightTime s:ℝ))*β midpointTime+(β midpointTime-1*β midpointTime)+_= _
    ring

lemma bridge_midpoint_disintegration :
    (((gaussianReal 0 (Real.toNNReal (1/4:ℝ))).prod
      (bridgeLaw.map (fun β ↦ Real.sqrt (1/2:ℝ) • β))).prod
      (bridgeLaw.map (fun β ↦ Real.sqrt (1/2:ℝ) • β))).map assembleBridge=bridgeLaw := by
  have he := bridge_three_law midpointTime
  norm_num [midpointTime] at he
  norm_num only [Real.sqrt_div,Real.sqrt_one,one_div]
  rw [←he,Measure.map_map assembleBridge_continuous.measurable (by fun_prop)]
  have ha : assembleBridge ∘ (fun β ↦ ((β midpointTime,bridgePrefix midpointTime β),bridgeRemainder midpointTime β))=ᵐ[bridgeLaw] id := by
    filter_upwards [HardSphere.bridge_endpoints] with β hβ
    exact assembleBridge_split β hβ.1 hβ.2
  change bridgeLaw.map (assembleBridge ∘ (fun β ↦ ((β midpointTime,bridgePrefix midpointTime β),bridgeRemainder midpointTime β)))=bridgeLaw
  rw [Measure.map_congr ha,Measure.map_id]

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def bridgeReverse : C(Time,ℝ) →L[ℝ] C(Time,ℝ) := ContinuousMap.compCLM ℝ ℝ reverseTime

lemma center_reverse (ω : Noise) :
    centerMap (reverseIncrements (path ω))=bridgeReverse (bridge ω) := by
  ext s
  simp only [centerMap_apply,reverseIncrements_apply,bridgeReverse,ContinuousMap.compCLM_apply,
    ContinuousMap.comp_apply,bridge_apply]
  have hr : reverseTime 1=0 := by ext; norm_num [reverseTime]
  rw [hr,path_at_zero]
  change path ω (reverseTime s)-path ω 1-(s:ℝ)*(0-path ω 1)=
    path ω (reverseTime s)-(1-(s:ℝ))*path ω 1
  ring

lemma bridgeReverse_preserving : MeasurePreserving bridgeReverse bridgeLaw bridgeLaw := by
  refine ⟨bridgeReverse.continuous.measurable,?_⟩
  have hm := congrArg (fun μ : Measure C(Time,ℝ) ↦ μ.map centerMap) reverseIncrements_law
  rw [Measure.map_map (f:=fun ω ↦ reverseIncrements (path ω)) centerMap.continuous.measurable
    (reverseIncrements.continuous.measurable.comp measurable_path),←bridgeLaw_center] at hm
  rw [bridgeLaw,Measure.map_map bridgeReverse.continuous.measurable measurable_bridge]
  convert hm using 1
  · congr 1
    funext ω
    exact (center_reverse ω).symm
  · rfl

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

def midpointNoise : Measure Point := Measure.pi (fun _ : Fin 3 ↦ gaussianReal 0 (Real.toNNReal (1/4:ℝ)))
instance : IsProbabilityMeasure midpointNoise := by unfold midpointNoise; infer_instance

def assembleNoise (p : (Point×Noise)×Noise) : Noise := fun j ↦ assembleBridge
  ((p.1.1 j,Real.sqrt (1/2:ℝ) • p.1.2 j),Real.sqrt (1/2:ℝ) • p.2 j)
lemma assembleNoise_continuous : Continuous assembleNoise := by
  apply continuous_pi
  intro j
  exact assembleBridge_continuous.comp (by fun_prop)

lemma scalar_assemble_law :
    (((gaussianReal 0 (Real.toNNReal (1/4:ℝ))).prod bridgeLaw).prod bridgeLaw).map
      (fun p ↦ assembleBridge ((p.1.1,Real.sqrt (1/2:ℝ) • p.1.2),Real.sqrt (1/2:ℝ) • p.2))=bridgeLaw := by
  have hs : MeasurePreserving (fun β : C(Time,ℝ) ↦ Real.sqrt (1/2:ℝ) • β) bridgeLaw
      (bridgeLaw.map (fun β ↦ Real.sqrt (1/2:ℝ) • β)) := ⟨by fun_prop,rfl⟩
  have hp := ((MeasurePreserving.id (gaussianReal 0 (Real.toNNReal (1/4:ℝ)))).prod hs).prod hs
  have hm := congrArg (fun μ : Measure ((ℝ×C(Time,ℝ))×C(Time,ℝ)) ↦ μ.map assembleBridge) hp.map_eq
  rw [Measure.map_map assembleBridge_continuous.measurable hp.measurable] at hm
  exact hm.trans bridge_midpoint_disintegration

lemma assembleNoise_preserving :
    MeasurePreserving assembleNoise ((midpointNoise.prod law).prod law) law := by
  refine ⟨assembleNoise_continuous.measurable,?_⟩
  let g : Measure ℝ := gaussianReal 0 (Real.toNNReal (1/4:ℝ))
  let b := bridgeLaw
  have h₁ := measurePreserving_arrowProdEquivProdArrow ℝ C(Time,ℝ) (Fin 3) (fun _ ↦ g) (fun _ ↦ b)
  have h₂ := measurePreserving_arrowProdEquivProdArrow (ℝ×C(Time,ℝ)) C(Time,ℝ) (Fin 3)
    (fun _ ↦ g.prod b) (fun _ ↦ b)
  have ht := (h₁.prod (MeasurePreserving.id (Measure.pi (fun _ : Fin 3 ↦ b)))).comp h₂
  change (((Measure.pi (fun _ : Fin 3 ↦ g)).prod (Measure.pi (fun _ : Fin 3 ↦ b))).prod
    (Measure.pi (fun _ : Fin 3 ↦ b))).map assembleNoise=Measure.pi (fun _ : Fin 3 ↦ b)
  rw [←ht.map_eq,Measure.map_map assembleNoise_continuous.measurable ht.measurable]
  change (Measure.pi (fun _ : Fin 3 ↦ (g.prod b).prod b)).map
    (fun p j ↦ assembleBridge (((p j).1.1,Real.sqrt (1/2:ℝ) • (p j).1.2),Real.sqrt (1/2:ℝ) • (p j).2))=_
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun p : (ℝ×C(Time,ℝ))×C(Time,ℝ) ↦
    assembleBridge ((p.1.1,Real.sqrt (1/2:ℝ) • p.1.2),Real.sqrt (1/2:ℝ) • p.2)) from
      assembleBridge_continuous.measurable.comp (by fun_prop)).aemeasurable)]
  simp_rw [show (g.prod b).prod b=(((gaussianReal 0 (Real.toNNReal (1/4:ℝ))).prod bridgeLaw).prod bridgeLaw) from rfl,
    scalar_assemble_law]
  rfl

def reverseNoise (β : Noise) : Noise := fun j ↦ bridgeReverse (β j)
lemma reverseNoise_continuous : Continuous reverseNoise := by unfold reverseNoise; fun_prop
lemma reverseNoise_preserving : MeasurePreserving reverseNoise law law := by
  refine ⟨reverseNoise_continuous.measurable,?_⟩
  unfold law reverseNoise
  rw [Measure.pi_map_pi (fun _ ↦ bridgeReverse.continuous.measurable.aemeasurable)]
  simp_rw [bridgeReverse_preserving.map_eq]

lemma left_add_right (s : Time) : (leftTime s:ℝ)+(rightTime s:ℝ)=2*(s:ℝ) := by
  change min (2*(s:ℝ)) 1+max (2*(s:ℝ)-1) 0=_
  by_cases h : 2*(s:ℝ)≤1
  · rw [min_eq_left h,max_eq_right (by linarith)]; ring
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (by linarith)]; ring

def midpointPoint (t : ℝ) (y z v : Point) : Point := fun j ↦ (y j+z j)/2+Real.sqrt (4*t)*v j

lemma trial_assemble (t : ℝ) (ht : 0≤t) (y z v : Point) (β γ : Noise) :
    trialPath t y z (midpointPoint t y z v) (β,γ)=
      leg (2*t) y z (assembleNoise ((v,pinned β),reverseNoise (pinned γ))) := by
  ext s j
  simp only [trialPath,leg,ContinuousMap.coe_mk,mean,Pi.add_apply,Pi.sub_apply,
    assembleNoise,assembleBridge,ContinuousMap.smul_apply,smul_eq_mul,reverseNoise,
    bridgeReverse,ContinuousMap.compCLM_apply,ContinuousMap.comp_apply,midpointPoint]
  have hs := left_add_right s
  have hr : (reverseTime (rightTime s):ℝ)=1-(rightTime s:ℝ) := rfl
  have hmul : Real.sqrt (4*t)*Real.sqrt (1/2:ℝ)=Real.sqrt (2*t) := by
    rw [←Real.sqrt_mul (by positivity)]
    congr 1
    ring
  rw [show 2*(2*t)=4*t by ring,hr]
  rw [←hmul]
  have hs' : (s:ℝ)=((leftTime s:ℝ)+(rightTime s:ℝ))/2 := by linarith
  rw [hs']
  ring

end HardSphere.Bridge

end
end

end

end OAI
