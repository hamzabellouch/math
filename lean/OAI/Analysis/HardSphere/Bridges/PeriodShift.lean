import Mathlib
import OAI.Analysis.HardSphere.PathBounds.InteractingVisits
import OAI.Analysis.HardSphere.Bridges.ConfinedLift
import OAI.Analysis.HardSphere.Conditioning.ConditionTransport
import OAI.Analysis.HardSphere.Bridges.PairSubtype

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

def shiftPath (c : Point) (f : C(Time,Point)) : C(Time,Point) :=
  f+ContinuousMap.const _ c
@[fun_prop] lemma shiftPath_continuous (c : Point) : Continuous (shiftPath c) := by
  unfold shiftPath
  fun_prop

lemma shiftPath_cancel (c : Point) (f : C(Time,Point)) : shiftPath (-c) (shiftPath c f)=f := by
  ext s j
  change (f s j+c j)+(-c j)=f s j
  ring

lemma project_shift {L : Length} (c : Point) (hc : projectPoint L c=0) (f : C(Time,Point)) :
    projectCurve L (shiftPath c f)=projectCurve L f := by
  ext s i j
  change (((f s j+c j):ℝ):AddCircle L.val)=_
  rw [AddCircle.coe_add]
  have h := congrFun hc j
  change ((c j:ℝ):AddCircle L.val)=0 at h
  rw [h,add_zero]
  rfl

lemma projectPoint_shift {L : Length} (c : Point) (hc : projectPoint L c=0) (v : Point) :
    projectPoint L (v+c)=projectPoint L v := by
  ext j
  change (((v j+c j):ℝ):AddCircle L.val)=_
  rw [AddCircle.coe_add]
  have h := congrFun hc j
  change ((c j:ℝ):AddCircle L.val)=0 at h
  rw [h,add_zero]

lemma trialPath_shift (t : ℝ) (y z u c : Point) (β : Noise×Noise) :
    trialPath t (y+c) (z+c) (u+c) β=shiftPath c (trialPath t y z u β) := by
  ext s j
  change (leg t (y+c) (u+c) (pinned β.1) (leftTime s) j +
    leg t (z+c) (u+c) (pinned β.2) (reverseTime (rightTime s)) j)-(u j+c j)=_
  rw [leg_translate,leg_translate]
  change ((leg t y u (pinned β.1) (leftTime s) j+c j)+
    (leg t z u (pinned β.2) (reverseTime (rightTime s)) j+c j))-(u j+c j)=_
  change _=((leg t y u (pinned β.1) (leftTime s) j+
    leg t z u (pinned β.2) (reverseTime (rightTime s)) j)-u j)+c j
  ring

lemma trialKernel_shift (t : ℝ) (y z u c : Point) :
    (trialKernel t y z u).map (shiftPath c)=trialKernel t (y+c) (z+c) (u+c) := by
  have hm : Measurable (trialPath t y z u) :=
    ((trialPath_continuous t y z).comp (continuous_const.prodMk continuous_id)).measurable
  rw [trialKernel_apply,trialKernel_apply,Measure.map_map (shiftPath_continuous c).measurable hm]
  congr 1
  funext β
  exact (trialPath_shift t y z u c β).symm

lemma permittedPath_shift {J : Type*} {L : Length} (n : ℕ) (r R C S : ℝ)
    (w : Time) (y z v c : Point) (hc : projectPoint L c=0) (F : J → ConfigurationPath 1 L)
    (f : C(Time,Point)) :
    shiftPath c f∈permittedPath n r R C S w (y+c) (z+c) (v+c) F ↔
      f∈permittedPath n r R C S w y z v F := by
  simp only [permittedPath,mem_ofPred_eq,project_shift c hc]
  have hconf : TrialConfined L (v+c) (shiftPath c f) ↔ TrialConfined L v f := by
    simp only [TrialConfined,shiftPath,ContinuousMap.add_apply,ContinuousMap.const_apply,
      add_sub_add_right_eq_sub,projectPoint_shift c hc]
  rw [hconf]
  have hpin : shiftPath c f∈fixedEndpoints (y+c) (z+c) ↔ f∈fixedEndpoints y z := by
    simp only [fixedEndpoints,mem_ofPred_eq,shiftPath,ContinuousMap.add_apply,ContinuousMap.const_apply,
      add_left_inj]
  rw [hpin]
  have hp (s : Time) : projectPoint L (shiftPath c f s)=projectPoint L (f s) :=
    projectPoint_shift c hc (f s)
  simp only [TrialCollision,hp]

lemma individualReference_shift (t : ℝ) (y z c : Point)
    (S T : Set C(Time,Point)) (hT : MeasurableSet T)
    (hST : ∀f,shiftPath c f∈T ↔ f∈S) :
    (individualReference t y z S).map (shiftPath c)=
      individualReference t (y+c) (z+c) T := by
  have he : S=(shiftPath c)⁻¹' T := by ext f;exact (hST f).symm
  change (conditionedMeasure (law.map (leg (2*t) y z)) S).map (shiftPath c)=_
  rw [he,conditioned_map_preimage _ _ (shiftPath_continuous c).measurable hT,
    Measure.map_map (shiftPath_continuous c).measurable (leg_continuous ..).measurable]
  congr 1
  congr 1
  funext β
  exact (leg_translate (2*t) y z c β).symm

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma shiftPath_cancel' (c : Point) (f : C(Time,Point)) :
    shiftPath c (shiftPath (-c) f)=f := by simpa only [neg_neg] using shiftPath_cancel (-c) f

def shiftWithin (c : Point) (S T : Set C(Time,Point))
    (hST : ∀f,shiftPath c f∈T ↔ f∈S) : S ≃ᵐ T where
  toFun f := ⟨shiftPath c f, (hST f).mpr f.property⟩
  invFun f := ⟨shiftPath (-c) f, (hST _).mp (by rw [shiftPath_cancel'];exact f.property)⟩
  left_inv f := by apply Subtype.ext;exact shiftPath_cancel c f
  right_inv f := by apply Subtype.ext;exact shiftPath_cancel' c f
  measurable_toFun := ((shiftPath_continuous c).measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := ((shiftPath_continuous (-c)).measurable.comp measurable_subtype_coe).subtype_mk

lemma referenceOn_shift (t : ℝ) (y z c : Point) (S T : Set C(Time,Point))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : ∀f,shiftPath c f∈T ↔ f∈S) :
    (referenceOn t y z S).map (shiftWithin c S T hST)=referenceOn t (y+c) (z+c) T := by
  apply (MeasurableEmbedding.subtype_coe hT).map_injective
  rw [Measure.map_map measurable_subtype_coe (shiftWithin c S T hST).measurable,
    referenceOn_map t (y+c) (z+c) hT]
  change (referenceOn t y z S).map (shiftPath c ∘ Subtype.val)=_
  rw [←Measure.map_map (shiftPath_continuous c).measurable measurable_subtype_coe,referenceOn_map t y z hS]
  exact individualReference_shift t y z c S T hT hST

lemma referenceOn_unshift (t : ℝ) (y z c : Point) (S T : Set C(Time,Point))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : ∀f,shiftPath c f∈T ↔ f∈S) :
    (referenceOn t (y+c) (z+c) T).map (shiftWithin c S T hST).symm=referenceOn t y z S := by
  rw [←referenceOn_shift t y z c S T hS hT hST,
    Measure.map_map (shiftWithin c S T hST).symm.measurable (shiftWithin c S T hST).measurable]
  simp only [MeasurableEquiv.symm_comp_self,Measure.map_id]

def pairedAcrossPeriod (t : ℝ) (y z y' z' c : Point) (A : Set Point)
    (S T U : Set C(Time,Point)) (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hTU : ∀f,shiftPath c f∈U ↔ f∈T) : Measure (S×T) :=
  (pairedPathsOn t y z (y'+c) (z'+c) A S U hS hU).map
    (fun p ↦ (p.1,(shiftWithin c T U hTU).symm p.2))

lemma pairedAcrossPeriod_physical {L : Length} {t C C' : ℝ}
    (ht : 0<t) (hC : 0≤C) (hC' : 0≤C') (y z y' z' c : Point)
    (hperiod : projectPoint L c=0) {A : Set Point} (hA : MeasurableSet A)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hb : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (hb' : ∀u∈A,‖u-(fun j ↦ ((y'+c) j+(z'+c) j)/2)‖≤C')
    (S T U : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hTU : ∀f,shiftPath c f∈U ↔ f∈T)
    {a b : ℝ≥0∞} (ha0 : 0<a) (hb0 : 0<b)
    (ha : ∀ᵐu ∂targetUniform A,a≤trialKernel t y z u S)
    (hb : ∀ᵐu ∂targetUniform A,b≤trialKernel t (y'+c) (z'+c) u U) :
    IsProbabilityMeasure (pairedAcrossPeriod t y z y' z' c A S T U hS hU hTU) ∧
    (pairedAcrossPeriod t y z y' z' c A S T U hS hU hTU).fst≤
      (a⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) • referenceOn t y z S ∧
    (pairedAcrossPeriod t y z y' z' c A S T U hS hU hTU).snd≤
      (b⁻¹*((volume A)⁻¹*(midpointLower t C')⁻¹)) • referenceOn t y' z' T ∧
    (∀ᵐp ∂pairedAcrossPeriod t y z y' z' c A S T U hS hU hTU,
      projectPoint L (p.1.val midpointTime)=projectPoint L (p.2.val midpointTime)) := by
  obtain ⟨hP,hfst,hsnd,hmid⟩ := pairedPathsOn_physical ht hC hC' y z (y'+c) (z'+c)
    hA hA0 hAfinite ‹∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C› hb' S U hS hU ha0 hb0 ha hb
  let _ := hP
  have hm : Measurable (fun p : S×U ↦ (p.1,(shiftWithin c T U hTU).symm p.2)) :=
    measurable_fst.prodMk ((shiftWithin c T U hTU).symm.measurable.comp measurable_snd)
  have hf : (pairedAcrossPeriod t y z y' z' c A S T U hS hU hTU).fst=
      (pairedPathsOn t y z (y'+c) (z'+c) A S U hS hU).fst := by
    rw [pairedAcrossPeriod,Measure.fst,Measure.map_map measurable_fst hm]
    rfl
  have hs : (pairedAcrossPeriod t y z y' z' c A S T U hS hU hTU).snd=
      (pairedPathsOn t y z (y'+c) (z'+c) A S U hS hU).snd.map (shiftWithin c T U hTU).symm := by
    rw [pairedAcrossPeriod,Measure.snd,Measure.map_map measurable_snd hm,
      Measure.snd,Measure.map_map (shiftWithin c T U hTU).symm.measurable measurable_snd]
    rfl
  refine ⟨by unfold pairedAcrossPeriod; infer_instance,?_,?_,?_⟩
  · rw [hf];exact hfst
  · rw [hs]
    have H := Measure.map_mono hsnd (shiftWithin c T U hTU).symm.measurable
    rw [Measure.map_smul _ (shiftWithin c T U hTU).symm.measurable.aemeasurable,
      referenceOn_unshift t y' z' c T U hT hU hTU] at H
    exact H
  · apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
    filter_upwards [hmid] with p hp
    change projectPoint L (p.1.val midpointTime)=projectPoint L ((shiftPath (-c) p.2.val) midpointTime)
    have hc : projectPoint L (-c)=0 := by
      ext j
      change (((-c j):ℝ):AddCircle L.val)=0
      rw [AddCircle.coe_neg]
      have h := congrFun hperiod j
      change ((c j:ℝ):AddCircle L.val)=0 at h
      rw [h,neg_zero]
    rw [hp]
    exact (projectPoint_shift (-c) hc (p.2.val midpointTime)).symm

lemma pairedAcrossPeriod_auxiliary {L : Length} {t C C' : ℝ}
    (ht : 0<t) (hC : 0≤C) (hC' : 0≤C') (y z y' z' c : Point)
    (hperiod : projectPoint L c=0) {A : Set Point} (hA : MeasurableSet A)
    (hA0 : volume A≠0) (hAfinite : volume A≠⊤)
    (hbound : ∀u∈A,‖u-(fun j ↦ (y j+z j)/2)‖≤C)
    (hbound' : ∀u∈A,‖u-(fun j ↦ ((y'+c) j+(z'+c) j)/2)‖≤C')
    (S T U : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) (hU : MeasurableSet U)
    (hTU : ∀f,shiftPath c f∈U ↔ f∈T)
    {a b : ℝ≥0∞} (ha0 : 0<a) (hb0 : 0<b)
    (ha : ∀ᵐu ∂targetUniform A,a≤trialKernel t y z u S)
    (hb : ∀ᵐu ∂targetUniform A,b≤trialKernel t (y'+c) (z'+c) u U) :
    ∃κ : Kernel S T,IsFiniteKernel κ ∧
      (referenceOn t y z S).compProd κ=pairedAcrossPeriod t y z y' z' c A S T U hS hU hTU ∧
      (∀f,κ f univ≤a⁻¹*((volume A)⁻¹*(midpointLower t C)⁻¹)) ∧
      (∫⁻f,κ f univ ∂referenceOn t y z S)=1 := by
  let _ : IsProbabilityMeasure (referenceOn t y z S) :=
    referenceOn_probability ht hC y z hA hA0 hAfinite hbound S hS ha0 ha
  let _ : IsProbabilityMeasure (referenceOn t (y'+c) (z'+c) U) :=
    referenceOn_probability ht hC' (y'+c) (z'+c) hA hA0 hAfinite hbound' U hU hb0 hb
  have htprob : IsProbabilityMeasure (referenceOn t y' z' T) := by
    rw [←referenceOn_unshift t y' z' c T U hT hU hTU]
    infer_instance
  let _ := htprob
  let _ : StandardBorelSpace T := hT.standardBorel
  let _ : Nonempty T := nonempty_of_isProbabilityMeasure (referenceOn t y' z' T)
  obtain ⟨hp,hfst,hsnd,hm⟩ := pairedAcrossPeriod_physical ht hC hC' y z y' z' c hperiod
    hA hA0 hAfinite hbound hbound' S T U hS hT hU hTU ha0 hb0 ha hb
  let _ := hp
  exact exists_bounded_auxiliary_kernel _ _
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ha0.ne')
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr (midpointLower_pos ht C).ne'))) hfst

end HardSphere.Bridge

end
end

end

end OAI
