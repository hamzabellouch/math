import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalSparse
import OAI.Analysis.HardSphere.Conditioning.ReferenceResample
import OAI.Analysis.HardSphere.Conditioning.ExtraReference

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]
omit [Fintype I] [Fintype C] in
lemma retainedEvent_ignore (checks : C→LocalCheck X) (j : I)
    (hj : ∀c,j∉(checks c).support) (s : Finset I) (x : ∀i,X i) (y : X j) :
    Function.update x j y∈retainedEvent checks s ↔ x∈retainedEvent checks s := by
  have he (c : C) : (checks c).pass (Function.update x j y) ↔ (checks c).pass x := by
    apply (checks c).depends
    intro i hi
    exact Function.update_of_ne (show i≠j from fun h ↦ hj c (h ▸ hi)) y x
  simp only [retainedEvent,Set.mem_ofPred_eq,he]
end HardSphere.Comparison
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I→Type*} [∀i,MeasurableSpace (X i)]
omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma primaryChecks_ignore_star (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (s : Finset I) (x : ∀i,X i) (y : X star) :
    Function.update x star y∈retainedEvent (primaryChecks r anchor allowed label get hg) s ↔
      x∈retainedEvent (primaryChecks r anchor allowed label get hg) s := by
  apply retainedEvent_ignore
  intro c
  simp only [primaryChecks,physicalSparseChecks,factorPathCheck,dependentCheck,
    Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨(hstar _).symm,(hstar _).symm⟩

lemma primary_outside_reference_equal
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (s : Finset I) (hs : star∈s)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (he : ∀i,i≠star→μ i=ν i) :
    (conditionedMeasure (Measure.pi μ) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ)).map
      (fun x : ∀i,X i ↦ fun i : {i // i∉s} ↦ x i)=
    (conditionedMeasure (Measure.pi ν) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ)).map
      (fun x : ∀i,X i ↦ fun i : {i // i∉s} ↦ x i) := by
  apply conditioned_map_ignore μ ν star he _ (measurableSet_retainedEvent _ _)
    (primaryChecks_ignore_star r anchor allowed label get hg star hstar Finset.univ)
    _ (by fun_prop)
  intro x y
  funext i
  exact Function.update_of_ne (show (i:I)≠star from fun h ↦ i.property (h.symm ▸ hs)) y x

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma conditioned_kernel_ignore {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (j : I) (he : ∀i,i≠j→μ i=ν i)
    (A : Set (∀i,X i)) (hA : MeasurableSet A) (hAi : ∀x y,Function.update x j y∈A↔x∈A)
    (κ : Kernel (∀i,X i) Y) [IsSFiniteKernel κ]
    (hi : ∀x y,κ (Function.update x j y)=κ x)
    (f : (∀i,X i)×Y→Z) (hf : Measurable f)
    (hfi : ∀x y p,f (Function.update x j y,p)=f (x,p)) :
    ((conditionedMeasure (Measure.pi μ) A).compProd κ).map f=
      ((conditionedMeasure (Measure.pi ν) A).compProd κ).map f := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf,lintegral_map hF hf]
  change (∫⁻a,(F∘f) a ∂(conditionedMeasure (Measure.pi μ) A).compProd κ)=
    ∫⁻a,(F∘f) a ∂(conditionedMeasure (Measure.pi ν) A).compProd κ
  rw [Measure.lintegral_compProd (hF.comp hf),Measure.lintegral_compProd (hF.comp hf)]
  apply conditioned_lintegral_ignore μ ν j he A hA hAi _
    (hF.comp hf).lintegral_kernel_prod_right'
  intro x y
  rw [hi]
  apply lintegral_congr
  intro p
  exact congrArg F (hfi x y p)

variable {C : Type*} [Fintype C] {Z : I→Type*} [∀i,MeasurableSpace (Z i)]
omit [Fintype I] in
lemma proposalKernel_ignore_selected (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) (j : I) (hj : j∈s) (x : ∀i,X i) (y : X j) :
    proposalKernel checks μ κ s o z (Function.update x j y)=proposalKernel checks μ κ s o z x := by
  rw [proposalKernel_apply,proposalKernel_apply]
  unfold proposalFiber
  congr 1
  ext p
  suffices hh : Function.updateFinset (fun i ↦ (Function.update x j y i,z i)) s p=
      Function.updateFinset (fun i ↦ (x i,z i)) s p by
    change _∈retainedEvent checks (s∪o) ↔ _∈retainedEvent checks (s∪o)
    rw [hh]
  funext i
  by_cases his : i∈s
  · simp [Function.updateFinset,his]
  · simp only [Function.updateFinset,dite_eq_right his]
    rw [Function.update_of_ne (show i≠j from fun h ↦ his (h.symm ▸ hj))]

end HardSphere.Comparison

end
end

end

end OAI
