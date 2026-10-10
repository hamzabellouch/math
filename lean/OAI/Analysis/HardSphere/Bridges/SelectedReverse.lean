import Mathlib
import OAI.Analysis.HardSphere.Bridges.ReversePair

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

abbrev selectedPerm (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i) : Equiv.Perm s where
  toFun i := ⟨σ i,(move_mem_iff σ s hf i).mpr i.property⟩
  invFun j := ⟨σ.symm j,by
    have h : σ (σ.symm j)∈s := by simp
    exact (move_mem_iff σ s hf _).mp h⟩
  left_inv i := Subtype.ext (σ.symm_apply_apply i)
  right_inv j := Subtype.ext (σ.apply_symm_apply j)

def reverseSelected (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i) :
    (∀i:s,X i×X (σ.symm i)) ≃ᵐ (∀j:s,X j×X (σ j)) :=
  (MeasurableEquiv.piCongrLeft (fun i:s ↦ X i×X (σ.symm i)) (selectedPerm σ s hf)).symm.trans
    (MeasurableEquiv.piCongrRight (fun j:s ↦ reverseFactor (X:=X) σ j))

omit [Fintype I] in
lemma reverseSelected_apply (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (p : ∀i:s,X i×X (σ.symm i)) (j : s) :
    reverseSelected σ s hf p j=
      (fiberEquiv (σ.symm_apply_apply j) (p (selectedPerm σ s hf j)).2,
        (p (selectedPerm σ s hf j)).1) := rfl

omit [Fintype I] in
lemma reverseSelected_product (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (μ : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (Measure.pi μ).map (reverseSelected σ s hf)=
      Measure.pi (fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j)) := by
  let e := MeasurableEquiv.piCongrLeft (fun i:s ↦ X i×X (σ.symm i)) (selectedPerm σ s hf)
  have h₁ : MeasurePreserving e.symm (Measure.pi μ)
      (Measure.pi fun j:s ↦ μ (selectedPerm σ s hf j)) :=
    MeasurePreserving.symm e (measurePreserving_piCongrLeft μ (selectedPerm σ s hf))
  have : ∀j:s, IsFiniteMeasure ((μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j)) := by
    intro j
    let : IsFiniteMeasure (μ (selectedPerm σ s hf j)) := (inferInstance : ∀i,IsFiniteMeasure (μ i)) _
    constructor
    rw [Measure.map_apply (reverseFactor (X:=X) σ j).measurable MeasurableSet.univ]
    simpa only [Set.preimage_univ] using (measure_lt_top (μ (selectedPerm σ s hf j)) Set.univ)
  have h₂ : MeasurePreserving (MeasurableEquiv.piCongrRight (fun j:s ↦ reverseFactor (X:=X) σ j))
      (Measure.pi fun j:s ↦ μ (selectedPerm σ s hf j))
      (Measure.pi fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j)) :=
    measurePreserving_pi (fun j:s ↦ μ (selectedPerm σ s hf j))
      (fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j))
      (fun j : s ↦ ⟨(reverseFactor (X:=X) σ j).measurable,rfl⟩)
  exact (h₂.comp h₁).map_eq

omit [Fintype I] in
lemma partialReverse_update (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (b : ∀i,X i×X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    partialReversePairs σ s hf (Function.updateFinset b s p)=
      Function.updateFinset (partialReversePairs σ s hf b) s (reverseSelected σ s hf p) := by
  funext j
  by_cases hj : j∈s
  · rw [partialReversePairs_selected σ s hf _ j hj]
    have hj' : σ j∈s := (move_mem_iff σ s hf j).mpr hj
    simp only [Function.updateFinset,dite_eq_left hj,dite_eq_left hj']
    rfl
  · have hj' : σ j∉s := fun h ↦ hj ((move_mem_iff σ s hf j).mp h)
    simp only [Function.updateFinset,dite_eq_right hj]
    change partialReverseFactor σ s hf j (Function.updateFinset b s p (σ j))=_
    simp only [Function.updateFinset,dite_eq_right hj']
    rfl

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma selected_physical_conditioned_reverse {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (b : ∀i,X i×X (σ.symm i))
    (μ : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (conditionedMeasure (Measure.pi μ) {p | Function.updateFinset b s p∈
      retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ}).map
      (reverseSelected σ s hf)=
    conditionedMeasure (Measure.pi fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j))
      {p | Function.updateFinset (partialReversePairs σ s hf b) s p∈
        retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ} := by
  let A : Set (∀j:s,X j×X (σ j)) := {p | Function.updateFinset (partialReversePairs σ s hf b) s p∈
        retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ}
  have hA : MeasurableSet A := (measurableSet_retainedEvent _ _).preimage
    measurable_updateFinset
  have he : (reverseSelected σ s hf)⁻¹' A={p | Function.updateFinset b s p∈
      retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ} := by
    ext p
    simp only [Set.mem_preimage,A,Set.mem_ofPred_eq]
    rw [←partialReverse_update σ s hf b p]
    exact Set.ext_iff.mp (partialReverse_checks σ s hf r anchor allowed label get hg)
      (Function.updateFinset b s p)
  rw [←he,conditioned_map_preimage _ _ (reverseSelected σ s hf).measurable hA,
    reverseSelected_product]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routePath_update_base (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (allowed : J→Set C(Time,Point)) (label : J→I) (get : ∀j,X (label j)→allowed j)
    (b b' : ∀i,X i×X (σ.symm i)) (he : ∀i,i∉s→(b i).1=(b' i).1)
    (p : ∀i:s,X i×X (σ.symm i)) (c : Bool) (j : J) :
    routePath σ s hf allowed label get c j (Function.updateFinset b s p (routeOwner σ label c j))=
    routePath σ s hf allowed label get c j (Function.updateFinset b' s p (routeOwner σ label c j)) := by
  cases c
  · change get j (Function.updateFinset b s p (label j)).1=get j (Function.updateFinset b' s p (label j)).1
    by_cases hj : label j∈s
    · simp only [Function.updateFinset,dite_eq_left hj]
    · simpa only [Function.updateFinset,dite_eq_right hj] using congrArg (get j) (he _ hj)
  · by_cases hj : label j∈s
    · have hh : σ (label j)∈s := (move_mem_iff σ s hf _).mpr hj
      change routePath σ s hf allowed label get true j (Function.updateFinset b s p (σ (label j))) =
        routePath σ s hf allowed label get true j (Function.updateFinset b' s p (σ (label j)))
      simp only [Function.updateFinset,dite_eq_left hh]
    · rw [routePath_unselected σ s hf allowed label get j hj,
        routePath_unselected σ s hf allowed label get j hj]
      simpa only [Function.updateFinset,dite_eq_right hj] using congrArg (get j) (he _ hj)

omit [Fintype J] [DecidableEq J] in
lemma route_fill_event_congr {L : Length} (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (b b' : ∀i,X i×X (σ.symm i)) (he : ∀i,i∉s→(b i).1=(b' i).1) :
    {p | Function.updateFinset b s p∈retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ}=
    {p | Function.updateFinset b' s p∈retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ} := by
  ext p
  change (∀e, _ → _) ↔ (∀e, _ → _)
  apply forall_congr'
  intro e
  apply imp_congr_right
  intro _he'
  change (¬TrialCollision r
    (projectCurve L (routePath σ s hf allowed label get e.1 e.2.val.2
      (Function.updateFinset b s p (routeOwner σ label e.1 e.2.val.2))).val)
    (routePath σ s hf allowed label get e.1 e.2.val.1
      (Function.updateFinset b s p (routeOwner σ label e.1 e.2.val.1))).val) ↔ _
  rw [routePath_update_base σ s hf allowed label get b b' he,
    routePath_update_base σ s hf allowed label get b b' he]
  rfl

lemma selected_reverse_same_outside {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i))
    (μ : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (conditionedMeasure (Measure.pi μ) {p | Function.updateFinset (fun i ↦ (x i,z i)) s p∈
      retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ}).map
      (reverseSelected σ s hf)=
    conditionedMeasure (Measure.pi fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j))
      {p | Function.updateFinset (fun i ↦ (x i,w i)) s p∈
        retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ} := by
  rw [selected_physical_conditioned_reverse σ s hf r anchor allowed label get hg]
  congr 1
  apply route_fill_event_congr σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg
  intro i hi
  exact partialReversePairs_outside_fst σ s hf (fun i ↦ (x i,z i)) i hi

end HardSphere.Bridge

end
end

end

end OAI
