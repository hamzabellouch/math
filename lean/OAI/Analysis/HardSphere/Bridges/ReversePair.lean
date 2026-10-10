import Mathlib
import OAI.Analysis.HardSphere.Bridges.PhysicalSparse
import OAI.Analysis.HardSphere.Conditioning.ConditionTransport

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

def reverseFactor (σ : Equiv.Perm I) (j : I) :
    (X (σ j)×X (σ.symm (σ j))) ≃ᵐ (X j×X (σ j)) :=
  ((MeasurableEquiv.refl _).prodCongr (fiberEquiv (σ.symm_apply_apply j))).trans
    (MeasurableEquiv.prodComm)

def reversePairs (σ : Equiv.Perm I) :
    (∀i,X i×X (σ.symm i)) ≃ᵐ (∀j,X j×X (σ j)) :=
  (MeasurableEquiv.piCongrLeft (fun i ↦ X i×X (σ.symm i)) σ).symm.trans
    (MeasurableEquiv.piCongrRight (reverseFactor σ))

omit [Fintype I] [DecidableEq I] in
@[simp] lemma reversePairs_apply (σ : Equiv.Perm I) (p : ∀i,X i×X (σ.symm i)) (j : I) :
    reversePairs σ p j=
      (fiberEquiv (σ.symm_apply_apply j) (p (σ j)).2,(p (σ j)).1) := rfl

omit [DecidableEq I] in
lemma reversePairs_product (σ : Equiv.Perm I)
    (μ : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (Measure.pi μ).map (reversePairs σ)=
      Measure.pi (fun j ↦ (μ (σ j)).map (reverseFactor σ j)) := by
  let e := MeasurableEquiv.piCongrLeft (fun i ↦ X i×X (σ.symm i)) σ
  have h₁ : MeasurePreserving e.symm (Measure.pi μ) (Measure.pi fun j ↦ μ (σ j)) :=
    MeasurePreserving.symm e (measurePreserving_piCongrLeft μ σ)
  have h₂ : MeasurePreserving (MeasurableEquiv.piCongrRight (reverseFactor σ))
      (Measure.pi fun j ↦ μ (σ j))
      (Measure.pi fun j ↦ (μ (σ j)).map (reverseFactor σ j)) :=
    measurePreserving_pi _ _ (fun j ↦ ⟨(reverseFactor σ j).measurable,rfl⟩)
  exact (h₂.comp h₁).map_eq

omit [DecidableEq I] in
lemma reversePairs_conditioned (σ : Equiv.Perm I)
    (μ : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)]
    {S : Set (∀j,X j×X (σ j))} (hS : MeasurableSet S) :
    (conditionedMeasure (Measure.pi μ) ((reversePairs σ)⁻¹' S)).map (reversePairs σ)=
      conditionedMeasure (Measure.pi fun j ↦ (μ (σ j)).map (reverseFactor σ j)) S := by
  rw [conditioned_map_preimage _ _ (reversePairs σ).measurable hS,reversePairs_product]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_trans {i j k : I} (h : i=j) (h' : j=k) (v : X i) :
    fiberEquiv h' (fiberEquiv h v)=fiberEquiv (h.trans h') v := by
  subst j; subst k; rfl

omit [Fintype I] [DecidableEq I] in
lemma reverse_fix (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i) :
    ∀i,i∉s→σ.symm i=i := by
  intro i hi
  apply σ.injective
  rw [σ.apply_symm_apply,hf i hi]

def partialReverseFactor (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (j : I) :
    (X (σ j)×X (σ.symm (σ j))) ≃ᵐ (X j×X (σ j)) :=
  if hj : j∈s then reverseFactor σ j else
    (fiberEquiv (hf j hj)).prodCongr
      (fiberEquiv ((σ.symm_apply_apply j).trans (hf j hj).symm))

def partialReversePairs (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) :
    (∀i,X i×X (σ.symm i)) ≃ᵐ (∀j,X j×X (σ j)) :=
  (MeasurableEquiv.piCongrLeft (fun i ↦ X i×X (σ.symm i)) σ).symm.trans
    (MeasurableEquiv.piCongrRight (partialReverseFactor σ s hf))

omit [Fintype I] in
lemma partialReversePairs_selected (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (p : ∀i,X i×X (σ.symm i)) (j : I) (hj : j∈s) :
    partialReversePairs σ s hf p j=
      (fiberEquiv (σ.symm_apply_apply j) (p (σ j)).2,(p (σ j)).1) := by
  change partialReverseFactor σ s hf j (p (σ j))=_
  simp only [partialReverseFactor,dite_eq_left hj,reverseFactor]
  rfl
omit [Fintype I] in
lemma partialReversePairs_outside_fst (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (p : ∀i,X i×X (σ.symm i)) (j : I) (hj : j∉s) :
    (partialReversePairs σ s hf p j).1=(p j).1 := by
  change (partialReverseFactor σ s hf j (p (σ j))).1=_
  simp only [partialReverseFactor,dite_eq_right hj]
  change fiberEquiv (hf j hj) (p (σ j)).1=(p j).1
  exact fiberEquiv_pi (hf j hj) (fun i ↦ (p i).1)

lemma partialReversePairs_product (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i)
    (μ : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (Measure.pi μ).map (partialReversePairs σ s hf)=
      Measure.pi (fun j ↦ (μ (σ j)).map (partialReverseFactor σ s hf j)) := by
  let e := MeasurableEquiv.piCongrLeft (fun i ↦ X i×X (σ.symm i)) σ
  have h₁ : MeasurePreserving e.symm (Measure.pi μ) (Measure.pi fun j ↦ μ (σ j)) :=
    MeasurePreserving.symm e (measurePreserving_piCongrLeft μ σ)
  have h₂ : MeasurePreserving (MeasurableEquiv.piCongrRight (partialReverseFactor σ s hf))
      (Measure.pi fun j ↦ μ (σ j))
      (Measure.pi fun j ↦ (μ (σ j)).map (partialReverseFactor σ s hf j)) :=
    measurePreserving_pi _ _ (fun j ↦ ⟨(partialReverseFactor σ s hf j).measurable,rfl⟩)
  exact (h₂.comp h₁).map_eq

lemma partialReversePairs_conditioned (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i)
    (μ : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)]
    {A : Set (∀j,X j×X (σ j))} (hA : MeasurableSet A) :
    (conditionedMeasure (Measure.pi μ) ((partialReversePairs σ s hf)⁻¹' A)).map
      (partialReversePairs σ s hf)=
    conditionedMeasure (Measure.pi fun j ↦ (μ (σ j)).map (partialReverseFactor σ s hf j)) A := by
  rw [conditioned_map_preimage _ _ (partialReversePairs σ s hf).measurable hA,
    partialReversePairs_product]

variable {J : Type*} [Fintype J] [DecidableEq J]
omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma partialReverse_primary_path (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j)
    (p : ∀i,X i×X (σ.symm i)) (j : J) :
    get j (partialReversePairs σ s hf p (label j)).1=
      routePath σ s hf allowed label get true j (p (routeOwner σ label true j)) := by
  by_cases hj : label j∈s
  · rw [partialReversePairs_selected σ s hf p _ hj]
    simp only [routePath,dite_eq_left hj]
    rfl
  · rw [partialReversePairs_outside_fst σ s hf p _ hj,
      routePath_unselected σ s hf allowed label get j hj]

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma partialReverse_secondary_path (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j)
    (p : ∀i,X i×X (σ.symm i)) (j : J) :
    routePath σ.symm s (reverse_fix σ s hf) allowed label get true j
      (partialReversePairs σ s hf p (routeOwner σ.symm label true j))=get j (p (label j)).1 := by
  by_cases hj : label j∈s
  · have hj' : σ.symm (label j)∈s :=
      (move_mem_iff σ.symm s (reverse_fix σ s hf) _).mpr hj
    simp only [routePath,dite_eq_left hj]
    change get j (fiberEquiv (σ.apply_symm_apply (label j))
      (partialReversePairs σ s hf p (σ.symm (label j))).2)=get j (p (label j)).1
    rw [partialReversePairs_selected σ s hf p _ hj']
    exact congrArg (get j) (fiberEquiv_pi (σ.apply_symm_apply (label j)) (fun i ↦ (p i).1))
  · rw [routePath_unselected σ.symm s (reverse_fix σ s hf) allowed label get j hj,
      partialReversePairs_outside_fst σ s hf p _ hj]

omit [Fintype J] [DecidableEq J] in
lemma partialReverse_checks {L : Length} (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (r : ℝ) (anchor : J→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j)) :
    (partialReversePairs σ s hf)⁻¹'
      retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ=
    retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ := by
  ext p
  constructor
  · intro hp e _
    rcases e with ⟨b,e⟩
    cases b
    · have hh := hp (true,e) (Finset.subset_univ _)
      change ¬TrialCollision r
        (projectCurve L (routePath σ.symm s (reverse_fix σ s hf) allowed label get true e.val.2
          (partialReversePairs σ s hf p (routeOwner σ.symm label true e.val.2))).val)
        (routePath σ.symm s (reverse_fix σ s hf) allowed label get true e.val.1
          (partialReversePairs σ s hf p (routeOwner σ.symm label true e.val.1))).val at hh
      rw [partialReverse_secondary_path,partialReverse_secondary_path] at hh
      exact hh
    · have hh := hp (false,e) (Finset.subset_univ _)
      change ¬TrialCollision r
        (projectCurve L (get e.val.2 (partialReversePairs σ s hf p (label e.val.2)).1).val)
        (get e.val.1 (partialReversePairs σ s hf p (label e.val.1)).1).val at hh
      rw [partialReverse_primary_path σ s hf allowed label get p e.val.2,
        partialReverse_primary_path σ s hf allowed label get p e.val.1] at hh
      exact hh
  · intro hp e _
    rcases e with ⟨b,e⟩
    cases b
    · change ¬TrialCollision r
        (projectCurve L (get e.val.2 (partialReversePairs σ s hf p (label e.val.2)).1).val)
        (get e.val.1 (partialReversePairs σ s hf p (label e.val.1)).1).val
      rw [partialReverse_primary_path σ s hf allowed label get p e.val.2,
        partialReverse_primary_path σ s hf allowed label get p e.val.1]
      exact hp (true,e) (Finset.subset_univ _)
    · change ¬TrialCollision r
        (projectCurve L (routePath σ.symm s (reverse_fix σ s hf) allowed label get true e.val.2
          (partialReversePairs σ s hf p (routeOwner σ.symm label true e.val.2))).val)
        (routePath σ.symm s (reverse_fix σ s hf) allowed label get true e.val.1
          (partialReversePairs σ s hf p (routeOwner σ.symm label true e.val.1))).val
      rw [partialReverse_secondary_path,partialReverse_secondary_path]
      exact hp (false,e) (Finset.subset_univ _)

lemma physical_conditioned_reverse {L : Length} (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (r : ℝ) (anchor : J→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (conditionedMeasure (Measure.pi μ)
        (retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ)).map
      (partialReversePairs σ s hf)=
    conditionedMeasure (Measure.pi fun j ↦ (μ (σ j)).map (partialReverseFactor σ s hf j))
      (retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ) := by
  rw [←partialReverse_checks σ s hf r anchor allowed label get hg]
  exact partialReversePairs_conditioned σ s hf μ (measurableSet_retainedEvent _ _)

end HardSphere.Bridge

end
end

end

end OAI
