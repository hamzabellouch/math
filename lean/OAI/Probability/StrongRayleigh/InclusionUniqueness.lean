import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable section

open MeasureTheory Set MeasurableSpace

namespace Problem336AdditiveD139

def inclusionEvent {I : Type u_1} (A : Finset I) : Set (I → Bool) :=
  {x | ∀ i ∈ A, x i = true}

@[simp] theorem inclusionEvent_empty {I : Type u_2} :
    inclusionEvent (∅ : Finset I) = Set.univ := by
  ext x
  simp [inclusionEvent]

@[simp] theorem inclusionEvent_singleton {I : Type u_3} (i : I) :
    inclusionEvent ({i} : Finset I) = {x : I → Bool | x i = true} := by
  ext x
  simp [inclusionEvent]

@[simp] theorem inclusionEvent_union {I : Type u_4} [DecidableEq I] (A B : Finset I) :
    inclusionEvent (A ∪ B) = inclusionEvent A ∩ inclusionEvent B := by
  classical
  ext x
  simp [inclusionEvent, or_imp, forall_and]

theorem measurableSet_inclusionEvent {I : Type u_5} (A : Finset I) :
    MeasurableSet (inclusionEvent A) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have h : inclusionEvent (insert i A) =
        {x : I → Bool | x i = true} ∩ inclusionEvent A := by
      ext x
      simp [inclusionEvent]
    rw [h]
    exact (measurable_pi_apply i (measurableSet_singleton true)).inter ih

theorem isPiSystem_inclusionEvents {I : Type u_6} :
    IsPiSystem (Set.range (@inclusionEvent I)) := by
  classical
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ _
  exact ⟨A ∪ B, inclusionEvent_union A B⟩

theorem generateFrom_inclusionEvents {I : Type u_7} :
    MeasurableSpace.generateFrom (Set.range (@inclusionEvent I)) =
      (inferInstance : MeasurableSpace (I → Bool)) := by
  classical
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le (by
      rintro _ ⟨A, rfl⟩
      exact measurableSet_inclusionEvent A)
  · change MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi]
    refine iSup_le fun i => ?_
    rw [← measurable_iff_comap_le]
    apply measurable_to_bool
    have h : (fun x : I → Bool => x i) ⁻¹' {true} = inclusionEvent {i} := by
      ext x
      simp [inclusionEvent]
    rw [h]
    exact MeasurableSpace.measurableSet_generateFrom ⟨{i}, rfl⟩

theorem probabilityMeasure_eq_of_inclusion_probabilities {I : Type u_8}
    (μ ν : ProbabilityMeasure (I → Bool))
    (h : ∀ A : Finset I,
      (μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true} =
      (ν : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_generateFrom_of_iUnion
    (Set.range (@inclusionEvent I)) (fun _ : ℕ => Set.univ)
    generateFrom_inclusionEvents.symm isPiSystem_inclusionEvents
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      exact Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
  · intro n
    exact ⟨∅, inclusionEvent_empty⟩
  · intro n
    exact measure_ne_top _ _
  · rintro _ ⟨A, rfl⟩
    exact h A

theorem probabilityMeasure_eq_of_inclusion_probabilities_toReal {I : Type u_9}
    (μ ν : ProbabilityMeasure (I → Bool))
    (h : ∀ A : Finset I,
      ((μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}).toReal =
      ((ν : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}).toReal) : μ = ν := by
  apply probabilityMeasure_eq_of_inclusion_probabilities μ ν
  intro A
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h A)

end Problem336AdditiveD139

end

end OAI
