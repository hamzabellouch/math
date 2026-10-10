import OAI.Probability.SpanningForest.CylinderLimitMeasure
import OAI.Probability.SpanningForest.BinaryWeakConvergence

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem336.CylinderKernel

def cylinder {I : Type*} (A B : Finset I) : Set (I → Bool) :=
  {x | (∀ i ∈ A, x i = true) ∧ (∀ i ∈ B, x i = false)}

def cylinders (I : Type*) : Set (Set (I → Bool)) :=
  {s | ∃ A B : Finset I, s = cylinder A B}

lemma isPiSystem_cylinders (I : Type*) : IsPiSystem (cylinders I) := by
  classical
  rintro s ⟨A, B, rfl⟩ t ⟨C, D, rfl⟩ _
  refine ⟨A ∪ C, B ∪ D, ?_⟩
  ext x
  simp only [cylinder, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Finset.mem_union, or_imp, forall_and]
  tauto

lemma generateFrom_cylinders (I : Type*) [Countable I] :
    MeasurableSpace.generateFrom (cylinders I) =
      (inferInstance : MeasurableSpace (I → Bool)) := by
  classical
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨A, B, rfl⟩
    exact (Problem336.isClopen_boolCylinder A B).isOpen.measurableSet
  · have hid : @Measurable (I → Bool) (I → Bool)
        (MeasurableSpace.generateFrom (cylinders I)) inferInstance id := by
      refine @Measurable.of_eval (I → Bool) I (fun _ => Bool)
        (MeasurableSpace.generateFrom (cylinders I)) (fun _ => inferInstance) id ?_
      intro i
      apply measurable_to_bool
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨{i}, ∅, ?_⟩
      ext x
      simp [cylinder]
    intro s hs
    exact hid hs

theorem measurable_probabilityMeasure_of_cylinders
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : X → ProbabilityMeasure (I → Bool))
    (hμ : ∀ A B : Finset I,
      Measurable (fun x => (μ x : Measure (I → Bool)) (cylinder A B))) :
    Measurable μ := by
  have h : Measurable (fun x => (μ x : Measure (I → Bool))) := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (generateFrom_cylinders I).symm (isPiSystem_cylinders I)
    rintro s ⟨A, B, rfl⟩
    exact hμ A B
  exact h.subtype_mk

theorem exists_measurable_probabilityMeasure_of_cylinder_limits
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (μn : ℕ → X → ProbabilityMeasure (I → Bool))
    (L : X → Finset I → Finset I → ℝ≥0∞)
    (hLm : ∀ A B, Measurable (fun x => L x A B))
    (hL : ∀ x A B, Tendsto
      (fun n => (μn n x : Measure (I → Bool)) (cylinder A B))
      atTop (𝓝 (L x A B))) :
    ∃ μ : X → ProbabilityMeasure (I → Bool), Measurable μ ∧
      ∀ x A B, (μ x : Measure (I → Bool)) (cylinder A B) = L x A B := by
  have hex (x : X) := Problem336.exists_probabilityMeasure_of_boolCylinder_limits
    (fun n => μn n x) (L x) (hL x)
  choose μ hμ using hex
  refine ⟨μ, measurable_probabilityMeasure_of_cylinders μ (fun A B => ?_), hμ⟩
  convert hLm A B using 1
  funext x
  exact hμ x A B

def positiveCylinders (I : Type*) : Set (Set (I → Bool)) :=
  {s | ∃ A : Finset I, s = {x | ∀ i ∈ A, x i = true}}

lemma isPiSystem_positiveCylinders (I : Type*) : IsPiSystem (positiveCylinders I) := by
  classical
  rintro s ⟨A, rfl⟩ t ⟨B, rfl⟩ _
  refine ⟨A ∪ B, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union, or_imp, forall_and]

lemma generateFrom_positiveCylinders (I : Type*) [Countable I] :
    MeasurableSpace.generateFrom (positiveCylinders I) =
      (inferInstance : MeasurableSpace (I → Bool)) := by
  classical
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨A, rfl⟩
    have hS : IsClopen {x : I → Bool | ∀ i ∈ A, x i = true} := by
      simpa using Problem336.isClopen_boolCylinder A ∅
    exact hS.isOpen.measurableSet
  · have hid : @Measurable (I → Bool) (I → Bool)
        (MeasurableSpace.generateFrom (positiveCylinders I)) inferInstance id := by
      refine @Measurable.of_eval (I → Bool) I (fun _ => Bool)
        (MeasurableSpace.generateFrom (positiveCylinders I)) (fun _ => inferInstance) id ?_
      intro i
      apply measurable_to_bool
      apply MeasurableSpace.measurableSet_generateFrom
      refine ⟨{i}, ?_⟩
      ext x
      simp
    intro s hs
    exact hid hs

theorem measurable_probabilityMeasure_of_positiveCylinders
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : X → ProbabilityMeasure (I → Bool))
    (hμ : ∀ A : Finset I,
      Measurable (fun x => (μ x : Measure (I → Bool)) {z | ∀ i ∈ A, z i = true})) :
    Measurable μ := by
  have h : Measurable (fun x => (μ x : Measure (I → Bool))) := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (generateFrom_positiveCylinders I).symm (isPiSystem_positiveCylinders I)
    rintro s ⟨A, rfl⟩
    exact hμ A
  exact h.subtype_mk

theorem exists_measurable_weakLimit_of_positiveCylinder_limits
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (μn : ℕ → X → ProbabilityMeasure (I → Bool))
    (L : X → Finset I → ℝ≥0∞)
    (hLm : ∀ A, Measurable (fun x => L x A))
    (hL : ∀ x A, Tendsto
      (fun n => (μn n x : Measure (I → Bool)) {z | ∀ i ∈ A, z i = true})
      atTop (𝓝 (L x A))) :
    ∃ μ : X → ProbabilityMeasure (I → Bool), Measurable μ ∧
      (∀ x A, (μ x : Measure (I → Bool)) {z | ∀ i ∈ A, z i = true} = L x A) ∧
      ∀ x, Tendsto (fun n => μn n x) atTop (𝓝 (μ x)) := by
  have hex (x : X) := BinaryLaw.exists_weakLimit_of_positiveCylinder_limits
    (fun n => μn n x) (L x) (hL x)
  choose μ hμ hw using hex
  refine ⟨μ, measurable_probabilityMeasure_of_positiveCylinders μ (fun A => ?_), hμ, hw⟩
  convert hLm A using 1
  funext x
  exact hμ x A

end Problem336.CylinderKernel

end

end OAI
