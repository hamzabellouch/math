import Mathlib

namespace OAI

noncomputable section

namespace Problem340

def conjugateMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (f : X → X) : Y → Y := fun y => e (f (e.symm y))

@[simp] theorem conjugateMap_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) (x : X) :
    conjugateMap e f (e x) = e (f x) := by
  simp [conjugateMap]

@[simp] theorem conjugateMap_symm {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) :
    conjugateMap e.symm (conjugateMap e f) = f := by
  funext x
  simp [conjugateMap]

theorem continuous_conjugateMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {f : X → X} (hf : Continuous f) : Continuous (conjugateMap e f) :=
  e.continuous.comp (hf.comp e.symm.continuous)

theorem bijective_conjugateMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {f : X → X} (hf : Function.Bijective f) : Function.Bijective (conjugateMap e f) :=
  e.bijective.comp (hf.comp e.symm.bijective)

@[simp] theorem bijective_conjugateMap_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) :
    Function.Bijective (conjugateMap e f) ↔ Function.Bijective f := by
  constructor
  · intro h
    simpa using bijective_conjugateMap e.symm h
  · exact bijective_conjugateMap e

theorem coverEntropy_conjugateMap {X Y : Type*}
    [UniformSpace X] [UniformSpace Y] [CompactSpace X] [CompactSpace Y]
    (e : X ≃ₜ Y) (f : X → X) :
    Dynamics.coverEntropy (conjugateMap e f) (Set.univ : Set Y) =
      Dynamics.coverEntropy f (Set.univ : Set X) := by
  have h : Function.Semiconj e f (conjugateMap e f) := by
    intro x
    simp
  have h' : Function.Semiconj e.symm (conjugateMap e f) f := by
    intro y
    simp [conjugateMap]
  apply le_antisymm
  · simpa only [Set.image_univ, e.surjective.range_eq] using
      Dynamics.coverEntropy_image_le_of_uniformContinuous h
        (CompactSpace.uniformContinuous_of_continuous e.continuous) Set.univ
  · simpa only [Set.image_univ, e.symm.surjective.range_eq] using
      Dynamics.coverEntropy_image_le_of_uniformContinuous h'
        (CompactSpace.uniformContinuous_of_continuous e.symm.continuous) Set.univ

end Problem340

end

end OAI
