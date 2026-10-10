import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set

lemma matrix_tsupport_subset_union {E : Type*} [TopologicalSpace E]
    {ι κ : Type*} [Finite ι] [Finite κ] (B : E → Matrix ι κ ℝ) :
    tsupport B⊆⋃ i,⋃ j,tsupport (fun x => B x i j) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun i =>
    isClosed_iUnion_of_finite (fun j => isClosed_closure)))
  intro x hx
  by_contra h
  apply hx
  ext i j
  apply image_eq_zero_of_notMem_tsupport (f := fun y => B y i j)
  intro hij
  exact h (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,hij⟩⟩)

lemma matrix_hasCompactSupport {E : Type*} [TopologicalSpace E]
    {ι κ : Type*} [Finite ι] [Finite κ] (B : E → Matrix ι κ ℝ)
    (hB : ∀ i j,HasCompactSupport (fun x => B x i j)) : HasCompactSupport B :=
  (isCompact_iUnion (fun i => isCompact_iUnion (fun j => hB i j))).of_isClosed_subset
    isClosed_closure (matrix_tsupport_subset_union B)

lemma matrix_tsupport_subset {E : Type*} [TopologicalSpace E]
    {ι κ : Type*} [Finite ι] [Finite κ] (B : E → Matrix ι κ ℝ) {U : Set E}
    (hB : ∀ i j,tsupport (fun x => B x i j)⊆U) : tsupport B⊆U :=
  (matrix_tsupport_subset_union B).trans (iUnion_subset (fun i => iUnion_subset (hB i)))

end ScalarConductivity

end

end OAI
