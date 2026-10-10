import OAI.Analysis.KadisonKastler.ProjectionFamilyCorner
import OAI.Analysis.KadisonKastler.StrongAnalyticApply

namespace OAI

/-! # Strong limits for increasing families of projection tests -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionFamilyRemainderSpace_iUnion {ι : Type*}
    (S : ι → Set (AlgebraProjection M)) :
    projectionFamilyRemainderSpace (⋃ i, S i)=⨅ i, projectionFamilyRemainderSpace (S i) := by
  ext x
  change x ∈ projectionFamilyRemainderSpace (⋃ i, S i) ↔
    x ∈ (⨅ i, projectionFamilyRemainderSpace (S i) : ClosedSubmodule ℂ H)
  rw [mem_projectionFamilyRemainderSpace,ClosedSubmodule.mem_iInf]
  constructor
  · intro hx i
    rw [mem_projectionFamilyRemainderSpace]
    exact fun p hp => hx p (Set.mem_iUnion.mpr ⟨i,hp⟩)
  · intro hx p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    exact (mem_projectionFamilyRemainderSpace (S i) x).mp (hx i) p hi

theorem projectionFamilyCommutationSpace_iUnion {ι : Type*}
    (J : H ≃ₗᵢ⋆[ℂ] H) (S : ι → Set (AlgebraProjection M)) :
    projectionFamilyCommutationSpace J (⋃ i, S i)=⨅ i, projectionFamilyCommutationSpace J (S i) := by
  ext x
  change x ∈ projectionFamilyCommutationSpace J (⋃ i, S i) ↔
    x ∈ (⨅ i, projectionFamilyCommutationSpace J (S i) : ClosedSubmodule ℂ H)
  rw [mem_projectionFamilyCommutationSpace,ClosedSubmodule.mem_iInf]
  constructor
  · intro hx i
    rw [mem_projectionFamilyCommutationSpace]
    exact fun p hp => hx p (Set.mem_iUnion.mpr ⟨i,hp⟩)
  · intro hx p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    exact (mem_projectionFamilyCommutationSpace J (S i) x).mp (hx i) p hi

theorem projectionFamilyRemainder_tendsto {ι : Type*} [Preorder ι]
    (S : ι → Set (AlgebraProjection M)) (hS : Monotone S) (x : H) :
    Tendsto (fun i => (projectionFamilyRemainder (S i)).val.val x) atTop
      (𝓝 ((projectionFamilyRemainder (⋃ i, S i)).val.val x)) := by
  have hK : Antitone (fun i => projectionFamilyRemainderSpace (S i)) :=
    projectionFamilyRemainderSpace_antitone.comp_monotone hS
  have ht := decreasing_closed_projection_tendsto _ hK x
  have hp : (⨅ i, projectionFamilyRemainderSpace (S i)).toSubmodule.starProjection=
      (projectionFamilyRemainderSpace (⋃ i, S i)).toSubmodule.starProjection := by
    congr 1
    exact congrArg ClosedSubmodule.toSubmodule (projectionFamilyRemainderSpace_iUnion S).symm
  rw [hp] at ht
  exact ht

theorem projectionFamilyPinching_tendsto {ι : Type*} [Preorder ι]
    (J : H ≃ₗᵢ⋆[ℂ] H) (S : ι → Set (AlgebraProjection M)) (hS : Monotone S) (x : H) :
    Tendsto (fun i => projectionFamilyPinching J (S i) x) atTop
      (𝓝 (projectionFamilyPinching J (⋃ i, S i) x)) := by
  have hK : Antitone (fun i => projectionFamilyCommutationSpace J (S i)) :=
    (projectionFamilyCommutationSpace_antitone J).comp_monotone hS
  have ht := decreasing_closed_projection_tendsto _ hK x
  have hp : (⨅ i, projectionFamilyCommutationSpace J (S i)).toSubmodule.starProjection=
      (projectionFamilyCommutationSpace J (⋃ i, S i)).toSubmodule.starProjection := by
    congr 1
    exact congrArg ClosedSubmodule.toSubmodule (projectionFamilyCommutationSpace_iUnion J S).symm
  rw [hp] at ht
  exact ht

theorem projectionFamilyQuadratic_tendsto {ι : Type*} [Preorder ι]
    (J : H ≃ₗᵢ⋆[ℂ] H) (S : ι → Set (AlgebraProjection M)) (hS : Monotone S) (x : H) :
    Tendsto (fun i => modularQuadratic J (projectionFamilyRemainder (S i)).val x) atTop
      (𝓝 (modularQuadratic J (projectionFamilyRemainder (⋃ i, S i)).val x)) := by
  have hn (i : ι) : ‖(projectionFamilyRemainder (S i)).val.val‖≤1 :=
    ((projectionFamilyRemainder (S i)).property.map M.toStarSubalgebra.subtype).norm_le _
  have ht := J.continuous.continuousAt.tendsto.comp
    (projectionFamilyRemainder_tendsto S hS (J x))
  exact tendsto_strong_apply (projectionFamilyRemainder_tendsto S hS)
    (Filter.Eventually.of_forall hn) ht

end

end KadisonKastler

end OAI
