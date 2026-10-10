import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChooseFaithfulMatrixRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTriangularImage
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticRepresentationAtlas

namespace OAI

/-! # Assembling a represented group from faithful factor integrations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L Γ X Y E : Type} [LieRing L] [LieAlgebra ℝ L]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [IsTopologicalGroup Γ] in
theorem exists_represented_matrix_group
    (Q : ∀ m, (L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) → Prop)
    (u : X → L) (v : Y → L) (f : X × Y → Γ) (hf : Function.Surjective f)
    (hdata : ∃ m, 0 < m ∧ ∃ j, Q m j ∧
      ∃ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ, Continuous ρ ∧ Function.Injective ρ ∧
        ∀ x y, ρ (f (x,y)) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y)))
    (hu : ∀ m j, Q m j → ∀ z, (j z).IsUpperTriangular)
    (hc : ∀ m j, Q m j → ∀ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
      (∀ x y, ρ (f (x,y)) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y))) →
        Nonempty (RepresentedLocalChart (E := E) ρ)) :
    ∃ m, ∃ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ, Continuous ρ ∧ Function.Injective ρ ∧
      (∀ g, (ρ g : Matrix (Fin m) (Fin m) ℝ).IsUpperTriangular) ∧
      Nonempty (RepresentedLocalChart (E := E) ρ) := by
  obtain ⟨m,_,j,hj,ρ,hρ,hi,he⟩ := hdata
  exact ⟨m,ρ,hρ,hi,upperTriangular_of_exponential_factors f hf
    (j ∘ u) (j ∘ v) (fun x => hu m j hj _) (fun y => hu m j hj _) ρ he,
    hc m j hj ρ he⟩

end PolycyclicRecognition

end

end OAI
