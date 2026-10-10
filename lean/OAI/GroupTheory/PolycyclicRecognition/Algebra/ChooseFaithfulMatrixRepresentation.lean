import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Lie.OfAssociative

namespace OAI

/-! # Choosing a faithful integration without expanding its source group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L Γ X Y : Type} [LieRing L] [LieAlgebra ℝ L]
  [Group Γ] [TopologicalSpace Γ]

theorem exists_faithful_matrix_integration
    (Q : ∀ m, (L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ) → Prop)
    (u : X → L) (v : Y → L) (f : X → Y → Γ)
    (hq : ∃ m, 0 < m ∧ ∃ j, Q m j)
    (hi : ∀ m j, Q m j →
      ∃ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ, Continuous ρ ∧
        ∀ x y, ρ (f x y) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y)))
    (hf : ∀ m j, Q m j → ∀ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
      (∀ x y, ρ (f x y) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y))) →
      Function.Injective ρ) :
    ∃ m, 0 < m ∧ ∃ j, Q m j ∧
      ∃ ρ : Γ →* (Matrix (Fin m) (Fin m) ℝ)ˣ, Continuous ρ ∧ Function.Injective ρ ∧
        ∀ x y, ρ (f x y) = algebraExpUnit (j (u x)) * algebraExpUnit (j (v y)) := by
  obtain ⟨m,hm,j,hj⟩ := hq
  obtain ⟨ρ,hρ,he⟩ := hi m j hj
  exact ⟨m,hm,j,hj,ρ,hρ,hf m j hj ρ he,he⟩

end PolycyclicRecognition

end

end OAI
