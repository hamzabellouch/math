import OAI.Analysis.KadisonKastler.UniformGraphComparison
import OAI.Analysis.KadisonKastler.SquareCompleteBound
import OAI.Analysis.KadisonKastler.FaithfulRepresentation

namespace OAI

/-! # Actual row approximants from a completely close linear map

The map need only be linear with range in the second algebra. Its
complete norm distance from inclusion supplies the same row approximants
used by the graph argument, with no further approximation assumption.
-/

namespace KadisonKastler

noncomputable section

section General

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A faithful star homomorphism preserves arbitrary finite rectangular
matrix norms, not only matrices indexed by finite ordinals. -/
theorem injective_starAlgHom_finite_rectangular_norm
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {I J : Type*} [Fintype I] [Fintype J] (X : CStarMatrix I J A) :
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ = ‖X‖ := by
  rw [← norm_rectangularCorner, rectangularCorner_map,
    injective_starAlgHom_matrix_norm φ hφ, norm_rectangularCorner]

/-- A complete bound controls a row indexed on the left by `Unit`. -/
theorem completelyBoundedBy_operator_row (F : A →ₗ[ℂ] B) {γ : ℝ}
    (hF : CompletelyBoundedBy F γ) {k : ℕ} (hk : 0 < k)
    (X : CStarMatrix Unit (Fin k) A) :
    ‖CStarMatrix.mapₗ F X‖ ≤ γ * ‖X‖ := by
  have hcard : 2 ≤ Fintype.card (Unit ⊕ Fin k) := by
    simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]
    omega
  have h := norm_map_square_of_fin F (fun n _ Y => hF n n Y) hcard (rectangularCorner X)
  rw [← rectangularCorner_map, norm_rectangularCorner, norm_rectangularCorner] at h
  exact h

end General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance rowApproximationOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance rowApproximationStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance rowApproximationOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance rowApproximationOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- A completely close map with range in N provides each concrete row
approximant required by the graph comparison theorem. -/
theorem exists_graphRow_approx_of_completelyBoundedBy
    (M N : VonNeumannAlgebra H) (F : Algebra M →ₗ[ℂ] (H →L[ℂ] H))
    (hFN : ∀ x, F x ∈ N) {γ : ℝ}
    (hclose : CompletelyBoundedBy (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) γ)
    (k : ℕ) (X : Fin k → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) :
    ∃ Z : Fin k → H →L[ℂ] H, (∀ i, Z i ∈ N) ∧
      ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖ := by
  by_cases hk : k = 0
  · subst k
    refine ⟨X, (fun i => Fin.elim0 i), ?_⟩
    have hz : operatorRow X = 0 := by ext i j; exact Fin.elim0 j
    simp only [sub_self, norm_zero, hz, mul_zero, le_refl]
  · let X₀ : CStarMatrix Unit (Fin k) (Algebra M) := fun _ i => ⟨X i, hX i⟩
    let Z : Fin k → H →L[ℂ] H := fun i => F ⟨X i, hX i⟩
    refine ⟨Z, (fun i => hFN _), ?_⟩
    have h := completelyBoundedBy_operator_row _ hclose (Nat.pos_of_ne_zero hk) X₀
    have he : CStarMatrix.mapₗ (M.toStarSubalgebra.subtype.toAlgHom.toLinearMap - F) X₀ =
        operatorRow X - operatorRow Z := by ext i j; rfl
    have hi : CStarMatrix.mapₗ M.toStarSubalgebra.subtype.toAlgHom.toLinearMap X₀ =
        operatorRow X := by ext i j; rfl
    have hn := injective_starAlgHom_finite_rectangular_norm M.toStarSubalgebra.subtype
      Subtype.val_injective X₀
    rw [hi] at hn
    rwa [he, ← hn] at h

end

end KadisonKastler

end OAI
