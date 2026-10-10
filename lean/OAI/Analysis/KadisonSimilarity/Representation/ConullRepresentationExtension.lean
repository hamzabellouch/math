import OAI.Analysis.KadisonSimilarity.Representation.ConullFieldExtension
import OAI.Analysis.KadisonSimilarity.Representation.NonunitalRangeRepresentation
import Mathlib.Analysis.CStarAlgebra.Unitization

namespace OAI

/-! Extend the original algebra's conull fiber representations by zero.
The maps remain nonunital star homomorphisms at every base point, so their
unit projections give genuine representations on every projection fiber. -/

noncomputable section
namespace KadisonSimilarity

variable {Ω B F : Type*} [CStarAlgebra B]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (s : Set Ω)

def zeroExtendNonunitalRepresentation
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F))
    (x : Ω) : B →⋆ₙₐ[ℂ] (F →L[ℂ] F) := by
  classical
  exact if h : x ∈ s then
    (ρ ⟨x, h⟩).toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ B)
  else 0

theorem zeroExtendNonunitalRepresentation_apply
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ] (F →L[ℂ] F)) (b : B) (x : Ω) :
    zeroExtendNonunitalRepresentation s ρ x b =
      zeroExtendOperatorField s (fun y => ρ y (Unitization.inr b)) x := by
  classical
  by_cases hx : x ∈ s
  · simp only [zeroExtendNonunitalRepresentation, zeroExtendOperatorField, dite_eq_left hx,
      NonUnitalStarAlgHom.comp_apply,
      Unitization.inrNonUnitalStarAlgHom_apply]
    rfl
  · simp only [zeroExtendNonunitalRepresentation, zeroExtendOperatorField, dite_eq_right hx,
      NonUnitalStarAlgHom.zero_apply]

end KadisonSimilarity

end

end OAI
