import OAI.Analysis.KadisonKastler.NormalTwoStateAlgebra
import OAI.Analysis.KadisonKastler.MatrixFixedCorners
import OAI.Analysis.KadisonKastler.ProductStateCentralizer

namespace OAI

/-! # The diagonal state in the normal two-representation matrix algebra -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
  (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))
  (Ω : H) (ξ : K)

theorem normalTwoState_state (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) :
    productVectorState (twoStateMatrixVector Ω ξ) (normalTwoStateEquiv θ hθ a).val =
      inner ℂ Ω ((a 0 0).val Ω) + inner ℂ ξ ((θ (a 1 1)).val ξ) := by
  rw [normalTwoStateEquiv_coe]
  change (∑ i : Fin 2, inner ℂ (tupleSingle 0 Ω i)
      ((twoStateMatrixRepresentation θ a (twoStateMatrixVector Ω ξ)).fst i)) +
    (∑ i : Fin 2, inner ℂ (tupleSingle 1 ξ i)
      ((twoStateMatrixRepresentation θ a (twoStateMatrixVector Ω ξ)).snd i)) = _
  simp only [Fin.sum_univ_two, tupleSingle_apply,
    twoStateMatrixRepresentation_vector_fst, twoStateMatrixRepresentation_vector_snd]
  simp

def normalTwoStateProjection (i : Fin 2) : Algebra (normalTwoStateAlgebra θ) :=
  normalTwoStateEquiv θ hθ (matrixSlot i i 1)

theorem normalTwoStateProjection_centralizes (i : Fin 2) :
    ProductStateCentralizes (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ)
      (normalTwoStateProjection θ hθ i).val := by
  intro a ha
  obtain ⟨b, hb⟩ := (normalTwoStateEquiv θ hθ).surjective ⟨a, ha⟩
  have he : (normalTwoStateEquiv θ hθ b).val = a := congrArg Subtype.val hb
  rw [← he]
  change productVectorState (twoStateMatrixVector Ω ξ)
      ((normalTwoStateEquiv θ hθ (matrixSlot i i 1)).val *
        (normalTwoStateEquiv θ hθ b).val) =
    productVectorState (twoStateMatrixVector Ω ξ)
      ((normalTwoStateEquiv θ hθ b).val *
        (normalTwoStateEquiv θ hθ (matrixSlot i i 1)).val)
  have hmul (x y : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) :
      (normalTwoStateEquiv θ hθ x).val * (normalTwoStateEquiv θ hθ y).val =
        (normalTwoStateEquiv θ hθ (x * y)).val :=
    congrArg Subtype.val (map_mul (normalTwoStateEquiv θ hθ) x y).symm
  rw [hmul, hmul, normalTwoState_state, normalTwoState_state]
  fin_cases i <;> simp [matrixSlot, CStarMatrix.mul_apply, Matrix.single_apply]

end

end KadisonKastler

end OAI
