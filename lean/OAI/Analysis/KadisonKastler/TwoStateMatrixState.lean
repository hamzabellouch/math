import OAI.Analysis.KadisonKastler.TwoStateMatrixAlgebra
import OAI.Analysis.KadisonKastler.ProductStateCentralizer

namespace OAI

/-! # The diagonal state of the two-state matrix algebra -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)

theorem twoStateMatrix_state (a : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) :
    productVectorState (twoStateMatrixVector Ω ξ) (twoStateMatrixEquiv M a).val =
      inner ℂ Ω ((a 0 0).val Ω) + inner ℂ ξ ((a 1 1).val ξ) := by
  rw [twoStateMatrixEquiv_coe]
  change (∑ i : Fin 2, inner ℂ (tupleSingle 0 Ω i)
      ((twoStateMatrixRepresentation (StarAlgEquiv.refl ℂ (Algebra M)) a
        (twoStateMatrixVector Ω ξ)).fst i)) +
    (∑ i : Fin 2, inner ℂ (tupleSingle 1 ξ i)
      ((twoStateMatrixRepresentation (StarAlgEquiv.refl ℂ (Algebra M)) a
        (twoStateMatrixVector Ω ξ)).snd i)) = _
  simp only [Fin.sum_univ_two, tupleSingle_apply,
    twoStateMatrixRepresentation_vector_fst, twoStateMatrixRepresentation_vector_snd]
  simp

def twoStateMatrixProjection (i : Fin 2) : Algebra (twoStateMatrixAlgebra M) :=
  twoStateMatrixEquiv M (CStarMatrix.ofMatrix (Matrix.single i i 1))

theorem twoStateMatrixProjection_centralizes (i : Fin 2) :
    ProductStateCentralizes (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ)
      (twoStateMatrixProjection M i).val := by
  intro a ha
  obtain ⟨b, hb⟩ := (twoStateMatrixEquiv M).surjective ⟨a, ha⟩
  have he : (twoStateMatrixEquiv M b).val = a := congrArg Subtype.val hb
  rw [← he]
  change productVectorState (twoStateMatrixVector Ω ξ)
      ((twoStateMatrixEquiv M (CStarMatrix.ofMatrix (Matrix.single i i 1))).val *
        (twoStateMatrixEquiv M b).val) =
    productVectorState (twoStateMatrixVector Ω ξ)
      ((twoStateMatrixEquiv M b).val *
        (twoStateMatrixEquiv M (CStarMatrix.ofMatrix (Matrix.single i i 1))).val)
  have hmul (x y : CStarMatrix (Fin 2) (Fin 2) (Algebra M)) :
      (twoStateMatrixEquiv M x).val * (twoStateMatrixEquiv M y).val =
        (twoStateMatrixEquiv M (x * y)).val :=
    congrArg Subtype.val (map_mul (twoStateMatrixEquiv M) x y).symm
  rw [hmul, hmul, twoStateMatrix_state, twoStateMatrix_state]
  fin_cases i <;> simp [CStarMatrix.mul_apply, Matrix.single_apply]

end

end KadisonKastler

end OAI
