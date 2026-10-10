import OAI.Analysis.KadisonKastler.TwoStateMatrixAlgebra
import OAI.Analysis.KadisonKastler.MatrixFixedCorners

namespace OAI

/-! # Isometric embeddings of the two diagonal state spaces -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def twoStateCornerEmbedding (i : Fin 2) : H →ₗᵢ[ℂ] TwoStateMatrixHilbert H H where
  toFun x := if i = 0 then WithLp.toLp 2 (tupleSingle 0 x, 0)
    else WithLp.toLp 2 (0, tupleSingle 1 x)
  map_add' x y := by
    fin_cases i <;> simp [map_add, ← WithLp.toLp_add]
  map_smul' z x := by
    fin_cases i <;> simp [map_smul, ← WithLp.toLp_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    fin_cases i <;> simp

omit [CompleteSpace H] in
@[simp] theorem twoStateCornerEmbedding_fst_zero (x : H) :
    (twoStateCornerEmbedding 0 x).fst = tupleSingle 0 x := rfl

omit [CompleteSpace H] in
@[simp] theorem twoStateCornerEmbedding_snd_zero (x : H) :
    (twoStateCornerEmbedding 0 x).snd = 0 := rfl

omit [CompleteSpace H] in
@[simp] theorem twoStateCornerEmbedding_fst_one (x : H) :
    (twoStateCornerEmbedding 1 x).fst = 0 := rfl

omit [CompleteSpace H] in
@[simp] theorem twoStateCornerEmbedding_snd_one (x : H) :
    (twoStateCornerEmbedding 1 x).snd = tupleSingle 1 x := rfl

def twoStateVectorAt (Ω ξ : H) (i : Fin 2) : H := if i = 0 then Ω else ξ

theorem twoStateCornerEmbedding_vector (M : VonNeumannAlgebra H) (Ω ξ : H)
    (i : Fin 2) (a : Algebra M) :
    twoStateCornerEmbedding i (a.val (twoStateVectorAt Ω ξ i)) =
      (twoStateMatrixEquiv M (matrixSlot i i a)).val (twoStateMatrixVector Ω ξ) := by
  rw [twoStateMatrixEquiv_coe]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro j
  · change (twoStateCornerEmbedding i (a.val (twoStateVectorAt Ω ξ i))).fst j =
      (twoStateMatrixRepresentation (StarAlgEquiv.refl ℂ (Algebra M))
        (matrixSlot i i a) (twoStateMatrixVector Ω ξ)).fst j
    rw [twoStateMatrixRepresentation_vector_fst]
    fin_cases i <;> fin_cases j <;>
      simp [twoStateVectorAt, matrixSlot, tupleSingle_apply]
  · change (twoStateCornerEmbedding i (a.val (twoStateVectorAt Ω ξ i))).snd j =
      (twoStateMatrixRepresentation (StarAlgEquiv.refl ℂ (Algebra M))
        (matrixSlot i i a) (twoStateMatrixVector Ω ξ)).snd j
    rw [twoStateMatrixRepresentation_vector_snd]
    fin_cases i <;> fin_cases j <;>
      simp [twoStateVectorAt, matrixSlot, tupleSingle_apply]

end

end KadisonKastler

end OAI
