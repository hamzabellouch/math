import OAI.Analysis.KadisonKastler.CuntzMatrices
import OAI.Analysis.KadisonKastler.BlockMatrices
import OAI.Analysis.KadisonKastler.SmallContractionUnitaryAverage
import OAI.Analysis.KadisonKastler.PublishedDixmier

namespace OAI

/-! # Independent unitary actions on an off-diagonal corner

Two orthogonal isometries identify the ambient algebra with its two-by-two
amplification. Block-diagonal conjugations then act independently on the
two sides of an off-diagonal coefficient. Convexity extends this action
to multiplication by small contractions.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def twoBlockUnitary (u v : unitary A) : unitary (CStarMatrix (Fin 2) (Fin 2) A) :=
  ⟨blockDiagonal (u : A) (v : A), by
    constructor <;> ext i j
    all_goals
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        simp [blockDiagonal, diagonalStarAlgHom_apply, u.property.1, u.property.2,
          v.property.1, v.property.2]⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CuntzFamily

variable (S : CuntzFamily (Fin 2) H)

theorem matrixEquiv_symm_eq_assemble (X : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H)) :
    S.matrixEquiv.symm X = S.assemble X := by
  apply S.matrixEquiv.injective
  exact (S.matrixEquiv.apply_symm_apply X).trans (S.matrix_assemble X).symm

def liftedTwoBlockUnitary (u v : unitary (H →L[ℂ] H)) : unitary (H →L[ℂ] H) :=
  Unitary.map (StarMonoidHom.ofClass S.matrixEquiv.symm) (twoBlockUnitary u v)

theorem matrix_liftedTwoBlockUnitary (u v : unitary (H →L[ℂ] H)) :
    S.matrix (S.liftedTwoBlockUnitary u v : H →L[ℂ] H) =
      blockDiagonal (u : H →L[ℂ] H) (v : H →L[ℂ] H) :=
  S.matrixEquiv.apply_symm_apply (twoBlockUnitary u v)

theorem liftedTwoBlockUnitary_mem (N : VonNeumannAlgebra H)
    (hS : ∀ i, S.entry i ∈ N) (u v : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ N) (hv : (v : H →L[ℂ] H) ∈ N) :
    (S.liftedTwoBlockUnitary u v : H →L[ℂ] H) ∈ N := by
  change S.matrixEquiv.symm (twoBlockUnitary u v) ∈ N
  rw [S.matrixEquiv_symm_eq_assemble]
  apply S.assemble_mem N hS
  intro i j
  change blockDiagonal (u : H →L[ℂ] H) (v : H →L[ℂ] H) i j ∈ N
  fin_cases i <;> fin_cases j
  · exact hu
  · exact N.zero_mem
  · exact N.zero_mem
  · exact hv

theorem exists_corner_conjugate (N : VonNeumannAlgebra H)
    (hS : ∀ i, S.entry i ∈ N) (T : H →L[ℂ] H)
    (u v : unitary (Algebra N)) :
    ∃ w : unitary (Algebra N),
      S.matrix (unitaryConj (ambientAlgebraUnitary w) T) 0 1 =
        (u : Algebra N).val * S.matrix T 0 1 * (v : Algebra N).val := by
  let U : unitary (H →L[ℂ] H) := ambientAlgebraUnitary u
  let V : unitary (H →L[ℂ] H) := ambientAlgebraUnitary (star v)
  let d : CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
    blockDiagonal (U : H →L[ℂ] H) (V : H →L[ℂ] H)
  let W : unitary (H →L[ℂ] H) := S.liftedTwoBlockUnitary U V
  have hW : (W : H →L[ℂ] H) ∈ N := S.liftedTwoBlockUnitary_mem N hS U V
    (u : Algebra N).property (star v : Algebra N).property
  refine ⟨algebraUnitaryOfMem W hW, ?_⟩
  have hWmat : S.matrix (W : H →L[ℂ] H) = d := S.matrix_liftedTwoBlockUnitary U V
  have he : S.matrix (unitaryConj W T) =
      d * S.matrix T * star d := by
    change S.matrixHom ((W : H →L[ℂ] H) * T * star (W : H →L[ℂ] H)) = _
    rw [map_mul, map_mul, map_star]
    change S.matrix _ * S.matrix T * star (S.matrix _) = _
    rw [hWmat]
  change S.matrix (unitaryConj W T) 0 1 = _
  rw [he]
  simp [d, U, V, ambientAlgebraUnitary, blockDiagonal, diagonalStarAlgHom_apply,
    CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two, mul_assoc]

def upperRightLinearMap : (H →L[ℂ] H) →ₗ[ℝ] (H →L[ℂ] H) :=
  { toFun T := S.matrix T 0 1
    map_add' T U := by simp [matrix, mul_add, add_mul]
    map_smul' t T := by simp [matrix] }

theorem small_contraction_corner_mem (N : VonNeumannAlgebra H)
    (hS : ∀ i, S.entry i ∈ N) (K : Set (H →L[ℂ] H)) (hK : Convex ℝ K)
    (hinv : ∀ w : unitary (Algebra N), ∀ T ∈ K,
      unitaryConj (ambientAlgebraUnitary w) T ∈ K)
    (T : H →L[ℂ] H) (hT : T ∈ K)
    (a b : Algebra N) (ha : ‖a‖ ≤ 1 / 2) (hb : ‖b‖ ≤ 1 / 2) :
    ∃ V ∈ K, S.matrix V 0 1 = a.val * S.matrix T 0 1 * b.val := by
  let L := S.upperRightLinearMap
  have hc : Convex ℝ (L '' K) := hK.linear_image L
  have hu (u v : unitary (Algebra N)) :
      (u : Algebra N).val * S.matrix T 0 1 * (v : Algebra N).val ∈ L '' K := by
    obtain ⟨w, hw⟩ := S.exists_corner_conjugate N hS T u v
    exact ⟨_, hinv w T hT, hw⟩
  have hm := mul_small_contractions_mem_convex
    (N.toStarSubalgebra.subtype.toAlgHom.restrictScalars ℝ) (S.matrix T 0 1)
    (L '' K) hc hu a b ha hb
  exact hm

end CuntzFamily

end

end KadisonKastler

end OAI
