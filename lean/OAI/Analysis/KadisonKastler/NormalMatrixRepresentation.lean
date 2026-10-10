import OAI.Analysis.KadisonKastler.NormalPairAlgebra
import OAI.Analysis.KadisonKastler.MatrixVonNeumann
import OAI.Analysis.KadisonKastler.WeakCPLimits

namespace OAI

/-! # Bounded weak continuity of the finite matrix representation change -/

namespace KadisonKastler

open Generator Filter
open scoped Topology CStarAlgebra

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

local instance normalMatrixSourceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance normalMatrixSourceStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

private theorem matrix_symm_entry_coefficient
    (a : Algebra (matrixVonNeumann (ι := Fin 2) M)) (i j : Fin 2) (x y : H) :
    inner ℂ y ((((matrixAlgebraEquiv M).symm a) i j).val x) =
      inner ℂ (tupleSingle i y) (a.val (tupleSingle j x)) := by
  rw [← operatorEntry_matrixOperatorHom, matrixAlgebraEquiv_symm_operator]
  change inner ℂ y (a.val (tupleSingle j x) i) = _
  fin_cases i <;> simp [PiLp.inner_apply, Fin.sum_univ_two, tupleSingle_apply]

def normalMatrixRepresentation (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    Algebra (matrixVonNeumann (ι := Fin 2) M) →⋆ₐ[ℂ]
      (FiniteHilbert (Fin 2) K →L[ℂ] FiniteHilbert (Fin 2) K) :=
  (matrixOperatorHom N).comp ((coefficientMatrixMap θ.toStarAlgHom).comp
    (matrixAlgebraEquiv M).symm.toStarAlgHom)

theorem normalMatrixRepresentation_boundedWeakNormal (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom)) :
    BoundedWeakNormal (matrixVonNeumann (ι := Fin 2) M) (normalMatrixRepresentation θ) := by
  intro ι l a b C hn hw x y
  let A := fun n => (matrixAlgebraEquiv M).symm (a n)
  let B := (matrixAlgebraEquiv M).symm b
  have hc (i j : Fin 2) (v w : K) :
      Tendsto (fun n => inner ℂ w ((θ (A n i j)).val v)) l
        (𝓝 (inner ℂ w ((θ (B i j)).val v))) := by
    apply hθ (fun n => A n i j) (B i j) C
    · filter_upwards [hn] with n hna
      have hentry : ‖A n i j‖ ≤ ‖A n‖ := CStarMatrix.norm_entry_le_norm
      have hnorm : ‖A n‖ = ‖a n‖ :=
        NonUnitalStarAlgHom.norm_map (matrixAlgebraEquiv M).symm
          (matrixAlgebraEquiv M).symm.injective (a n)
      exact hentry.trans (hnorm.trans_le hna)
    · intro v w
      simpa only [A, B, matrix_symm_entry_coefficient] using
        hw (tupleSingle j v) (tupleSingle i w)
  exact hilbertMatrix_weak_limit
    (fun n => (coefficientMatrixMap θ.toStarAlgHom (A n)).map N.toStarSubalgebra.subtype)
    ((coefficientMatrixMap θ.toStarAlgHom B).map N.toStarSubalgebra.subtype)
    hc x y

end

end KadisonKastler

end OAI
