import Mathlib
import OAI.Analysis.LaughlinFock.BesselComparison
import OAI.Analysis.LaughlinFock.PolynomialPositivity

namespace OAI

/-! L D L. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def copyMatrixData (D : ℕ) (xs : List (List ℚ)) : Matrix (CopyLabel D) (CopyLabel D) ℚ :=
  fun r s => ((xs[r.val.val/2]?.getD [])[s.val.val/2]?).getD 0

def copyDiagonalData (D : ℕ) (xs : List ℚ) : CopyLabel D → ℚ :=
  fun r => (xs[r.val.val/2]?).getD 0

 
def matrixEntriesDecidable {ι : Type*} [Fintype ι] {α : Type*} [DecidableEq α]
    (A B : Matrix ι ι α) : Decidable (∀ i j, A i j = B i j) :=
  @Fintype.decidableForallFintype _ _ (fun _ =>
    @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) _) _

 
theorem rational_ldl_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M L : Matrix ι ι ℚ) (d : ι → ℚ)
    (he : M = L * Matrix.diagonal d * Lᵀ) (hd : ∀ i, 0 ≤ d i) :
    (M.map (algebraMap ℚ ℂ)).PosSemidef := by
  let Lr := L.map (algebraMap ℚ ℝ)
  have hh : (Matrix.diagonal (fun i => (d i : ℝ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast hd i
  have hr : (M.map (algebraMap ℚ ℝ)).PosSemidef := by
    have ht : (Lᵀ).map (algebraMap ℚ ℝ) = Lrᴴ := by
      ext i j
      simp [Lr]
    rw [he, Matrix.map_mul, Matrix.map_mul, ht]
    have he' : (Matrix.diagonal d).map (algebraMap ℚ ℝ) =
        Matrix.diagonal (fun i => (d i : ℝ)) := by
      ext i j
      by_cases hij : i=j <;> simp [hij]
    rw [he']
    exact hh.mul_mul_conjTranspose_same Lr
  have hc := real_matrix_posSemidef_complex (M.map (algebraMap ℚ ℝ)) hr
  convert hc using 1
  ext i j
  simp

end LaughlinFock
end

end OAI
