import OAI.Analysis.Quantum.DimensionTen.BorderRelations
import OAI.Analysis.Quantum.DimensionTen.MinorData

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border

lemma adjugate_updateRow_column {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i j : n) (u : n → R) :
    (A.updateRow i u).adjugate j i = A.adjugate j i := by
  simp only [Matrix.adjugate_apply]
  congr 1
  ext k l
  by_cases hk : k = i <;> simp [Matrix.updateRow_apply, hk]

lemma dot_adjugate_column {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i : n) (u : n → R) :
    dotProduct u (fun j => A.adjugate j i) = (A.updateRow i u).det := by
  rw [Matrix.det_eq_sum_mul_adjugate_row _ i]
  simp only [Matrix.updateRow_self, adjugate_updateRow_column, dotProduct]

def cofactorKernel {R : Type*} [CommRing R] (x : Fin 4 → R) : Fin 4 → R :=
  fun j => ((pencilR x).submatrix (rowChoices 0) id).adjugate j 3

lemma cofactorKernel_mul {R : Type*} [CommRing R] (x : Fin 4 → R) (i : Fin 6) :
    (pencilR x *ᵥ cofactorKernel x) i =
      (((pencilR x).submatrix (rowChoices 0) id).updateRow 3 (pencilR x i)).det := by
  exact dot_adjugate_column _ _ _

lemma top_minors_kernel {R : Type*} [CommRing R] (M : Matrix (Fin 6) (Fin 4) R)
    (h : ∀ k : Fin 15, (M.submatrix (rowChoices k) id).det = 0) :
    M *ᵥ (fun j => (M.submatrix (rowChoices 0) id).adjugate j 3) = 0 := by
  ext i
  change dotProduct (M i) (fun j => (M.submatrix (rowChoices 0) id).adjugate j 3) = 0
  rw [dot_adjugate_column]
  fin_cases i
  · exact Matrix.det_updateRow_eq_zero (M := M.submatrix (rowChoices 0) id)
      (i := 0) (j := 3) (by decide)
  · exact Matrix.det_updateRow_eq_zero (M := M.submatrix (rowChoices 0) id)
      (i := 1) (j := 3) (by decide)
  · exact Matrix.det_updateRow_eq_zero (M := M.submatrix (rowChoices 0) id)
      (i := 2) (j := 3) (by decide)
  · have he : (M.submatrix (rowChoices 0) id).updateRow 3 (M 3) =
        M.submatrix (rowChoices 0) id := by
      exact Matrix.updateRow_eq_self _ _
    exact (congrArg Matrix.det he).trans (h 0)
  · have he : (M.submatrix (rowChoices 0) id).updateRow 3 (M 4) =
        M.submatrix (rowChoices 1) id := by
      ext i j
      fin_cases i <;> simp [Matrix.updateRow, rowChoices, PencilAlgebra.rows]
    exact (congrArg Matrix.det he).trans (h 1)
  · have he : (M.submatrix (rowChoices 0) id).updateRow 3 (M 5) =
        M.submatrix (rowChoices 2) id := by
      ext i j
      fin_cases i <;> simp [Matrix.updateRow, rowChoices, PencilAlgebra.rows]
    exact (congrArg Matrix.det he).trans (h 2)

lemma cofactorKernel_eq_zero {R : Type*} [CommRing R] (x : Fin 4 → R)
    (h : minor x = 0) : pencilR x *ᵥ cofactorKernel x = 0 :=
  top_minors_kernel (pencilR x) (fun k => congrFun h k)

lemma rank_lt_of_kernel {R : Type*} [Field R] (M : Matrix (Fin 6) (Fin 4) R)
    (v : Fin 4 → R) (hv : v ≠ 0) (hm : M *ᵥ v = 0) : M.rank < 4 := by
  have hn : ¬ Function.Injective (fun w => M *ᵥ w) := by
    intro hh
    exact hv (hh (hm.trans (Matrix.mulVec_zero M).symm))
  have hr := Matrix.rank_le_width M
  have he : M.rank ≠ 4 := by
    intro h
    apply hn
    change Function.Injective (Matrix.mulVecLin M)
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hdim := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    change M.rank + Module.finrank R (LinearMap.ker (Matrix.mulVecLin M)) =
      Module.finrank R (Fin 4 → R) at hdim
    simp only [h, Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  simpa only [Fintype.card_fin] using lt_of_le_of_ne hr he

end DimensionTen.Border

end
end

section
noncomputable section
open Matrix
namespace DimensionTen.Border

def cofactorCoeffs : Fin 20 → ℤ := ![216, 324, 576, -432, -282, 180, 120, -1116, -1296, -216, 32, 80, -412, -384, 468, -456, -912, 936, 288, 432]

lemma low_eq {R : Type*} [CommRing R] (t : Fin 3 → R) :
    low t = ![t 0 ^ 0 * t 1 ^ 0 * t 2 ^ 0, t 0 ^ 0 * t 1 ^ 0 * t 2 ^ 1, t 0 ^ 0 * t 1 ^ 1 * t 2 ^ 0, t 0 ^ 1 * t 1 ^ 0 * t 2 ^ 0, t 0 ^ 0 * t 1 ^ 0 * t 2 ^ 2, t 0 ^ 0 * t 1 ^ 1 * t 2 ^ 1, t 0 ^ 0 * t 1 ^ 2 * t 2 ^ 0, t 0 ^ 1 * t 1 ^ 0 * t 2 ^ 1, t 0 ^ 1 * t 1 ^ 1 * t 2 ^ 0, t 0 ^ 2 * t 1 ^ 0 * t 2 ^ 0, t 0 ^ 0 * t 1 ^ 0 * t 2 ^ 3, t 0 ^ 0 * t 1 ^ 1 * t 2 ^ 2, t 0 ^ 0 * t 1 ^ 2 * t 2 ^ 1, t 0 ^ 0 * t 1 ^ 3 * t 2 ^ 0, t 0 ^ 1 * t 1 ^ 0 * t 2 ^ 2, t 0 ^ 1 * t 1 ^ 1 * t 2 ^ 1, t 0 ^ 1 * t 1 ^ 2 * t 2 ^ 0, t 0 ^ 2 * t 1 ^ 0 * t 2 ^ 1, t 0 ^ 2 * t 1 ^ 1 * t 2 ^ 0, t 0 ^ 3 * t 1 ^ 0 * t 2 ^ 0] := by
  ext i
  fin_cases i <;> simp [low, mon, monExps, Fin.prod_univ_succ, mul_assoc]

lemma cofactor_chart_last {R : Type*} [CommRing R] (t : Fin 3 → R) :
    cofactorKernel (Fin.cons 1 t) 3 = ∑ i, (cofactorCoeffs i : R) * low t i := by
  rw [cofactorKernel, Matrix.adjugate_apply, pencilR_eq, det_four, low_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.updateRow_apply,
    Matrix.submatrix_apply, Pi.single_apply]
  have hc2 : Fin.cons (α := fun _ : Fin 4 => R) 1 t 2 = t 1 := rfl
  have hc3 : Fin.cons (α := fun _ : Fin 4 => R) 1 t 3 = t 2 := rfl
  simp [pencilExplicit, rowChoices, PencilAlgebra.rows, cofactorCoeffs, hc2, hc3]
  ring

lemma cofactor_alpha_last_ne : cofactorKernel (Fin.cons 1 alpha) 3 ≠ 0 := by
  intro h
  have hh : cofactorKernel (Fin.cons 1 alpha) 3 =
      ∑ i, (cofactorCoeffs i : ℚ) • low alpha i := by
    simpa only [Algebra.smul_def, map_intCast] using cofactor_chart_last alpha
  rw [hh] at h
  have hE := congrArg E h
  rw [E_sum, map_zero] at hE
  have hz := congrFun hE 0
  norm_num [cofactorCoeffs] at hz

end DimensionTen.Border

end
end

end OAI
