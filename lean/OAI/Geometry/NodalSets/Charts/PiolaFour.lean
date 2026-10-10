import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Adjugate
import OAI.Geometry.NodalSets.Elliptic.ContravariantPullback

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma adjugate_four_explicit (M : Fin 4 → Fin 4 → ℝ) :
    Matrix.adjugate M = !![(M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 - M 1 2 * M 2 1 * M 3 3 + M 1 2 * M 2 3 * M 3 1 + M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1), -(M 0 1 * M 2 2 * M 3 3 - M 0 1 * M 2 3 * M 3 2 - M 0 2 * M 2 1 * M 3 3 + M 0 2 * M 2 3 * M 3 1 + M 0 3 * M 2 1 * M 3 2 - M 0 3 * M 2 2 * M 3 1), (M 0 1 * M 1 2 * M 3 3 - M 0 1 * M 1 3 * M 3 2 - M 0 2 * M 1 1 * M 3 3 + M 0 2 * M 1 3 * M 3 1 + M 0 3 * M 1 1 * M 3 2 - M 0 3 * M 1 2 * M 3 1), -(M 0 1 * M 1 2 * M 2 3 - M 0 1 * M 1 3 * M 2 2 - M 0 2 * M 1 1 * M 2 3 + M 0 2 * M 1 3 * M 2 1 + M 0 3 * M 1 1 * M 2 2 - M 0 3 * M 1 2 * M 2 1);
      -(M 1 0 * M 2 2 * M 3 3 - M 1 0 * M 2 3 * M 3 2 - M 1 2 * M 2 0 * M 3 3 + M 1 2 * M 2 3 * M 3 0 + M 1 3 * M 2 0 * M 3 2 - M 1 3 * M 2 2 * M 3 0), (M 0 0 * M 2 2 * M 3 3 - M 0 0 * M 2 3 * M 3 2 - M 0 2 * M 2 0 * M 3 3 + M 0 2 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 2 - M 0 3 * M 2 2 * M 3 0), -(M 0 0 * M 1 2 * M 3 3 - M 0 0 * M 1 3 * M 3 2 - M 0 2 * M 1 0 * M 3 3 + M 0 2 * M 1 3 * M 3 0 + M 0 3 * M 1 0 * M 3 2 - M 0 3 * M 1 2 * M 3 0), (M 0 0 * M 1 2 * M 2 3 - M 0 0 * M 1 3 * M 2 2 - M 0 2 * M 1 0 * M 2 3 + M 0 2 * M 1 3 * M 2 0 + M 0 3 * M 1 0 * M 2 2 - M 0 3 * M 1 2 * M 2 0);
      (M 1 0 * M 2 1 * M 3 3 - M 1 0 * M 2 3 * M 3 1 - M 1 1 * M 2 0 * M 3 3 + M 1 1 * M 2 3 * M 3 0 + M 1 3 * M 2 0 * M 3 1 - M 1 3 * M 2 1 * M 3 0), -(M 0 0 * M 2 1 * M 3 3 - M 0 0 * M 2 3 * M 3 1 - M 0 1 * M 2 0 * M 3 3 + M 0 1 * M 2 3 * M 3 0 + M 0 3 * M 2 0 * M 3 1 - M 0 3 * M 2 1 * M 3 0), (M 0 0 * M 1 1 * M 3 3 - M 0 0 * M 1 3 * M 3 1 - M 0 1 * M 1 0 * M 3 3 + M 0 1 * M 1 3 * M 3 0 + M 0 3 * M 1 0 * M 3 1 - M 0 3 * M 1 1 * M 3 0), -(M 0 0 * M 1 1 * M 2 3 - M 0 0 * M 1 3 * M 2 1 - M 0 1 * M 1 0 * M 2 3 + M 0 1 * M 1 3 * M 2 0 + M 0 3 * M 1 0 * M 2 1 - M 0 3 * M 1 1 * M 2 0);
      -(M 1 0 * M 2 1 * M 3 2 - M 1 0 * M 2 2 * M 3 1 - M 1 1 * M 2 0 * M 3 2 + M 1 1 * M 2 2 * M 3 0 + M 1 2 * M 2 0 * M 3 1 - M 1 2 * M 2 1 * M 3 0), (M 0 0 * M 2 1 * M 3 2 - M 0 0 * M 2 2 * M 3 1 - M 0 1 * M 2 0 * M 3 2 + M 0 1 * M 2 2 * M 3 0 + M 0 2 * M 2 0 * M 3 1 - M 0 2 * M 2 1 * M 3 0), -(M 0 0 * M 1 1 * M 3 2 - M 0 0 * M 1 2 * M 3 1 - M 0 1 * M 1 0 * M 3 2 + M 0 1 * M 1 2 * M 3 0 + M 0 2 * M 1 0 * M 3 1 - M 0 2 * M 1 1 * M 3 0), (M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0)] := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix (n := 3) M i j, Matrix.det_fin_three]
  dsimp only [Matrix.submatrix]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.succAbove, Fin.lt_def, Fin.le_def,
      Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]

theorem adjugate_divergence_four
    (A : Coord → Fin 4 → Fin 4 → ℝ) (x : Coord)
    (hA : ∀ i j, DifferentiableAt ℝ (fun z ↦ A z i j) x)
    (hclosed : ∀ a i j, fderiv ℝ (fun z ↦ A z a j) x (Pi.single i 1) =
      fderiv ℝ (fun z ↦ A z a i) x (Pi.single j 1)) (a : Fin 4) :
    ∑ i : Fin 4, fderiv ℝ (fun z ↦ Matrix.adjugate (A z) i a) x (Pi.single i 1) = 0 := by
  simp_rw [adjugate_four_explicit]
  fin_cases a
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ (A z 1 1 * A z 2 2 * A z 3 3 - A z 1 1 * A z 2 3 * A z 3 2 - A z 1 2 * A z 2 1 * A z 3 3 + A z 1 2 * A z 2 3 * A z 3 1 + A z 1 3 * A z 2 1 * A z 3 2 - A z 1 3 * A z 2 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ -(A z 1 0 * A z 2 2 * A z 3 3 - A z 1 0 * A z 2 3 * A z 3 2 - A z 1 2 * A z 2 0 * A z 3 3 + A z 1 2 * A z 2 3 * A z 3 0 + A z 1 3 * A z 2 0 * A z 3 2 - A z 1 3 * A z 2 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ (A z 1 0 * A z 2 1 * A z 3 3 - A z 1 0 * A z 2 3 * A z 3 1 - A z 1 1 * A z 2 0 * A z 3 3 + A z 1 1 * A z 2 3 * A z 3 0 + A z 1 3 * A z 2 0 * A z 3 1 - A z 1 3 * A z 2 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ -(A z 1 0 * A z 2 1 * A z 3 2 - A z 1 0 * A z 2 2 * A z 3 1 - A z 1 1 * A z 2 0 * A z 3 2 + A z 1 1 * A z 2 2 * A z 3 0 + A z 1 2 * A z 2 0 * A z 3 1 - A z 1 2 * A z 2 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ -(A z 0 1 * A z 2 2 * A z 3 3 - A z 0 1 * A z 2 3 * A z 3 2 - A z 0 2 * A z 2 1 * A z 3 3 + A z 0 2 * A z 2 3 * A z 3 1 + A z 0 3 * A z 2 1 * A z 3 2 - A z 0 3 * A z 2 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 2 2 * A z 3 3 - A z 0 0 * A z 2 3 * A z 3 2 - A z 0 2 * A z 2 0 * A z 3 3 + A z 0 2 * A z 2 3 * A z 3 0 + A z 0 3 * A z 2 0 * A z 3 2 - A z 0 3 * A z 2 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 2 1 * A z 3 3 - A z 0 0 * A z 2 3 * A z 3 1 - A z 0 1 * A z 2 0 * A z 3 3 + A z 0 1 * A z 2 3 * A z 3 0 + A z 0 3 * A z 2 0 * A z 3 1 - A z 0 3 * A z 2 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 2 1 * A z 3 2 - A z 0 0 * A z 2 2 * A z 3 1 - A z 0 1 * A z 2 0 * A z 3 2 + A z 0 1 * A z 2 2 * A z 3 0 + A z 0 2 * A z 2 0 * A z 3 1 - A z 0 2 * A z 2 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ (A z 0 1 * A z 1 2 * A z 3 3 - A z 0 1 * A z 1 3 * A z 3 2 - A z 0 2 * A z 1 1 * A z 3 3 + A z 0 2 * A z 1 3 * A z 3 1 + A z 0 3 * A z 1 1 * A z 3 2 - A z 0 3 * A z 1 2 * A z 3 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 2 * A z 3 3 - A z 0 0 * A z 1 3 * A z 3 2 - A z 0 2 * A z 1 0 * A z 3 3 + A z 0 2 * A z 1 3 * A z 3 0 + A z 0 3 * A z 1 0 * A z 3 2 - A z 0 3 * A z 1 2 * A z 3 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 1 * A z 3 3 - A z 0 0 * A z 1 3 * A z 3 1 - A z 0 1 * A z 1 0 * A z 3 3 + A z 0 1 * A z 1 3 * A z 3 0 + A z 0 3 * A z 1 0 * A z 3 1 - A z 0 3 * A z 1 1 * A z 3 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 1 * A z 3 2 - A z 0 0 * A z 1 2 * A z 3 1 - A z 0 1 * A z 1 0 * A z 3 2 + A z 0 1 * A z 1 2 * A z 3 0 + A z 0 2 * A z 1 0 * A z 3 1 - A z 0 2 * A z 1 1 * A z 3 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 3 1 0, hclosed 3 2 0, hclosed 3 2 1, hclosed 3 3 0, hclosed 3 3 1, hclosed 3 3 2]
    ring
  · simp only [Fin.sum_univ_succ]
    change fderiv ℝ (fun z ↦ -(A z 0 1 * A z 1 2 * A z 2 3 - A z 0 1 * A z 1 3 * A z 2 2 - A z 0 2 * A z 1 1 * A z 2 3 + A z 0 2 * A z 1 3 * A z 2 1 + A z 0 3 * A z 1 1 * A z 2 2 - A z 0 3 * A z 1 2 * A z 2 1)) x (Pi.single 0 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 2 * A z 2 3 - A z 0 0 * A z 1 3 * A z 2 2 - A z 0 2 * A z 1 0 * A z 2 3 + A z 0 2 * A z 1 3 * A z 2 0 + A z 0 3 * A z 1 0 * A z 2 2 - A z 0 3 * A z 1 2 * A z 2 0)) x (Pi.single 1 1) + (fderiv ℝ (fun z ↦ -(A z 0 0 * A z 1 1 * A z 2 3 - A z 0 0 * A z 1 3 * A z 2 1 - A z 0 1 * A z 1 0 * A z 2 3 + A z 0 1 * A z 1 3 * A z 2 0 + A z 0 3 * A z 1 0 * A z 2 1 - A z 0 3 * A z 1 1 * A z 2 0)) x (Pi.single 2 1) + (fderiv ℝ (fun z ↦ (A z 0 0 * A z 1 1 * A z 2 2 - A z 0 0 * A z 1 2 * A z 2 1 - A z 0 1 * A z 1 0 * A z 2 2 + A z 0 1 * A z 1 2 * A z 2 0 + A z 0 2 * A z 1 0 * A z 2 1 - A z 0 2 * A z 1 1 * A z 2 0)) x (Pi.single 3 1) + 0))) = 0
    simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
      fderiv_fun_neg, add_apply, sub_apply,
      smul_apply, neg_apply, smul_eq_mul]
    simp only [hclosed 0 1 0, hclosed 0 2 0, hclosed 0 2 1, hclosed 0 3 0, hclosed 0 3 1, hclosed 0 3 2, hclosed 1 1 0, hclosed 1 2 0, hclosed 1 2 1, hclosed 1 3 0, hclosed 1 3 1, hclosed 1 3 2, hclosed 2 1 0, hclosed 2 2 0, hclosed 2 2 1, hclosed 2 3 0, hclosed 2 3 1, hclosed 2 3 2]
    ring

end
end Yau.Geometry

end OAI
