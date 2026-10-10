import Mathlib
import OAI.Analysis.Conductivity.Flux.FiniteEndPhysicalTensor

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma contDiffAt_mat3_det {A : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) : ContDiffAt ℝ n (fun y => (A y).det) x := by
  simp_rw [Matrix.det_fin_three]
  have hc (i j : Fin 3) := contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j
  fun_prop

lemma contDiffAt_mat3_adjugate {A : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) : ContDiffAt ℝ n (fun y => (A y).adjugate) x := by
  simp_rw [Matrix.adjugate_fin_three]
  have hc (i j : Fin 3) := contDiffAt_pi.mp (contDiffAt_pi.mp hA i) j
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> norm_num only [Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons] <;> fun_prop

lemma contDiffAt_mat3_inv {A : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) (hd : (A x).det≠0) :
    ContDiffAt ℝ n (fun y => (A y)⁻¹) x := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv']
  exact ((contDiffAt_mat3_det hA).inv hd).smul (contDiffAt_mat3_adjugate hA)

lemma contDiffAt_mat3_transpose {A : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) : ContDiffAt ℝ n (fun y => (A y)ᵀ) x := by
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i))

lemma contDiffAt_mat3_mul {A B : Coord3 → Mat3} {x : Coord3} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B x) :
    ContDiffAt ℝ n (fun y => A y*B y) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum (fun k _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) k).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hB k) j))

lemma contDiff_faceRayAngle (w : ℝ) (j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (faceRayAngle w j) := by
  have h1 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun b : ℝ => Real.arctan (b/w)) :=
    Real.contDiff_arctan.comp (contDiff_id.div_const w)
  have h2 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun b : ℝ => Real.arctan (w*b)) :=
    Real.contDiff_arctan.comp (contDiff_const.mul contDiff_id)
  unfold faceRayAngle
  fin_cases j <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;> fun_prop

lemma contDiff_faceRayDensity (w : ℝ) (j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (faceRayDensity w j) := by
  have h1 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : ℝ => (1+(x/w)^2)⁻¹) :=
    (contDiff_const.add ((contDiff_id.div_const w).pow 2)).inv (fun x => by positivity)
  have h2 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x : ℝ => (1+(w*x)^2)⁻¹) :=
    (contDiff_const.add ((contDiff_const.mul contDiff_id).pow 2)).inv (fun x => by positivity)
  unfold faceRayDensity
  fin_cases j <;> dsimp <;> simp only [div_eq_mul_inv,one_mul] <;> fun_prop

lemma contDiff_sourceFaceAngles (i j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceFaceAngles i j) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases k
  · exact contDiff_apply _ _ _
  · exact contDiff_const.mul ((contDiff_faceRayAngle 1 i).comp (contDiff_apply _ _ 1))
  · exact contDiff_const.mul ((contDiff_faceRayAngle sourceRadialWidth j).comp (contDiff_apply _ _ 2))

lemma contDiff_sourceCollarJacobian (i j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceCollarJacobian i j) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  fin_cases a <;> fin_cases b <;>
    simp only [sourceCollarJacobian, sourceCollarRadius, squareFace, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] <;> fun_prop

lemma contDiff_sourceFaceAngleMatrix (i j : Fin 4) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (sourceFaceAngleMatrix i j) := by
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  by_cases hab : a=b
  · subst b
    fin_cases a <;> simp only [sourceFaceAngleMatrix,Matrix.diagonal_apply_eq]
    · exact contDiff_const
    · exact contDiff_const.mul ((contDiff_faceRayDensity 1 i).comp (contDiff_apply _ _ 1))
    · exact contDiff_const.mul ((contDiff_faceRayDensity sourceRadialWidth j).comp (contDiff_apply _ _ 2))
  · simp only [sourceFaceAngleMatrix,Matrix.diagonal_apply_ne _ hab]
    exact contDiff_const

lemma contDiffAt_sourceCartesianGradientMatrix (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (sourceCartesianGradientMatrix i j) x := by
  have hi := contDiffAt_mat3_inv (contDiffAt_mat3_transpose (contDiff_sourceCollarJacobian i j).contDiffAt)
    (by rw [Matrix.det_transpose]; exact sourceCollarJacobian_extended_ne_zero i j hx)
  exact contDiffAt_mat3_mul hi (contDiff_sourceFaceAngleMatrix i j).contDiffAt

lemma contDiffAt_attachedCartesianMatrix (a : ℝ) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (attachedCartesianMatrix a i j) x :=
  contDiffAt_mat3_mul (contDiffAt_sourceCartesianGradientMatrix i j hx) contDiffAt_const

lemma contDiffAt_sourceFlatDensity (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (sourceFlatDensity i j) x := by
  exact (contDiffAt_mat3_det (contDiff_sourceFaceAngleMatrix i j).contDiffAt).div
    ((contDiffAt_mat3_det (contDiff_sourceCollarJacobian i j).contDiffAt).abs
      (sourceCollarJacobian_extended_ne_zero i j hx))
    (abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx))

lemma contDiffAt_attachedVariableTensor {K : Coord3 → Mat3} {x : Coord3}
    (hK : ContDiffAt ℝ (↑(⊤:ℕ∞)) K x) {a : ℝ} (ha : a≠0) (i j : Fin 4)
    (hx : x∈sourceCollarOpenBox) :
    ContDiffAt ℝ (↑(⊤:ℕ∞)) (attachedVariableTensor K a i j) x := by
  have hi := contDiffAt_mat3_inv (contDiffAt_attachedCartesianMatrix a i j (sourceCollarOpenBox_subset hx))
    (attachedCartesianMatrix_det_ne_zero ha i j (sourceCollarOpenBox_subset hx))
  exact (contDiffAt_const.mul (contDiffAt_sourceFlatDensity i j (sourceCollarOpenBox_subset hx))).smul
    (contDiffAt_mat3_mul (contDiffAt_mat3_mul (contDiffAt_mat3_transpose hi) hK) hi)

end ScalarConductivity

end
end

end OAI
