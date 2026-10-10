import Mathlib
import OAI.Analysis.AffineBernstein.LinearizedNormalization

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ConstantDetCalculus
open Filter Matrix
open scoped Topology

/-- Entrywise derivative of a genuine smooth matrix field. -/
def matrixDirDeriv {n m : ℕ} (v : Space n) (A : Space n → Matrix (Fin m) (Fin m) ℝ)
    (x : Space n) : Matrix (Fin m) (Fin m) ℝ := fun i j => dirDeriv v (fun y => A y i j) x

lemma dirDeriv_matrix_mul {n m : ℕ} {A B : Space n → Matrix (Fin m) (Fin m) ℝ}
    {x : Space n} (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) x) (v : Space n) :
    matrixDirDeriv v (fun y => A y*B y) x =
      matrixDirDeriv v A x*B x + A x*matrixDirDeriv v B x := by
  ext i j
  simp only [matrixDirDeriv,Matrix.mul_apply,Matrix.add_apply]
  rw [dirDeriv_sum (fun k y => A y i k*B y k j) (fun k => (hA i k).mul (hB k j))]
  simp only [dirDeriv_mul (hA _ _) (hB _ _),Finset.sum_add_distrib]

lemma dirDeriv_matrix_trace {n m : ℕ} {A : Space n → Matrix (Fin m) (Fin m) ℝ}
    {x : Space n} (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : Space n) :
    dirDeriv v (fun y => (A y).trace) x = (matrixDirDeriv v A x).trace := by
  exact dirDeriv_sum (fun i y => A y i i) (fun i => hA i i) v

lemma contDiff_inverseHessian_entry {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) (i j : Fin n) :
    ContDiff ℝ ∞ (fun y => (hessian u y)⁻¹ i j) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_inverse_matrix_entry_param
    (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => contDiffAt_hessian_entry hu.contDiffAt i j)
    (hp x).det_pos.ne' i j

lemma contDiff_hessian_entry_global {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (i j : Fin n) : ContDiff ℝ ∞ (fun y => hessian u y i j) := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => contDiffAt_hessian_entry hu.contDiffAt i j

lemma matrixDirDeriv_inverseHessian {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) (v x : Space n) :
    matrixDirDeriv v (fun y => (hessian u y)⁻¹) x =
      -((hessian u x)⁻¹ * matrixDirDeriv v (hessian u) x * (hessian u x)⁻¹) := by
  have he : (fun y => (hessian u y)⁻¹*hessian u y) = (fun _ => (1:Matrix (Fin n) (Fin n) ℝ)) := by
    funext y
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hp y).det_pos.ne')
  have hd := dirDeriv_matrix_mul
    (fun i j => (contDiff_inverseHessian_entry hu hp i j).differentiable (by simp) x)
    (fun i j => (contDiff_hessian_entry_global hu i j).differentiable (by simp) x) v
  rw [he] at hd
  have hz : matrixDirDeriv v (fun _ : Space n => (1:Matrix (Fin n) (Fin n) ℝ)) x=0 := by
    ext i j
    simp [matrixDirDeriv,dirDeriv]
  rw [hz] at hd
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M*(hessian u x)⁻¹) hd
  rw [Matrix.zero_mul,Matrix.add_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (hp x).det_pos.ne'),Matrix.mul_one] at hh
  exact eq_neg_of_add_eq_zero_left hh.symm

lemma hessian_dirDeriv_vector {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (v x : Space n) : hessian (dirDeriv v u) x = matrixDirDeriv v (hessian u) x := by
  ext i j
  exact third_dirDeriv_comm isOpen_univ hu.contDiffOn (mem_univ x) _ _ _

lemma hessian_dirDeriv_twice {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (v x : Space n) : hessian (dirDeriv v (dirDeriv v u)) x =
      matrixDirDeriv v (hessian (dirDeriv v u)) x :=
  hessian_dirDeriv_vector (contDiff_dirDeriv hu v) v x

lemma constant_det_trace_diff_zero {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) (v x : Space n) :
    ((hessian u x)⁻¹ * hessian (dirDeriv v u) x).trace=0 := by
  have he : logHessianDet u = fun _ => Real.log (hessian u 0).det := by
    funext y
    exact congrArg Real.log (hD y 0)
  have hh := dirDeriv_logHessianDet hu.contDiffAt (hp x) v
  rw [he] at hh
  have hz : dirDeriv v (fun _ : Space n => Real.log (hessian u 0).det) x=0 := by simp [dirDeriv]
  rw [hz] at hh
  rw [matrix_trace_pair _ _ (hessian_isSymm (contDiff_dirDeriv hu v).contDiffAt),hessian_dirDeriv_vector hu]
  exact hh.symm

lemma constant_det_directional_equation {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hD : ∀ x y, (hessian u x).det=(hessian u y).det) (v x : Space n) :
    inverseHessianTrace u (dirDeriv v (dirDeriv v u)) x =
      ((hessian u x)⁻¹ * hessian (dirDeriv v u) x *
       (hessian u x)⁻¹ * hessian (dirDeriv v u) x).trace := by
  let M := hessian (dirDeriv v u)
  have hM : ∀ i j, ContDiff ℝ ∞ (fun y => M y i j) :=
    contDiff_hessian_entry_global (contDiff_dirDeriv hu v)
  have hi := contDiff_inverseHessian_entry hu hp
  have he : (fun y => ((hessian u y)⁻¹*M y).trace) = fun _ => (0:ℝ) := by
    funext y
    exact constant_det_trace_diff_zero hu hp hD v y
  have hh := dirDeriv_matrix_trace (A := fun y => (hessian u y)⁻¹*M y)
    (fun i j => by
      simp only [Matrix.mul_apply]
      exact DifferentiableAt.fun_sum fun k _ => ((hi i k).differentiable (by simp) x).mul
        ((hM k j).differentiable (by simp) x)) v
  rw [he] at hh
  have hz : dirDeriv v (fun _ : Space n => (0:ℝ)) x=0 := by simp [dirDeriv]
  rw [hz,dirDeriv_matrix_mul (fun i j => (hi i j).differentiable (by simp) x)
    (fun i j => (hM i j).differentiable (by simp) x) v,
    matrixDirDeriv_inverseHessian hu hp,hessian_dirDeriv_vector hu v x |>.symm,
    ← hessian_dirDeriv_twice hu v x,Matrix.trace_add,Matrix.neg_mul,Matrix.trace_neg] at hh
  rw [inverseHessianTrace_eq_matrixTrace (contDiff_dirDeriv (contDiff_dirDeriv hu v) v)]
  dsimp only [M] at hh
  linarith

lemma directional_second_gradient {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (v x : Space n) (i : Fin n) :
    dirDeriv (coordinateVector n i) (dirDeriv v (dirDeriv v u)) x =
      (hessian (dirDeriv v u) x *ᵥ (fun j => v j)) i := by
  rw [dirDeriv_comm (contDiff_dirDeriv hu v).contDiffAt,
    dirDeriv_coordinate_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dirDeriv_comm (contDiff_dirDeriv hu v).contDiffAt]
  exact mul_comm _ _

end ConstantDetCalculus


end
end AffineBernstein
end

end OAI
