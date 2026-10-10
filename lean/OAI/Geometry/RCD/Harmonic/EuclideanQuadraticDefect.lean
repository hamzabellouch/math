import OAI.Geometry.RCD.Sobolev.EuclideanScalarLaplacian
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! # Derivatives of the quadratic defining an interior torsion test -/

open Set Metric MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff BigOperators
noncomputable section
namespace RegularPointCoordinates

def euclideanQuadraticDefect (n : ℕ) (R : ℝ) (x : Euclidean n) : ℝ := R^2-‖x‖^2

theorem euclideanQuadraticDefect_smooth (n : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (euclideanQuadraticDefect n R) :=
  contDiff_const.sub (contDiff_norm_sq ℝ)

theorem euclideanQuadraticDefect_fderiv {n : ℕ} (R : ℝ) (x v : Euclidean n) :
    fderiv ℝ (euclideanQuadraticDefect n R) x v = -2*inner ℝ x v := by
  have h := (hasFDerivAt_const (R^2) x).sub (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have he := congrArg (fun L : Euclidean n →L[ℝ] ℝ => L v) h.fderiv
  change fderiv ℝ (euclideanQuadraticDefect n R) x v=_ at he
  simp only [two_smul,zero_sub,neg_apply,add_apply,innerSL_apply_apply] at he
  linarith

theorem euclideanQuadraticDefect_basis {n : ℕ} (R : ℝ) (x : Euclidean n) (i : Fin n) :
    fderiv ℝ (euclideanQuadraticDefect n R) x (EuclideanSpace.single i 1) = -2*x i := by
  rw [euclideanQuadraticDefect_fderiv]
  simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul]

theorem euclideanQuadraticDefect_laplacian {n : ℕ} (R : ℝ) (x : Euclidean n) :
    (Δ (euclideanQuadraticDefect n R)) x= -2*(n:ℝ) := by
  rw [laplacian_eq_sum_second_directional ((euclideanQuadraticDefect_smooth n R).of_le (by simp))]
  have hd (i : Fin n) :
      fderiv ℝ (fun z => fderiv ℝ (euclideanQuadraticDefect n R) z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)= -2 := by
    simp_rw [euclideanQuadraticDefect_basis]
    have he : HasFDerivAt (fun z : Euclidean n => -2*z i) ((-2:ℝ) • EuclideanSpace.proj i) x :=
      ((EuclideanSpace.proj i) : Euclidean n →L[ℝ] ℝ).hasFDerivAt.const_mul (-2:ℝ)
    rw [he.fderiv]
    simp
  simp_rw [hd]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem euclideanQuadraticDefect_gradient_sq {n : ℕ} (R : ℝ) (x : Euclidean n) :
    (∑ i : Fin n, (fderiv ℝ (euclideanQuadraticDefect n R) x (EuclideanSpace.single i 1))^2)=
      4*‖x‖^2 := by
  simp_rw [euclideanQuadraticDefect_basis,mul_pow]
  rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
  norm_num

end RegularPointCoordinates

end

end OAI
