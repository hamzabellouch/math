import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Matrix

namespace Problem336.Determinantal

variable {V E : Type*} [Fintype V] [finiteEdges : Fintype E]
variable [DecidableEq V] [decidableEdges : DecidableEq E]

def transferKernel (A : Matrix V E ℝ) : Matrix E E ℝ :=
  A.transpose * (A * A.transpose)⁻¹ * A

omit decidableEdges in
theorem transferKernel_transpose [DecidableEq E] (A : Matrix V E ℝ) :
    (transferKernel A).transpose = transferKernel A := by
  simp only [transferKernel, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv]
  simp only [Matrix.mul_assoc]

omit decidableEdges in
theorem transferKernel_idempotent [DecidableEq E] (A : Matrix V E ℝ)
    (hA : IsUnit (A * A.transpose).det) :
    transferKernel A * transferKernel A = transferKernel A := by
  unfold transferKernel
  calc
    A.transpose * (A * A.transpose)⁻¹ * A *
        (A.transpose * (A * A.transpose)⁻¹ * A) =
      A.transpose * ((A * A.transpose)⁻¹ * (A * A.transpose)) *
        (A * A.transpose)⁻¹ * A := by simp only [Matrix.mul_assoc]
    _ = A.transpose * (A * A.transpose)⁻¹ * A := by
      rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]

omit decidableEdges in
theorem projection_diagonal_eq_sum_sq [DecidableEq E] (K : Matrix E E ℝ)
    (hKsym : K.transpose = K) (hKproj : K * K = K) (e : E) :
    K e e = ∑ f, (K e f) ^ 2 := by
  have hsym (f : E) : K f e = K e f := by
    exact congrArg (fun M : Matrix E E ℝ => M e f) hKsym
  calc
    K e e = (K * K) e e := by rw [hKproj]
    _ = ∑ f, (K e f) ^ 2 := by
      simp only [Matrix.mul_apply, hsym, pow_two]

theorem projection_diagonal_mem_Icc (K : Matrix E E ℝ)
    (hKsym : K.transpose = K) (hKproj : K * K = K) (e : E) :
    K e e ∈ Set.Icc (0 : ℝ) 1 := by
  have hsum := projection_diagonal_eq_sum_sq K hKsym hKproj e
  have hnonneg : 0 ≤ K e e := by
    rw [hsum]
    exact Finset.sum_nonneg (fun f _ => sq_nonneg (K e f))
  have hsquare : (K e e) ^ 2 ≤ K e e := by
    calc
      (K e e) ^ 2 ≤ ∑ f, (K e f) ^ 2 :=
        Finset.single_le_sum (fun f _ => sq_nonneg (K e f)) (Finset.mem_univ e)
      _ = K e e := hsum.symm
  constructor
  · exact hnonneg
  · nlinarith

theorem transferKernel_diagonal_mem_Icc (A : Matrix V E ℝ)
    (hA : IsUnit (A * A.transpose).det) (e : E) :
    transferKernel A e e ∈ Set.Icc (0 : ℝ) 1 :=
  projection_diagonal_mem_Icc (transferKernel A)
    (transferKernel_transpose A) (transferKernel_idempotent A hA) e

def pairMatrix (K : Matrix E E ℝ) (e f : E) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![K e e, K e f; K f e, K f f]

omit finiteEdges decidableEdges in
theorem pairMatrix_det [Fintype E] [DecidableEq E] (K : Matrix E E ℝ) (e f : E) :
    (pairMatrix K e f).det = K e e * K f f - K e f * K f e := by
  exact Matrix.det_fin_two_of _ _ _ _

theorem determinantal_pair_covariance (K : Matrix E E ℝ)
    (hKsym : K.transpose = K) (e f : E) :
    (pairMatrix K e f).det - K e e * K f f = -(K e f) ^ 2 := by
  have hsym : K f e = K e f :=
    congrArg (fun M : Matrix E E ℝ => M e f) hKsym
  rw [pairMatrix_det, hsym]
  ring

theorem determinantal_pair_covariance_nonpos (K : Matrix E E ℝ)
    (hKsym : K.transpose = K) (e f : E) :
    (pairMatrix K e f).det - K e e * K f f ≤ 0 := by
  rw [determinantal_pair_covariance K hKsym e f]
  exact neg_nonpos.mpr (sq_nonneg _)

end Problem336.Determinantal

end

end OAI
