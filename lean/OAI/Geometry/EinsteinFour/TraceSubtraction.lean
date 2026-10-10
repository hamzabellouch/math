import OAI.Geometry.EinsteinFour.TraceAction
import OAI.Geometry.EinsteinFour.BianchiSlices
import OAI.Geometry.EinsteinFour.TraceDecomposition

namespace OAI

/-! Exact subtraction of the prescribed trace from the weighted square. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The restricted trace adjoint pairs with any actual inner-Bianchi array,
including an unsymmetrized weight derivative. -/
theorem traceComponent_pairing_hessian (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (X : Hessian) (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) :
    hessianPairing (traceComponent M) X =
      (5 / 12 : ℝ) * matrixPairing M (hessianTrace X) := by
  have hx : slicesHessian (innerSlice X) = X := by
    funext i j a b
    change (innerSlice X i).matrix a b j = X i j a b
    rw [innerSlice_matrix X i (fun j => (hmatrix i j).1)]
  have htr : slicesTrace (innerSlice X) = hessianTrace X := by
    ext a b
    change (∑ i, (innerSlice X i).matrix a b i) = ∑ i, X i i a b
    apply Finset.sum_congr rfl
    intro i _
    rw [innerSlice_matrix X i (fun j => (hmatrix i j).1)]
  calc
    _ = hessianPairing (traceComponent M) (slicesHessian (innerSlice X)) := by rw [hx]
    _ = _ := by
      rw [traceComponent_pairing M hs ht (innerSlice X)
        (fun i => innerSlice_traceFree X i (fun j => (hmatrix i j).2))
        (fun i => innerSlice_bianchi X i (fun j => (hmatrix i j).1) (hbianchi i)), htr]
      rfl

/-- The weight derivative keeps the genuine inner Bianchi constraints. -/
theorem weightTensor_matrix_bianchi (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∀ i j, symmetric (weightTensor a Z i j) ∧ traceFree (weightTensor a Z i j)) ∧
      (∀ i r, divergence (weightTensor a Z) i r = 0) := by
  constructor
  · intro i j
    constructor
    · intro b c
      change a i * Z.matrix b c j = a i * Z.matrix c b j
      rw [Z.matrix_symmetric b c]
    · have h := congrArg (fun z : Vec => z j) hz
      simp [Fin.sum_univ_three] at h
      change (∑ b, a i * Z.matrix b b j) = 0
      simp only [Fin.sum_univ_three]
      change a i * Z.diagonal 0 j + a i * Z.diagonal 1 j +
        a i * Z.diagonal 2 j = 0
      linear_combination a i * h
  · intro i r
    have h (s : Fin 3) :
        (WithLp.toLp 2 (fun j => weightTensor a Z i j s r) : Vec) =
          a i • Z.matrix s r := by
      ext j
      rfl
    simp only [divergence, h, quaternion_smul, ← Finset.smul_sum,
      ← Tensor.divergence_eq_sum, hb r, smul_zero]

/-- Trace of the unsymmetrized weight tensor is contraction with its real
outer derivative vector. -/
theorem weightTensor_trace (a : Vec) (Z : Tensor) :
    hessianTrace (weightTensor a Z) = fun b c => inner ℝ a (Z.matrix b c) := by
  ext b c
  simp [hessianTrace, weightTensor, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_four]
  ring

def traceCurvatureBlock (t : Fin 3 → ℝ) (M : Mat) : Mat :=
  (4 : ℝ) • M - diagonalCurvatureAction t M

theorem traceCurvatureBlock_symmetric (t : Fin 3 → ℝ) (M : Mat)
    (hs : symmetric M) : symmetric (traceCurvatureBlock t M) := by
  intro a b
  change 4 * M a b - diagonalCurvatureAction t M a b =
    4 * M b a - diagonalCurvatureAction t M b a
  unfold diagonalCurvatureAction
  rw [hs a b]
  by_cases hab : a = b
  · subst b
    rfl
  · simp only [hab, Ne.symm hab, ite_false]
    ring

theorem traceCurvatureBlock_traceFree (t : Fin 3 → ℝ) (M : Mat)
    (ht : traceFree M) : traceFree (traceCurvatureBlock t M) := by
  have h := ht
  simp only [traceFree, Fin.sum_univ_three] at h
  simp only [traceFree, traceCurvatureBlock, diagonalCurvatureAction,
    Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ite_true]
  linear_combination 4 * h

/-- The curvature action of the trace component pairs through the actual
Hessian trace, with the full skew part retained. -/
theorem traceComponent_curvaturePairing (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (M : Mat) (hsM : symmetric M) (htM : traceFree M)
    (X : Hessian) (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) :
    curvaturePairing t u (traceComponent M) X =
      (5 / 12 : ℝ) * matrixPairing (traceCurvatureBlock t M) (hessianTrace X) := by
  rw [traceComponent_curvatureAction t u ht M hsM htM]
  exact traceComponent_pairing_hessian (traceCurvatureBlock t M)
    (traceCurvatureBlock_symmetric t M hsM) (traceCurvatureBlock_traceFree t M htM)
    X hmatrix hbianchi

/-- The mixed trace pairing equals its self pairing when the trace is prescribed. -/
theorem prescribed_trace_curvaturePairing (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (M : Mat) (hsM : symmetric M) (htM : traceFree M)
    (X : Hessian) (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) :
    curvaturePairing t u X (traceComponent M) =
      curvaturePairing t u (traceComponent M) (traceComponent M) := by
  rw [curvaturePairing_comm t u X,
    traceComponent_curvaturePairing t u ht M hsM htM X hmatrix hbianchi,
    traceComponent_curvaturePairing t u ht M hsM htM (traceComponent M)
      (fun i j => ⟨traceComponent_symmetric M hsM htM i j,
        traceComponent_traceFree M hsM htM i j⟩)
      (traceComponent_divergence M hsM htM), htrace, trace_traceComponent]

/-- Both trace subtractions in the weighted Hessian square are exact. In
particular, the mixed term uses the full unsymmetrized weight tensor. -/
theorem weighted_trace_subtraction (t u : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (M : Mat) (hsM : symmetric M) (htM : traceFree M)
    (X L : Hessian) (hmatrix : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hbianchi : ∀ i r, divergence X i r = 0) (htrace : hessianTrace X = M) (m : ℝ) :
    m * curvaturePairing t u (X - traceComponent M) (X - traceComponent M) +
        curvaturePairing t u (X - traceComponent M) L =
      m * curvaturePairing t u X X + curvaturePairing t u X L -
        m * curvaturePairing t u (traceComponent M) (traceComponent M) -
          curvaturePairing t u (traceComponent M) L := by
  have hx := prescribed_trace_curvaturePairing t u ht M hsM htM X hmatrix hbianchi htrace
  have hsub : X - traceComponent M = X + (-1 : ℝ) • traceComponent M := by module
  rw [hsub]
  simp only [curvaturePairing_add_left, curvaturePairing_add_right,
    curvaturePairing_smul_left, curvaturePairing_smul_right]
  rw [curvaturePairing_comm t u (traceComponent M) X, hx]
  ring

end
end PositiveEinsteinFour.HighestHessian

end OAI
