import OAI.Geometry.EinsteinFour.Bianchi
import Mathlib.LinearAlgebra.Matrix.Trace

namespace OAI

/-! # The prescribed trace component of the Bianchi Hessian

The arrays are real tensors. The lift is the explicit formula for the
restricted trace adjoint in Section 5; its Bianchi constraint, trace and
squared norm follow by direct calculation in the fixed quaternion frame. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
abbrev Hessian := Fin 4 → Fin 4 → Mat

def symmetric (M : Mat) : Prop := ∀ i j, M i j = M j i

def traceFree (M : Mat) : Prop := ∑ i, M i i = 0

def ofCoordinates (a b c d e : ℝ) : Mat :=
  ![![a, c, d], ![c, b, e], ![d, e, -a-b]]

theorem coordinates_eq (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    ofCoordinates (M 0 0) (M 1 1) (M 0 1) (M 0 2) (M 1 2) = M := by
  have hd : M 2 2 = -M 0 0 - M 1 1 := by
    have h := ht
    simp [traceFree, Fin.sum_univ_succ] at h
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ofCoordinates, hd]
  all_goals exact hs _ _

/-- Matrix coefficients of the same quaternion triple used for gradients. -/
def quaternionMatrix (s : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![![0, -1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 1, 0]],
    ![![0, 0, -1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, -1, 0, 0]],
    ![![0, 0, 0, -1], ![0, 0, -1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]]] s

theorem quaternionMatrix_apply (s : Fin 3) (q : Vec) (i : Fin 4) :
    ∑ j, quaternionMatrix s i j * q j = quaternion s q i := by
  fin_cases s <;> fin_cases i <;>
    simp [quaternionMatrix, quaternion, Fin.sum_univ_succ]

/-- Speed-two rotations on the self-dual matrix indices. -/
def rotation (s : Fin 3) : Mat :=
  ![![![0, 0, 0], ![0, 0, -2], ![0, 2, 0]],
    ![![0, 0, 2], ![0, 0, 0], ![-2, 0, 0]],
    ![![0, -2, 0], ![2, 0, 0], ![0, 0, 0]]] s

def matrixAction (s : Fin 3) (M : Mat) : Mat := fun a b =>
  ∑ c, (rotation s a c * M c b - M a c * rotation s c b)

@[simp] theorem matrixAction_coordinates_zero (a b c d e : ℝ) :
    matrixAction 0 (ofCoordinates a b c d e) =
      ofCoordinates 0 (-4 * e) (-2 * d) (2 * c) (2 * a + 4 * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAction, rotation, ofCoordinates, Fin.sum_univ_succ] <;> ring

@[simp] theorem matrixAction_coordinates_one (a b c d e : ℝ) :
    matrixAction 1 (ofCoordinates a b c d e) =
      ofCoordinates (4 * d) 0 (2 * e) (-4 * a - 2 * b) (-2 * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAction, rotation, ofCoordinates, Fin.sum_univ_succ] <;> ring

@[simp] theorem matrixAction_coordinates_two (a b c d e : ℝ) :
    matrixAction 2 (ofCoordinates a b c d e) =
      ofCoordinates (-4 * c) (4 * c) (2 * a - 2 * b) (-2 * e) (2 * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAction, rotation, ofCoordinates, Fin.sum_univ_succ] <;> ring

def matrixNormSq (M : Mat) : ℝ := ∑ a, ∑ b, M a b ^ 2

/-- The spin-two Casimir, computed on the actual symmetric trace-free matrix. -/
theorem matrixAction_casimir (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    (∑ a, ∑ b, ∑ s, matrixAction s M a b ^ 2) = 24 * matrixNormSq M := by
  rw [← coordinates_eq M hs ht]
  simp [matrixAction, rotation, ofCoordinates, matrixNormSq,
    Fin.sum_univ_succ]
  ring

/-- The explicit trace lift `3/5 δij S + 1/10 Σ I_s,ij Σ_s S`. -/
def traceLift (M : Mat) : Hessian := fun i j a b =>
  (if i = j then (3 / 5 : ℝ) * M a b else 0) +
    (1 / 10 : ℝ) * ∑ s, quaternionMatrix s i j * matrixAction s M a b

def hessianTrace (X : Hessian) : Mat := ∑ i, X i i

/-- Entry-first order is a permutation of the usual Frobenius sum. -/
def hessianNormSq (X : Hessian) : ℝ := ∑ a, ∑ b, ∑ i, ∑ j, X i j a b ^ 2

private theorem quaternionMatrix_diagonal (s : Fin 3) (i : Fin 4) :
    quaternionMatrix s i i = 0 := by
  fin_cases s <;> fin_cases i <;> rfl

/-- Trace followed by its lift gives exactly `12/5 Id`. -/
theorem trace_traceLift (M : Mat) : hessianTrace (traceLift M) = (12 / 5 : ℝ) • M := by
  ext a b
  simp [hessianTrace, traceLift, quaternionMatrix_diagonal, Fin.sum_univ_succ]
  ring

private theorem quaternion_square_sum (x : ℝ) (a : Fin 3 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      ((if i = j then (3 / 5 : ℝ) * x else 0) +
        (1 / 10 : ℝ) * ∑ s, quaternionMatrix s i j * a s) ^ 2) =
      (36 / 25) * x ^ 2 + (1 / 25) * ∑ s, a s ^ 2 := by
  simp [quaternionMatrix, Fin.sum_univ_succ]
  ring

/-- The norm of the explicit restricted trace lift. -/
theorem traceLift_norm (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    hessianNormSq (traceLift M) = (12 / 5) * matrixNormSq M := by
  have hentry (a b : Fin 3) :
      (∑ i : Fin 4, ∑ j : Fin 4, traceLift M i j a b ^ 2) =
        (36 / 25) * M a b ^ 2 + (1 / 25) * ∑ s, matrixAction s M a b ^ 2 := by
    simpa only [traceLift] using
      quaternion_square_sum (M a b) (fun s => matrixAction s M a b)
  unfold hessianNormSq
  simp_rw [hentry]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [matrixAction_casimir M hs ht]
  unfold matrixNormSq
  ring

/-- The actual Bianchi divergence of an inner-gradient slice of the lift. -/
def liftDivergence (M : Mat) (i : Fin 4) (r : Fin 3) : Vec :=
  ∑ s, quaternion s (WithLp.toLp 2 (fun j => traceLift M i j s r))

private theorem traceLift_bianchi_0_0 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 0 0 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_0_1 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 0 1 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_0_2 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 0 2 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_1_0 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 1 0 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_1_1 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 1 1 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_1_2 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 1 2 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_2_0 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 2 0 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_2_1 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 2 1 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_2_2 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 2 2 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_3_0 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 3 0 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_3_1 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 3 1 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

private theorem traceLift_bianchi_3_2 (a b c d e : ℝ) :
    liftDivergence (ofCoordinates a b c d e) 3 2 = 0 := by
  ext u
  fin_cases u <;>
    simp [liftDivergence, traceLift, quaternionMatrix, quaternion,
      Fin.sum_univ_succ]
  all_goals simp [ofCoordinates] <;> ring

/-- Every lifted trace belongs to the constrained inner-gradient space. -/
theorem traceLift_bianchi (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (i : Fin 4) (r : Fin 3) : liftDivergence M i r = 0 := by
  rw [← coordinates_eq M hs ht]
  fin_cases i <;> fin_cases r
  · exact traceLift_bianchi_0_0 _ _ _ _ _
  · exact traceLift_bianchi_0_1 _ _ _ _ _
  · exact traceLift_bianchi_0_2 _ _ _ _ _
  · exact traceLift_bianchi_1_0 _ _ _ _ _
  · exact traceLift_bianchi_1_1 _ _ _ _ _
  · exact traceLift_bianchi_1_2 _ _ _ _ _
  · exact traceLift_bianchi_2_0 _ _ _ _ _
  · exact traceLift_bianchi_2_1 _ _ _ _ _
  · exact traceLift_bianchi_2_2 _ _ _ _ _
  · exact traceLift_bianchi_3_0 _ _ _ _ _
  · exact traceLift_bianchi_3_1 _ _ _ _ _
  · exact traceLift_bianchi_3_2 _ _ _ _ _

/-- The prescribed trace component of an actual Hessian. -/
def traceComponent (M : Mat) : Hessian := fun i j => (5 / 12 : ℝ) • traceLift M i j

theorem trace_traceComponent (M : Mat) : hessianTrace (traceComponent M) = M := by
  unfold hessianTrace traceComponent
  rw [← Finset.smul_sum]
  change (5 / 12 : ℝ) • hessianTrace (traceLift M) = M
  rw [trace_traceLift]
  module

/-- The exact coefficient subtracted in the weighted Hessian identity. -/
theorem traceComponent_norm (M : Mat) (hs : symmetric M) (ht : traceFree M) :
    hessianNormSq (traceComponent M) = (5 / 12) * matrixNormSq M := by
  have hscale : hessianNormSq (traceComponent M) =
      (5 / 12 : ℝ) ^ 2 * hessianNormSq (traceLift M) := by
    simp [hessianNormSq, traceComponent, mul_pow, Finset.mul_sum]
  rw [hscale, traceLift_norm M hs ht]
  ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
