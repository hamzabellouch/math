import OAI.Geometry.EinsteinFour.TraceHessian

namespace OAI

/-! The explicit trace lift is the actual adjoint on the Bianchi subspace. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

private def referenceShape : Shape where
  s := ![-1, -1, 2]
  trace := by norm_num [Fin.sum_univ_succ]
  square := by norm_num [Fin.sum_univ_succ]

/-- Pairing of one outer-derivative slice of the lift with an actual Bianchi
matrix of four-vectors. -/
def liftSlicePairing (M : Mat) (i : Fin 4) (Z : Tensor) : ℝ :=
  ∑ a, ∑ b, ∑ j, traceLift M i j a b * Z.matrix a b j

/-- Pairing with the corresponding derivative component of the gradient. -/
def derivativePairing (M : Mat) (i : Fin 4) (Z : Tensor) : ℝ :=
  ∑ a, ∑ b, M a b * Z.matrix a b i

private theorem traceLift_adjoint_parameters_0
    (a b c d e : ℝ) (p k l : Vec) :
    liftSlicePairing (ofCoordinates a b c d e) 0 (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) 0 (parameters referenceShape p k l) := by
  simp [liftSlicePairing, derivativePairing, traceLift,
    quaternionMatrix, parameters, Tensor.matrix,
    referenceShape, difference, next, previous, quaternion, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem traceLift_adjoint_parameters_1
    (a b c d e : ℝ) (p k l : Vec) :
    liftSlicePairing (ofCoordinates a b c d e) 1 (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) 1 (parameters referenceShape p k l) := by
  simp [liftSlicePairing, derivativePairing, traceLift,
    quaternionMatrix, parameters, Tensor.matrix,
    referenceShape, difference, next, previous, quaternion, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem traceLift_adjoint_parameters_2
    (a b c d e : ℝ) (p k l : Vec) :
    liftSlicePairing (ofCoordinates a b c d e) 2 (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) 2 (parameters referenceShape p k l) := by
  simp [liftSlicePairing, derivativePairing, traceLift,
    quaternionMatrix, parameters, Tensor.matrix,
    referenceShape, difference, next, previous, quaternion, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem traceLift_adjoint_parameters_3
    (a b c d e : ℝ) (p k l : Vec) :
    liftSlicePairing (ofCoordinates a b c d e) 3 (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) 3 (parameters referenceShape p k l) := by
  simp [liftSlicePairing, derivativePairing, traceLift,
    quaternionMatrix, parameters, Tensor.matrix,
    referenceShape, difference, next, previous, quaternion, Fin.sum_univ_succ]
  all_goals (simp [ofCoordinates]; ring)

private theorem traceLift_adjoint_parameters
    (a b c d e : ℝ) (p k l : Vec) (i : Fin 4) :
    liftSlicePairing (ofCoordinates a b c d e) i (parameters referenceShape p k l) =
      derivativePairing (ofCoordinates a b c d e) i (parameters referenceShape p k l) := by
  fin_cases i
  · exact traceLift_adjoint_parameters_0 _ _ _ _ _ _ _ _
  · exact traceLift_adjoint_parameters_1 _ _ _ _ _ _ _ _
  · exact traceLift_adjoint_parameters_2 _ _ _ _ _ _ _ _
  · exact traceLift_adjoint_parameters_3 _ _ _ _ _ _ _ _

/-- The adjoint identity holds for every actual symmetric trace-free Bianchi
gradient; no projection identity is a premise. -/
theorem traceLift_adjoint_slice (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) (i : Fin 4) :
    liftSlicePairing M i Z = derivativePairing M i Z := by
  rw [← coordinates_eq M hs ht, ← parameters_reconstruction referenceShape Z hz hb]
  exact traceLift_adjoint_parameters _ _ _ _ _ _ _ _ i

/-- Trace of the two derivative slots, for a family of Bianchi gradients. -/
def slicesTrace (Z : Fin 4 → Tensor) : Mat := fun a b => ∑ i, (Z i).matrix a b i

/-- The global finite-dimensional adjoint identity for the restricted trace. -/
theorem traceLift_adjoint (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (Z : Fin 4 → Tensor) (hz : ∀ i, (Z i).traceFree) (hb : ∀ i, (Z i).bianchi) :
    (∑ i, liftSlicePairing M i (Z i)) = ∑ a, ∑ b, M a b * slicesTrace Z a b := by
  have h (i : Fin 4) := traceLift_adjoint_slice M hs ht (Z i) (hz i) (hb i) i
  simp_rw [h]
  unfold derivativePairing slicesTrace
  simp only [Fin.sum_univ_succ]
  ring

/-- The actual four-index array associated to differentiated Bianchi tensors. -/
def slicesHessian (Z : Fin 4 → Tensor) : Hessian :=
  fun i j a b => (Z i).matrix a b j

/-- Frobenius pairing on all four tensor slots. -/
def hessianPairing (X Y : Hessian) : ℝ :=
  ∑ a, ∑ b, ∑ i, ∑ j, X i j a b * Y i j a b

theorem hessianPairing_self (X : Hessian) :
    hessianPairing X X = hessianNormSq X := by
  simp only [hessianPairing, hessianNormSq, pow_two]

theorem hessianPairing_comm (X Y : Hessian) :
    hessianPairing X Y = hessianPairing Y X := by
  simp only [hessianPairing, mul_comm]

theorem hessianNormSq_sub (X Y : Hessian) :
    hessianNormSq (X - Y) = hessianNormSq X - 2 * hessianPairing X Y +
      hessianNormSq Y := by
  have h (i j : Fin 4) (a b : Fin 3) :
      (X i j a b - Y i j a b) ^ 2 = X i j a b ^ 2 -
        2 * (X i j a b * Y i j a b) + Y i j a b ^ 2 := by ring
  change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b - Y i j a b) ^ 2) = _
  simp only [hessianNormSq, hessianPairing, h, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The trace component pairs with an arbitrary constrained Hessian only
through its trace. This includes the prescribed skew part of the Hessian. -/
theorem traceComponent_pairing (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (Z : Fin 4 → Tensor) (hz : ∀ i, (Z i).traceFree) (hb : ∀ i, (Z i).bianchi) :
    hessianPairing (traceComponent M) (slicesHessian Z) =
      (5 / 12 : ℝ) * ∑ a, ∑ b, M a b * slicesTrace Z a b := by
  have h := traceLift_adjoint M hs ht Z hz hb
  change (∑ a, ∑ b, ∑ i, ∑ j,
    ((5 / 12 : ℝ) * traceLift M i j a b) * (Z i).matrix a b j) = _
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [← h]
  congr 1
  unfold liftSlicePairing
  simp only [Fin.sum_univ_succ]
  ring

/-- Exact subtraction of the whole prescribed trace component. -/
theorem traceComponent_subtraction (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (Z : Fin 4 → Tensor) (hz : ∀ i, (Z i).traceFree) (hb : ∀ i, (Z i).bianchi)
    (htrace : slicesTrace Z = M) :
    hessianNormSq (slicesHessian Z - traceComponent M) =
      hessianNormSq (slicesHessian Z) - (5 / 12) * matrixNormSq M := by
  rw [hessianNormSq_sub, hessianPairing_comm, traceComponent_pairing M hs ht Z hz hb,
    htrace, traceComponent_norm M hs ht]
  have h : (∑ a, ∑ b, M a b * M a b) = matrixNormSq M := by
    simp only [matrixNormSq, pow_two]
  rw [h]
  ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
