import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMinor
import Mathlib.Topology.Algebra.Module.Determinant

namespace OAI

/-! # A polynomial minor is the determinant of the actual slice derivative -/

noncomputable section

namespace PolycyclicRecognition

open MvPolynomial Matrix
open scoped BigOperators

def appendParameterLinear (n k : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + k) → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.addCases
    (fun j => ContinuousLinearMap.proj j) (fun _ => 0) i)

theorem appendParameterLinear_apply (n k : ℕ) (v : Fin n → ℝ) :
    appendParameterLinear n k v = Fin.append v 0 := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [appendParameterLinear]

theorem hasFDerivAt_finAppend {n k : ℕ} (v : Fin n → ℝ) (z : Fin k → ℝ) :
    HasFDerivAt (fun w => Fin.append w z) (appendParameterLinear n k) v := by
  convert (appendParameterLinear n k).hasFDerivAt.add_const (Fin.append 0 z) using 1
  ext w i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [appendParameterLinear_apply]

def polynomialSliceDifferential {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.pi (fun i => polynomialDifferential (p i) (Fin.append v z))).comp
    (appendParameterLinear n k)

theorem hasFDerivAt_polynomialSlice {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    HasFDerivAt (fun w i => MvPolynomial.eval (Fin.append w z) (p i))
      (polynomialSliceDifferential p v z) v := by
  exact (hasFDerivAt_pi.mpr (fun i => hasFDerivAt_mvPolynomial_eval (p i) (Fin.append v z))).comp v
    (hasFDerivAt_finAppend v z)

theorem eval_polynomialJacobianMinor {n k : ℕ}
    (p : Fin n → MvPolynomial (Fin (n + k)) ℝ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
    MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor p) =
      (polynomialSliceDifferential p v z).det := by
  classical
  rw [polynomialJacobianMinor, RingHom.map_det]
  change _ = (polynomialSliceDifferential p v z).toLinearMap.det
  rw [← LinearMap.det_toMatrix']
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change MvPolynomial.eval (Fin.append v z) (pderiv (Fin.castAdd k j) (p i)) =
    polynomialDifferential (p i) (Fin.append v z) (appendParameterLinear n k (Pi.single j 1))
  have he : appendParameterLinear n k (Pi.single j 1) = Pi.single (Fin.castAdd k j) 1 := by
    rw [appendParameterLinear_apply]
    ext a
    refine Fin.addCases ?_ ?_ a <;> intro b <;> simp [Pi.single_apply]
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hh
    omega
  rw [he, polynomialDifferential_basis]

end PolycyclicRecognition

end

end OAI
