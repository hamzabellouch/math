import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCWBoundary
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation
namespace CWPrimitiveDegeneration

open Polynomial

theorem outerMap_degree (output input : Fin 3) :
    (CWBoundary.outerMap (X : Polynomial ℂ) output input).degree ≤ 1 := by
  by_cases heq : input = output
  · rw [CWBoundary.outerMap, CWBoundary.diagonalMap, ite_eq_left heq]
    by_cases hone : output = 1 <;> simp [CWBoundary.outerWeight, hone]
  · simp [CWBoundary.outerMap, CWBoundary.diagonalMap, heq]

theorem middleMap_degree (output input : Fin 3) :
    (CWBoundary.middleMap (X : Polynomial ℂ) output input).degree ≤ 1 := by
  by_cases heq : input = output
  · rw [CWBoundary.middleMap, CWBoundary.diagonalMap, ite_eq_left heq]
    by_cases hone : output = 1 <;> simp [CWBoundary.middleWeight, hone]
  · simp [CWBoundary.middleMap, CWBoundary.diagonalMap, heq]

def boundary : Tensor.PolynomialRestrictionDegeneration
    CoppersmithWinograd.tensor CWBoundary.tensor 1 1 1 1 where
  leftMap := CWBoundary.outerMap X
  middleMap := CWBoundary.middleMap X
  rightMap := CWBoundary.outerMap X
  left_degree := outerMap_degree
  middle_degree := middleMap_degree
  right_degree := outerMap_degree
  vanishes := by
    intro x y z j hj
    have hjzero : j = 0 := by omega
    subst j
    change (CWBoundary.scalingPolynomial x y z).coeff 0 = 0
    simp [CWBoundary.scalingPolynomial_coeff]
  leading := CWBoundary.scalingPolynomial_leading

@[simp] theorem boundary_basePolynomial :
    boundary.basePolynomial = CWBoundary.scalingPolynomial := rfl

theorem five_initial_coefficients :
    CWBoundary.tensor 0 0 2 = 1 ∧ CWBoundary.tensor 0 1 1 = 1 ∧
    CWBoundary.tensor 2 0 0 = 1 ∧ CWBoundary.tensor 1 1 0 = 1 ∧
    CWBoundary.tensor 0 2 0 = 1 := by
  norm_num [CWBoundary.tensor, CoppersmithWinograd.tensor]

def boundaryApproximation : Tensor.PolynomialApproximation CWBoundary.tensor 3 5 15 :=
  boundary.compose CoppersmithWinograd.approximation

@[simp] theorem boundaryApproximation_polynomial :
    boundaryApproximation.polynomial =
      Tensor.restrict (CWBoundary.outerMap X) (CWBoundary.middleMap X)
        (CWBoundary.outerMap X)
        (fun x y z => Polynomial.expand ℂ 2 (CoppersmithWinograd.polynomial x y z)) := rfl

theorem boundaryApproximation_polynomial_apply (x y z : Fin 3) :
    boundaryApproximation.polynomial x y z =
      if x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
          x.val + y.val + z.val = 6 then
        X ^ (2 * (x.val + y.val + z.val) + CWBoundary.weight x y z) else 0 := by
  rw [boundaryApproximation_polynomial]
  change Tensor.restrict
    (CWBoundary.diagonalMap (CWBoundary.outerWeight X))
    (CWBoundary.diagonalMap (CWBoundary.middleWeight X))
    (CWBoundary.diagonalMap (CWBoundary.outerWeight X))
    (fun x y z => Polynomial.expand ℂ 2 (CoppersmithWinograd.polynomial x y z))
    x y z = _
  rw [CWBoundary.restrict_diagonal_apply, CoppersmithWinograd.polynomial_apply]
  by_cases hs : x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
      x.val + y.val + z.val = 6
  · simp only [ite_eq_left hs, map_pow, Polynomial.expand_X, ← pow_mul]
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> by_cases hz : z = 1 <;>
      simp [CWBoundary.outerWeight, CWBoundary.middleWeight, CWBoundary.weight,
        hx, hy, hz, pow_add] <;> ring
  · simp [hs]

theorem boundaryApproximation_leading (x y z : Fin 3) :
    (boundaryApproximation.polynomial x y z).coeff 5 = CWBoundary.tensor x y z :=
  boundaryApproximation.leading x y z

theorem boundary_rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power CWBoundary.tensor n) ((15 * n + 1) * 3 ^ n) :=
  boundaryApproximation.rank_power n

theorem cw_cyclic : Tensor.cyclic CoppersmithWinograd.tensor =
    CoppersmithWinograd.tensor := by
  funext x y z
  simp [Tensor.cyclic, CoppersmithWinograd.tensor,
    Nat.add_comm, Nat.add_left_comm]

def cyclicBoundary : Tensor.PolynomialRestrictionDegeneration
    CoppersmithWinograd.tensor (Tensor.cyclic CWBoundary.tensor) 1 1 1 1 where
  leftMap := boundary.cyclic.leftMap
  middleMap := boundary.cyclic.middleMap
  rightMap := boundary.cyclic.rightMap
  left_degree := boundary.cyclic.left_degree
  middle_degree := boundary.cyclic.middle_degree
  right_degree := boundary.cyclic.right_degree
  vanishes := by
    intro x y z j hj
    simpa only [cw_cyclic] using boundary.cyclic.vanishes x y z j hj
  leading := by
    intro x y z
    simpa only [cw_cyclic] using boundary.cyclic.leading x y z

def twiceCyclicBoundary : Tensor.PolynomialRestrictionDegeneration
    CoppersmithWinograd.tensor (Tensor.cyclic (Tensor.cyclic CWBoundary.tensor))
      1 1 1 1 where
  leftMap := cyclicBoundary.cyclic.leftMap
  middleMap := cyclicBoundary.cyclic.middleMap
  rightMap := cyclicBoundary.cyclic.rightMap
  left_degree := cyclicBoundary.cyclic.left_degree
  middle_degree := cyclicBoundary.cyclic.middle_degree
  right_degree := cyclicBoundary.cyclic.right_degree
  vanishes := by
    intro x y z j hj
    simpa only [cw_cyclic] using cyclicBoundary.cyclic.vanishes x y z j hj
  leading := by
    intro x y z
    simpa only [cw_cyclic] using cyclicBoundary.cyclic.leading x y z

theorem cyclicBoundary_deleted : Tensor.cyclic CWBoundary.tensor 0 1 1 = 0 := by
  exact CWBoundary.tensor_deleted

theorem twiceCyclicBoundary_deleted :
    Tensor.cyclic (Tensor.cyclic CWBoundary.tensor) 1 1 0 = 0 := by
  exact CWBoundary.tensor_deleted

def cyclicBoundaryApproximation :
    Tensor.PolynomialApproximation (Tensor.cyclic CWBoundary.tensor) 3 5 15 :=
  cyclicBoundary.compose CoppersmithWinograd.approximation

def twiceCyclicBoundaryApproximation :
    Tensor.PolynomialApproximation (Tensor.cyclic (Tensor.cyclic CWBoundary.tensor))
      3 5 15 :=
  twiceCyclicBoundary.compose CoppersmithWinograd.approximation

@[simp] theorem cyclicBoundaryApproximation_polynomial :
    cyclicBoundaryApproximation.polynomial =
      Tensor.restrict (CWBoundary.middleMap X) (CWBoundary.outerMap X)
        (CWBoundary.outerMap X)
        (fun x y z => Polynomial.expand ℂ 2 (CoppersmithWinograd.polynomial x y z)) := rfl

@[simp] theorem twiceCyclicBoundaryApproximation_polynomial :
    twiceCyclicBoundaryApproximation.polynomial =
      Tensor.restrict (CWBoundary.outerMap X) (CWBoundary.outerMap X)
        (CWBoundary.middleMap X)
        (fun x y z => Polynomial.expand ℂ 2 (CoppersmithWinograd.polynomial x y z)) := rfl

end CWPrimitiveDegeneration
end MatrixMultiplication.Foundation

end

end OAI
