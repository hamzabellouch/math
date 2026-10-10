import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialKernelExecution

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.ExecutionApproximation

open MatrixMultiplication.Foundation
open Tensor LocalMaps PolynomialLocalConstruction PolynomialKernelExecution

variable {X Y Z Prefix PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)

theorem polynomial_substitution (original : Tensor ℂ X Y Z) :
    fiberTransform E.leftMap E.middleMap E.rightMap
      (fun x y z => Polynomial.C (Tensor.product original E.auxiliary x y z)) =
      originalScale (fun x y z => Polynomial.C (original x y z))
        (kernel E.auxiliary E.leftMap E.middleMap E.rightMap) := by
  have h := fiberTransform_originalScale E.leftMap E.middleMap E.rightMap
    (fun x y z => Polynomial.C (original x y z))
    (fun x y z => Polynomial.C (E.auxiliary x.2 y.2 z.2))
  have hinput :
      (fun x y z => Polynomial.C (Tensor.product original E.auxiliary x y z)) =
        originalScale (fun x y z => Polynomial.C (original x y z))
          (fun x y z => Polynomial.C (E.auxiliary x.2 y.2 z.2)) := by
    funext x y z
    simp only [Tensor.product, originalScale, map_mul]
  rw [hinput]
  simpa only [kernel] using h

variable [Fintype X] [Fintype Y] [Fintype Z]

def degeneration (original : Tensor ℂ X Y Z)
    (supported : ∀ x y z, ¬ support x y z → original x y z = 0) :
    PolynomialRestrictionDegeneration (Tensor.product original E.auxiliary)
      (originalScale original E.value) E.order E.leftDegree E.middleDegree E.rightDegree := by
  classical
  refine {
    leftMap := fiberMatrix E.leftMap
    middleMap := fiberMatrix E.middleMap
    rightMap := fiberMatrix E.rightMap
    left_degree := ?_
    middle_degree := ?_
    right_degree := ?_
    vanishes := ?_
    leading := ?_
  }
  · intro x i
    by_cases h : x.1 = i.1
    · simpa only [fiberMatrix, ite_eq_left h] using E.left_degree x.1 x.2 i.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro y j
    by_cases h : y.1 = j.1
    · simpa only [fiberMatrix, ite_eq_left h] using E.middle_degree y.1 y.2 j.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro z k
    by_cases h : z.1 = k.1
    · simpa only [fiberMatrix, ite_eq_left h] using E.right_degree z.1 z.2 k.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro x y z j hj
    rw [← fiberTransform_eq_restrict, polynomial_substitution E original]
    simp only [originalScale, Polynomial.coeff_C_mul]
    by_cases hs : support x.1 y.1 z.1
    · rw [E.vanishes x y z hs j hj, mul_zero]
    · rw [supported x.1 y.1 z.1 hs, zero_mul]
  · intro x y z
    rw [← fiberTransform_eq_restrict, polynomial_substitution E original]
    simp only [originalScale, Polynomial.coeff_C_mul]
    by_cases hs : support x.1 y.1 z.1
    · rw [E.leading x y z hs]
    · rw [supported x.1 y.1 z.1 hs]
      simp only [zero_mul]

def approximation {original : Tensor ℂ X Y Z} {r d D : ℕ}
    (source : PolynomialApproximation original r d D)
    (supported : ∀ x y z, ¬ support x y z → original x y z = 0) :
    PolynomialApproximation (originalScale original E.value)
      (r * E.rankBound) (d * (E.order + 1) + E.order)
      (D * (E.order + 1) + E.leftDegree + E.middleDegree + E.rightDegree) := by
  have combined := source.productExact E.auxiliary E.rankBound E.auxiliary_rank
  exact (degeneration E original supported).compose combined

end MatrixMultiplication.ExecutionApproximation

end

end OAI
