import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteCommutingOperatorAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialOperatorDetector
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteShiftProductAlgebra

namespace OAI

/-! # Polynomial relations among exterior shift operators -/

noncomputable section
namespace PolycyclicRecognition
open scoped Polynomial
variable (K : Type) [Field K]

def polynomialExteriorMul (n : ℕ) (p : K[X]) : Module.End K (⋀[K]^n K[X]) :=
  exteriorPower.map n (LinearMap.mulLeft K p)

theorem polynomialExteriorMul_commute (n : ℕ) (p q : K[X]) :
    Commute (polynomialExteriorMul K n p) (polynomialExteriorMul K n q) := by
  have h : (LinearMap.mulLeft K p).comp (LinearMap.mulLeft K q) =
      (LinearMap.mulLeft K q).comp (LinearMap.mulLeft K p) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [← mul_assoc, mul_comm p q, mul_assoc]
  change (exteriorPower.map n _).comp (exteriorPower.map n _) = _
  rw [← exteriorPower.map_comp, h, exteriorPower.map_comp]
  rfl

def polynomialExteriorShiftEvaluation (n k : ℕ) (c : Fin k → K) :
    MvPolynomial (Fin k) K →ₐ[K] Module.End K (⋀[K]^n K[X]) :=
  commutingOperatorEval K (fun i => polynomialExteriorMul K n (Polynomial.C (c i) - Polynomial.X))
    (fun _ _ => polynomialExteriorMul_commute K n _ _)

@[simp] theorem polynomialExteriorShiftEvaluation_X (n k : ℕ) (c : Fin k → K)
    (i : Fin k) : polynomialExteriorShiftEvaluation K n k c (MvPolynomial.X i) =
      polynomialExteriorMul K n (Polynomial.C (c i) - Polynomial.X) :=
  commutingOperatorEval_X K _ _ i

theorem polynomialExteriorMul_scalarDifference (n : ℕ) (c : K) (w : ⋀[K]^n K[X]) :
    polynomialExteriorDeterminant K n
      (polynomialExteriorMul K n (Polynomial.C c - Polynomial.X) w) =
        shiftProduct K n c * polynomialExteriorDeterminant K n w := by
  have he (i : Fin n) : Polynomial.aeval (MvPolynomial.X i)
      (Polynomial.C c - Polynomial.X) = MvPolynomial.C c - MvPolynomial.X i := by
    rw [map_sub, Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  refine (polynomialExteriorDeterminant_mul K n (Polynomial.C c - Polynomial.X) w).trans ?_
  exact congrArg (fun p => p * polynomialExteriorDeterminant K n w)
    (Finset.prod_congr rfl (fun i _ => he i))

/-- A relation among operators restricting to polynomial exterior shifts is
also a relation among the corresponding products in independent variables. -/
theorem polynomialExterior_relation_detected {W : Type} [AddCommGroup W] [Module K W]
    (n k : ℕ) (c : Fin k → K)
    (α : MvPolynomial (Fin k) K →ₐ[K] Module.End K W)
    (E : (⋀[K]^n K[X]) →ₗ[K] W) (hE : Function.Injective E)
    (hα : ∀ i w, E (polynomialExteriorMul K n (Polynomial.C (c i) - Polynomial.X) w) =
      α (MvPolynomial.X i) (E w))
    {p : MvPolynomial (Fin k) K} (hp : α p = 0) :
    MvPolynomial.aeval (fun i => shiftProduct K n (c i)) p = 0 := by
  apply polynomialOperator_relation_detected α (polynomialExteriorShiftEvaluation K n k c)
    (MvPolynomial.aeval (fun i => shiftProduct K n (c i))) E hE
    (polynomialExteriorDeterminant K n) ?_ ?_
    (exteriorPower.ιMulti K n (fun i : Fin n => (Polynomial.X : K[X]) ^ i.val))
    (polynomialExteriorDeterminant_monomials_ne_zero K n) hp
  · intro i w
    simpa only [polynomialExteriorShiftEvaluation_X] using hα i w
  · intro i w
    simpa only [polynomialExteriorShiftEvaluation_X, MvPolynomial.aeval_X] using
      polynomialExteriorMul_scalarDifference K n (c i) w

end PolycyclicRecognition

end

end OAI
