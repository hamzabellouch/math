import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialExponentialCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlowSmooth

namespace OAI

/-! # Derivation flows act on polynomial exponential groups -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

namespace PolynomialExponentialCoordinates

def groupAutomorphism (e : L ≃ₗ⁅ℝ⁆ L) : MulAut L where
  toEquiv := e.toLinearEquiv.toEquiv
  map_mul' x y := by
    rw [P.mul_eq, P.mul_eq]
    have h := finiteDynkinPolynomial_map e.toLieHom P.coefficients ![x, y]
    change e (finiteDynkinPolynomial P.coefficients ![x, y]) = _ at h
    change e (finiteDynkinPolynomial P.coefficients ![x, y]) = _
    rw [h]
    congr 1
    funext i
    fin_cases i <;> rfl

@[simp] theorem groupAutomorphism_apply (e : L ≃ₗ⁅ℝ⁆ L) (x : L) :
    groupAutomorphism (P := P) e x = e x := rfl

def derivationAction (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    Multiplicative ℝ →* MulAut L where
  toFun t := groupAutomorphism (P := P) (nilpotentDerivationFlow D hD t.toAdd)
  map_one' := by
    ext x
    exact nilpotentDerivationFlow_zero D hD x
  map_mul' s t := by
    ext x
    exact nilpotentDerivationFlow_add D hD s.toAdd t.toAdd x

@[simp] theorem derivationAction_apply (D : LieDerivation ℝ L L)
    (hD : IsNilpotent D.toLinearMap) (t : Multiplicative ℝ) (x : L) :
    derivationAction (P := P) D hD t x = nilpotentDerivationFlow D hD t.toAdd x := rfl

end PolynomialExponentialCoordinates
end PolycyclicRecognition

end

end OAI
