import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnipotentCoordinateBCH
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialUnipotentModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential

namespace OAI

/-! # Integration between polynomial exponential models

Each model has a faithful unipotent representation. Enlarging both product
bounds to their maximum gives the same universal BCH coefficients, hence
every Lie homomorphism preserves the two group laws.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L K : Type*} [RealNormedLieAlgebra L] [RealNormedLieAlgebra K]
  [FiniteDimensional ℝ L] [FiniteDimensional ℝ K]
  [P : PolynomialExponentialCoordinates L] [Q : PolynomialExponentialCoordinates K]

theorem polynomialCoordinate_map_mul (f : L →ₗ⁅ℝ⁆ K) (x y : L) :
    f (x * y) = f x * f y := by
  obtain ⟨m, c, ρ, j, hρ, _, _, hexp, _, hc⟩ :=
    exists_polynomial_unipotent_model (Module.finBasis ℝ L)
  obtain ⟨m', c', ρ', j', hρ', _, _, hexp', _, hc'⟩ :=
    exists_polynomial_unipotent_model (Module.finBasis ℝ K)
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin m') (Fin m') ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have hprod := finite_product_of_unipotent_coordinates ρ hρ j hexp (max c c')
    (fun l hl => hc l ((Nat.le_max_left c c').trans hl.le)) ![x, y]
  have hprod' := finite_product_of_unipotent_coordinates ρ' hρ' j' hexp' (max c c')
    (fun l hl => hc' l ((Nat.le_max_right c c').trans hl.le)) ![f x, f y]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one] at hprod hprod'
  rw [hprod, finiteDynkinPolynomial_map, hprod']
  congr 1
  funext i
  fin_cases i <;> rfl

def polynomialCoordinateHom (f : L →ₗ⁅ℝ⁆ K) : L →* K where
  toFun := f
  map_one' := by rw [P.one_eq_zero, map_zero, Q.one_eq_zero]
  map_mul' := polynomialCoordinate_map_mul f

@[simp] theorem polynomialCoordinateHom_apply (f : L →ₗ⁅ℝ⁆ K) (x : L) :
    polynomialCoordinateHom f x = f x := rfl

theorem contDiff_polynomialCoordinateHom (f : L →ₗ⁅ℝ⁆ K) :
    ContDiff ℝ ∞ (polynomialCoordinateHom f) :=
  f.toLinearMap.toContinuousLinearMap.contDiff

theorem contMDiff_polynomialCoordinateHom (f : L →ₗ⁅ℝ⁆ K) :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, K)) ∞ (polynomialCoordinateHom f) :=
  (contDiff_polynomialCoordinateHom f).contMDiff

theorem mfderiv_polynomialCoordinateHom (f : L →ₗ⁅ℝ⁆ K) :
    mfderiv (𝓘(ℝ, L)) (𝓘(ℝ, K)) (polynomialCoordinateHom f) 1 =
      f.toLinearMap.toContinuousLinearMap := by
  exact f.toLinearMap.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.mfderiv

end PolycyclicRecognition

end

end OAI
