import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixFunctions
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisPolynomialMaps
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlowSmooth

namespace OAI

/-! # Joint polynomial coordinates of a nilpotent derivation flow -/

noncomputable section
namespace PolycyclicRecognition

theorem multivariatePolynomialFunctions_pow {I : Type*} {f : (I → ℝ) → ℝ}
    (hf : f ∈ multivariatePolynomialFunctions I) (k : ℕ) :
    (fun x => f x ^ k) ∈ multivariatePolynomialFunctions I := by
  obtain ⟨p, hp⟩ := mem_multivariatePolynomialFunctions.mp hf
  exact mem_multivariatePolynomialFunctions.mpr
    ⟨p ^ k, fun x => by rw [map_pow, hp]⟩

variable {I L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

omit [FiniteDimensional ℝ L] in
theorem coordinatePolynomial_linear_map (A : L →ₗ[ℝ] L) (F : (I → ℝ) → L)
    (hF : IsCoordinatePolynomial (fun x => b.equivFun (F x))) :
    IsCoordinatePolynomial (fun x => b.equivFun (A (F x))) := by
  have h := IsCoordinatePolynomial.comp (IsPolynomialInBasis.linear (b := b) (c := b) A) hF
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using h

local instance polynomialDerivationCoordinatesRational : Module ℚ L :=
  Module.compHom L (algebraMap ℚ ℝ)

omit [FiniteDimensional ℝ L] in
theorem coordinatePolynomial_derivationFlow
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
    (f : (I → ℝ) → ℝ) (F : (I → ℝ) → L)
    (hf : f ∈ multivariatePolynomialFunctions I)
    (hF : IsCoordinatePolynomial (fun x => b.equivFun (F x))) :
    IsCoordinatePolynomial (fun x => b.equivFun (nilpotentDerivationFlow D hD (f x) (F x))) := by
  let k := nilpotencyClass D.toLinearMap
  have hk : D.toLinearMap ^ k = 0 := pow_nilpotencyClass hD
  apply coordinatePolynomial_iff_components.mpr
  intro j
  have heq : (fun x => b.equivFun (nilpotentDerivationFlow D hD (f x) (F x)) j) =
      ∑ i ∈ Finset.range k, (fun x => f x ^ i *
        b.equivFun (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) (F x)) j) := by
    funext x
    rw [nilpotentDerivationFlow_eq_sum D hD hk]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact multivariatePolynomialFunctions_mul (multivariatePolynomialFunctions_pow hf i)
    (coordinatePolynomial_iff_components.mp (coordinatePolynomial_linear_map b _ F hF) j)

end PolycyclicRecognition

end

end OAI
