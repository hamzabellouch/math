import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateCurves
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlowSmooth

namespace OAI

/-! # Polynomial curves under linear maps and nilpotent derivation flows -/

noncomputable section
namespace PolycyclicRecognition

theorem polynomialFunctions_mul {f g : ℝ → ℝ}
    (hf : f ∈ polynomialFunctions) (hg : g ∈ polynomialFunctions) :
    (fun t => f t * g t) ∈ polynomialFunctions := by
  obtain ⟨p, hp⟩ := mem_polynomialFunctions_iff.mp hf
  obtain ⟨q, hq⟩ := mem_polynomialFunctions_iff.mp hg
  exact mem_polynomialFunctions_iff.mpr ⟨p * q, fun t => by rw [Polynomial.eval_mul, hp, hq]⟩

theorem polynomialFunctions_pow {f : ℝ → ℝ} (hf : f ∈ polynomialFunctions) (k : ℕ) :
    (fun t => f t ^ k) ∈ polynomialFunctions := by
  obtain ⟨p, hp⟩ := mem_polynomialFunctions_iff.mp hf
  exact mem_polynomialFunctions_iff.mpr ⟨p ^ k, fun t => by rw [Polynomial.eval_pow, hp]⟩

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

theorem hasPolynomialLineCoordinates_linear (A : L →ₗ[ℝ] L) (F : ℝ → L)
    (hF : HasPolynomialLineCoordinates b F) :
    HasPolynomialLineCoordinates b (fun t => A (F t)) := by
  intro j
  exact polynomial_of_coordinateEvaluations b.equivFun.toLinearMap b.equivFun.injective F hF
    ((LinearMap.proj j).comp (b.equivFun.toLinearMap.comp A))

local instance polynomialCurveModuleRat : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

theorem hasPolynomialLineCoordinates_derivationFlow
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
    (f : ℝ → ℝ) (F : ℝ → L) (hf : f ∈ polynomialFunctions)
    (hF : HasPolynomialLineCoordinates b F) :
    HasPolynomialLineCoordinates b (fun t => nilpotentDerivationFlow D hD (f t) (F t)) := by
  let k := nilpotencyClass D.toLinearMap
  have hk : D.toLinearMap ^ k = 0 := pow_nilpotencyClass hD
  intro j
  have heq : (fun t => b.repr (nilpotentDerivationFlow D hD (f t) (F t)) j) =
      ∑ i ∈ Finset.range k, (fun t => f t ^ i *
        b.repr (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) (F t)) j) := by
    funext t
    rw [nilpotentDerivationFlow_eq_sum D hD hk]
    simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, Finset.sum_apply]
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact polynomialFunctions_mul (polynomialFunctions_pow hf i)
    (hasPolynomialLineCoordinates_linear b _ F hF j)

end PolycyclicRecognition

end

end OAI
