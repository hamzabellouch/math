import OAI.Geometry.EinsteinFour.ScalarPoissonKernelCommutator
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelPerturbation

namespace OAI

/-! The actual transpose of the localized second-order scalar operator.
All coefficient and derivative operations here act on Schwartz functions;
there is no assumed integration-by-parts or regularity identity. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

/-- The normalized constant-coefficient operator on test functions. -/
def scalarSchwartzHelmholtz (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  φ - (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • Δ φ

/-- The actual variable-coefficient operator on tempered distributions. -/
def scalarPerturbedOperator (a : Fin 4 → Fin 4 → 𝓢(V, ℂ))
    (b : Fin 4 → 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) : 𝓢'(V, ℂ) :=
  normalizedScalarHelmholtz u +
    (∑ i : Fin 4, ∑ j : Fin 4, smulLeftCLM ℂ (a i j)
      (scalarCoordinateDerivative i (scalarCoordinateDerivative j u))) +
    ∑ i : Fin 4, smulLeftCLM ℂ (b i) (scalarCoordinateDerivative i u)

/-- The transpose includes the derivatives of the coefficients. -/
def scalarSchwartzTranspose (a : Fin 4 → Fin 4 → 𝓢(V, ℂ))
    (b : Fin 4 → 𝓢(V, ℂ)) (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  scalarSchwartzHelmholtz φ +
    (∑ i : Fin 4, ∑ j : Fin 4,
      scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i
        (SchwartzMap.smulLeftCLM ℂ (a i j) φ))) -
    ∑ i : Fin 4, scalarSchwartzCoordinateDerivative i
      (SchwartzMap.smulLeftCLM ℂ (b i) φ)

theorem scalarSchwartzHelmholtz_transpose (u : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    normalizedScalarHelmholtz u φ = u (scalarSchwartzHelmholtz φ) := by
  simp [normalizedScalarHelmholtz, scalarSchwartzHelmholtz]

private theorem scalar_second_transpose (i j : Fin 4) (u : 𝓢'(V, ℂ))
    (φ : 𝓢(V, ℂ)) :
    scalarCoordinateDerivative i (scalarCoordinateDerivative j u) φ =
      u (scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i φ)) := by
  simp [scalarCoordinateDerivative, scalarSchwartzCoordinateDerivative,
    LineDeriv.lineDerivOp_neg]

/-- The precise distributional transpose identity, including signs and the
order reversal in the two derivative slots. -/
theorem scalarPerturbedOperator_transpose (a : Fin 4 → Fin 4 → 𝓢(V, ℂ))
    (b : Fin 4 → 𝓢(V, ℂ)) (u : 𝓢'(V, ℂ)) (φ : 𝓢(V, ℂ)) :
    scalarPerturbedOperator a b u φ = u (scalarSchwartzTranspose a b φ) := by
  simp only [scalarPerturbedOperator, scalarSchwartzTranspose,
    add_apply, sum_apply, smulLeftCLM_apply_apply, scalar_second_transpose,
    scalarSchwartzHelmholtz_transpose, map_add, map_sub, map_sum]
  simp only [scalarCoordinateDerivative, scalarSchwartzCoordinateDerivative,
    lineDerivOp_apply_apply, map_neg]
  rw [Finset.sum_neg_distrib]
  abel

/-- First-order product rule on the test-function space. -/
theorem scalarSchwartzCoordinateDerivative_product (a φ : 𝓢(V, ℂ)) (i : Fin 4) :
    scalarSchwartzCoordinateDerivative i (SchwartzMap.smulLeftCLM ℂ a φ) =
      SchwartzMap.smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a) φ +
        SchwartzMap.smulLeftCLM ℂ a (scalarSchwartzCoordinateDerivative i φ) := by
  ext x
  simp only [scalarSchwartzCoordinateDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.smulLeftCLM_apply a.hasTemperateGrowth, smul_eq_mul]
  rw [fderiv_fun_mul a.differentiableAt φ.differentiableAt]
  simp only [add_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} a : 𝓢(V, ℂ)).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  ring

/-- Expanding the two coefficient derivatives exhibits all lower-order terms. -/
theorem scalarSchwartzCoordinateDerivative_second_product
    (a φ : 𝓢(V, ℂ)) (i j : Fin 4) :
    scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i
      (SchwartzMap.smulLeftCLM ℂ a φ)) =
      SchwartzMap.smulLeftCLM ℂ a
        (scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i φ)) +
      SchwartzMap.smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative i a)
        (scalarSchwartzCoordinateDerivative j φ) +
      SchwartzMap.smulLeftCLM ℂ (scalarSchwartzCoordinateDerivative j a)
        (scalarSchwartzCoordinateDerivative i φ) +
      SchwartzMap.smulLeftCLM ℂ
        (scalarSchwartzCoordinateDerivative j (scalarSchwartzCoordinateDerivative i a)) φ := by
  rw [scalarSchwartzCoordinateDerivative_product]
  change ∂_{EuclideanSpace.basisFun (Fin 4) ℝ j} (_ + _) = _
  rw [LineDeriv.lineDerivOp_add]
  change scalarSchwartzCoordinateDerivative j _ + scalarSchwartzCoordinateDerivative j _ = _
  rw [scalarSchwartzCoordinateDerivative_product, scalarSchwartzCoordinateDerivative_product]
  abel

end
end PositiveEinsteinFour.Geometry

end OAI
