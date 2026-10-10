import OAI.Analysis.KadisonKastler.WeightedStripFactorization
import OAI.Analysis.KadisonKastler.WeightedStripDense
import OAI.Analysis.KadisonKastler.WeightedStripAverage
import OAI.Analysis.KadisonKastler.ModularOrbit

namespace OAI

/-! # The bounded modular equation determines the orbit average

The scalar contour theorem is applied after multiplying by an injective
dense-range spectral weight. Its cancellation then identifies the actual
operator average, not only its weighted matrix coefficients.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularOrbitAverage_eq_of_equation (X Y : H →L[ℂ] H) (φ : ℝ)
    (hφ : |φ| < Real.pi)
    (heq : tomitaMiddleOperator (M := M) J Ω * Y * tomitaMiddleOperator (M := M) J Ω =
      Complex.exp (Complex.I * φ / 2) •
          (graphResolvent M J Ω 1 * X * (1 - graphResolvent M J Ω 1)) +
        Complex.exp (-(Complex.I * φ / 2)) •
          ((1 - graphResolvent M J Ω 1) * X * graphResolvent M J Ω 1)) :
    modularOrbitAverage J Ω hsep hcyc Y φ hφ = X := by
  apply weightedStripOperator_cancel_sandwich J Ω hsep hcyc
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  let W := weightedStripOperator (M := M) J Ω 0
  let F := modularOrbit J Ω hsep hcyc Y
  let w := stripAverageKernel Real.pi (φ : ℂ)
  have hw : Integrable w := stripAverageKernel_integrable (by simpa using hφ)
  have hi : Integrable (fun t => w t • F t (W η)) :=
    integrable_weighted_operator_vector volume w hw F
      (fun x => (modularOrbit_continuous J Ω hsep hcyc Y x).aestronglyMeasurable)
      ‖Y‖ (Filter.Eventually.of_forall (modularOrbit_norm_le J Ω hsep hcyc Y)) (W η)
  have hav : inner ℂ ξ ((W * modularOrbitAverage J Ω hsep hcyc Y φ hφ * W) η) =
      ∫ t : ℝ, w t * inner ℂ ξ ((W * F t * W) η) := by
    change ((innerSL ℂ ξ).comp W) (∫ t : ℝ, w t • F t (W η)) = _
    rw [← ((innerSL ℂ ξ).comp W).integral_comp_comm hi]
    simp only [ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul,
      mul_apply_eq_comp, innerSL_apply_apply]
  have hb (t : ℝ) :
      inner ℂ ξ ((W * F t * W) η) =
        Complex.exp (Complex.I * φ / 2) *
            weightedStripCoefficient (M := M) J Ω X ξ η ((1 / 2 : ℂ) + t * Complex.I) +
          Complex.exp (-(Complex.I * φ / 2)) *
            weightedStripCoefficient (M := M) J Ω X ξ η ((-1 / 2 : ℂ) + t * Complex.I) := by
    have h := congrArg (fun A : H →L[ℂ] H => inner ℂ ξ (A η))
      (weightedStrip_boundary_factorization J Ω hsep hcyc X Y _ _ heq t)
    simpa only [add_apply, smul_apply,
      inner_add_right, inner_smul_right, smul_eq_mul, weightedStripCoefficient, W, F, modularOrbit] using h.symm
  calc
    _ = ∫ t : ℝ, w t * inner ℂ ξ ((W * F t * W) η) := hav
    _ = ∫ t : ℝ, stripAverageKernel Real.pi (φ : ℂ) t *
        (Complex.exp (Complex.I * φ / 2) *
            weightedStripCoefficient (M := M) J Ω X ξ η ((1 / 2 : ℂ) + t * Complex.I) +
          Complex.exp (-(Complex.I * φ / 2)) *
            weightedStripCoefficient (M := M) J Ω X ξ η ((-1 / 2 : ℂ) + t * Complex.I)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => congrArg (w t * ·) (hb t)
    _ = _ := by
      simpa only [weightedStripCoefficient, neg_zero] using
        weightedStripCoefficient_average J Ω X ξ η φ hφ

end

end KadisonKastler

end OAI
