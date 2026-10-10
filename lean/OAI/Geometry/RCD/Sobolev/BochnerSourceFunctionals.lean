import OAI.Geometry.RCD.Sobolev.SobolevTestFunctional
import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Linear source terms for an L² Laplacian -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

def boundedIntegralFunctional (ρ : X → ℝ) (hρ : Integrable ρ μ) :
    (X →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∫ x, v x * ρ x ∂μ
  map_add' v w := by
    have hi (f : X →ᵇ ℝ) : Integrable (fun x => f x * ρ x) μ :=
      hρ.bdd_mul f.continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => f.norm_coe_le_norm x)
    change (∫ x, (v x + w x) * ρ x ∂μ) = _
    simp_rw [add_mul]
    exact integral_add (hi v) (hi w)
  map_smul' c v := by
    change (∫ x, (c * v x) * ρ x ∂μ) = c * ∫ x, v x * ρ x ∂μ
    simp_rw [mul_assoc]
    exact integral_const_mul c _

variable [ProperSpace X] (hQ : QuadraticCheegerEnergy μ)

def gammaSourceFunctional (d : Lp ℝ 2 μ) (u : SobolevSpace μ hQ) (L : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L) :
    SobolevSpace μ hQ →ₗ[ℝ] ℝ where
  toFun w := weightedGamma μ hQ d u w
  map_add' v w := by
    have hi (f : SobolevSpace μ hQ) : Integrable (fun x => d x * localGamma μ hQ u f x) μ :=
      (Lp.memLp d).integrable_mul (localGamma_memLp_of_bounded_gradient μ hQ u f L hu)
    unfold weightedGamma
    rw [← integral_add (hi v) (hi w)]
    apply integral_congr_ae
    filter_upwards [localGamma_add_right μ hQ u v w] with x hx
    rw [hx, mul_add]
  map_smul' c v := by
    change weightedGamma μ hQ d u (c • v) = c * weightedGamma μ hQ d u v
    rw [weightedGamma_comm μ hQ d u (c • v), weightedGamma_smul_left,
      weightedGamma_comm μ hQ d v u]

end RegularPointCoordinates

end

end OAI
