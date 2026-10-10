import OAI.Geometry.RCD.Sobolev.WeakLaplacianProduct
import OAI.Geometry.RCD.Sobolev.WeightedGammaGradientBound

namespace OAI

/-! # Product tests against an L² weak Laplacian

Both product factors are bounded Sobolev functions. In particular no
Sobolev derivative of the Laplacian is needed for these identities.
-/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The energy product rule with the two bounded coefficients exposed. -/
theorem energyForm_product_test (f g w : SobolevSpace μ hQ) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x|≤A)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤B) :
    energyForm μ hQ (SobolevSpace.product μ hQ f g A B) w =
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ f) g w+
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ g) f w := by
  have hi := (localGamma_memL1 μ hQ g w).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ f))
    (by simpa only [Real.norm_eq_abs] using hf)
  have hj := (localGamma_memL1 μ hQ f w).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ g))
    (by simpa only [Real.norm_eq_abs] using hg)
  rw [← integral_localGamma_eq_energyForm]
  unfold weightedGamma
  rw [← integral_add hi hj]
  exact integral_congr_ae (localGamma_product_left μ hQ f g w A B hf hg)

/-- Integration by parts against a bounded Sobolev product. This is the
cancellation used in the Bochner square rule for merely L² sources. -/
theorem IsWeakLaplacian.weighted_product (f g w : SobolevSpace μ hQ)
    (d : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ hQ f d) (A B : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤B) :
    weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f g+
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ g) f w =
        -(∫ x, SobolevSpace.toLp μ hQ w x*SobolevSpace.toLp μ hQ g x*d x ∂μ) := by
  have he := energyForm_product_test μ hQ g w f A B hg hw
  rw [energyForm_comm μ hQ (SobolevSpace.product μ hQ g w A B) f,hd] at he
  rw [weightedGamma_comm μ hQ (SobolevSpace.toLp μ hQ g) w f,
    weightedGamma_comm μ hQ (SobolevSpace.toLp μ hQ w) g f] at he
  have hi : inner ℝ d (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g w A B)) =
      ∫ x, SobolevSpace.toLp μ hQ w x*SobolevSpace.toLp μ hQ g x*d x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ g w A B hg hw] with x hx
    simp only [Real.inner_apply,hx]
    ring
  rw [hi] at he
  linarith only [he]

end RegularPointCoordinates

end

end OAI
