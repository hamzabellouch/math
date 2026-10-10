import OAI.Geometry.RCD.Sobolev.MeasureProductEnergy

namespace OAI

/-! # The square rule for a bounded weak Laplacian

This is the product identity needed to differentiate heat variance.
The asserted right-hand side is an actual L² function.
-/

open Set Filter MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The exact weak square rule, proved using bounded tests and density. -/
theorem weakLaplacian_square (f : SobolevSpace μ hQ) (d q : Lp ℝ 2 μ)
    (C : ℝ≥0) (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hd : IsWeakLaplacian μ hQ f d)
    (hq : q =ᵐ[μ] fun x => 2*(SobolevSpace.toLp μ hQ f x*d x+localGamma μ hQ f f x)) :
    IsWeakLaplacian μ hQ (SobolevSpace.square μ hQ f C) q := by
  have heq : SobolevSpace.square μ hQ f C = SobolevSpace.product μ hQ f f C C := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.square_coe μ hQ f C hf,
      SobolevSpace.product_coe μ hQ f f C C hf hf] with x hs hp
    change SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ f C) x =
      SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f f C C) x
    rw [hs,hp,pow_two]
  apply weakLaplacian_of_bounded_tests μ hQ
  intro g B hg
  let P := SobolevSpace.product μ hQ f g C B
  have hP := SobolevSpace.product_coe μ hQ f g C B hf hg
  have hbil := energy_product_integration_by_parts μ hQ f f g C C B hf hf hg
  rw [← heq] at hbil
  have htest := hd P
  have hi1 : Integrable (fun x => d x*SobolevSpace.toLp μ hQ P x) μ :=
    (Lp.memLp d).integrable_mul (Lp.memLp (SobolevSpace.toLp μ hQ P))
  have hi2 : Integrable (fun x => SobolevSpace.toLp μ hQ g x*localGamma μ hQ f f x) μ := by
    apply (localGamma_memL1 μ hQ f f).bdd_mul (Lp.aestronglyMeasurable _)
    simpa only [Real.norm_eq_abs] using hg
  have hpair : inner ℝ q (SobolevSpace.toLp μ hQ g) =
      2*inner ℝ d (SobolevSpace.toLp μ hQ P)+
        2*∫ x, SobolevSpace.toLp μ hQ g x*localGamma μ hQ f f x ∂μ := by
    rw [L2.inner_def,L2.inner_def]
    simp only [Real.inner_apply]
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hi1.const_mul 2) (hi2.const_mul 2)]
    apply integral_congr_ae
    filter_upwards [hq,hP] with x hq hP
    change SobolevSpace.toLp μ hQ P x = _ at hP
    simp only [hq,hP]
    ring
  change energyForm μ hQ (SobolevSpace.square μ hQ f C) g = -inner ℝ q _
  change energyForm μ hQ f P = _ at htest
  change energyForm μ hQ (SobolevSpace.square μ hQ f C) g =
    energyForm μ hQ f P+energyForm μ hQ f P-
      2*∫ x, SobolevSpace.toLp μ hQ g x*localGamma μ hQ f f x ∂μ at hbil
  rw [hbil,htest,hpair]
  ring

end RegularPointCoordinates

end

end OAI
