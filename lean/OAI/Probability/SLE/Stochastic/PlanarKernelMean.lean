import OAI.Probability.SLE.Geometry.CompactPlanarGaussian
import OAI.Probability.SLE.Stochastic.PlanarWienerIncrements

namespace OAI

/-! Conditional averaging against the actual product Gaussian increment.
This is the integral form needed for the planar Brownian generator. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma independent_planar_gaussian_integral
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : Ω → X) (Y : Ω → ℝ×ℝ) (hZ : Measurable Z) (_hY : Measurable Y)
    (δ : ℝ≥0)
    (hLaw : HasLaw Y ((gaussianReal 0 δ).prod (gaussianReal 0 δ)) P)
    (hind : IndepFun Z Y P)
    (H : X×(ℝ×ℝ) → ℝ) (hH : Measurable H) (C : ℝ)
    (hbound : ∀ p, |H p| ≤ C) :
    (∫ ω, H (Z ω,Y ω) ∂P) =
      ∫ ω, ∫ y, H (Z ω,y) ∂(gaussianReal 0 δ).prod (gaussianReal 0 δ) ∂P := by
  let ν := (gaussianReal 0 δ).prod (gaussianReal 0 δ)
  have hZLaw : HasLaw Z (P.map Z) P := ⟨hZ.aemeasurable,rfl⟩
  have hj := hind.hasLaw_prod hZLaw hLaw
  have hHi : Integrable H ((P.map Z).prod ν) :=
    Integrable.of_bound hH.aestronglyMeasurable C
      (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hbound p)
  calc
    _ = ∫ p, H p ∂(P.map Z).prod ν := hj.integral_comp hH.aestronglyMeasurable
    _ = ∫ x, ∫ y, H (x,y) ∂ν ∂P.map Z := integral_prod H hHi
    _ = _ := (hZLaw.integral_comp hHi.integral_prod_left.aestronglyMeasurable).symm

end SLEExactGauge

end

end OAI
