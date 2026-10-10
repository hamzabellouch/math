import OAI.Geometry.RCD.Sobolev.BochnerMeasureProduct

namespace OAI

/-! # The full local measure identity for the Bochner product rule -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Multiplying a gradient direction by a regular function produces the
Hessian term in the full local Bochner measure, including singular mass. -/
theorem bochner_measure_product [SecondCountableTopology X] [IsFiniteMeasureOnCompacts μ]
    {Ω S : Set X} (hΩ : MeasurableSet Ω) (K : ℝ)
    (f g h df dg dh Fg Fh Gh Fz : SobolevSpace μ hQ)
    (dg₀ dh₀ : Lp ℝ 2 μ) (hdg : IsWeakLaplacian μ hQ g dg₀)
    (hdh : IsWeakLaplacian μ hQ h dh₀)
    (hdg₀ : dg₀ =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dg)
    (hdh₀ : dh₀ =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dh)
    (G H : X →ᵇ ℝ) (hG : SobolevSpace.toLp μ hQ g =ᵐ[μ] G)
    (hH : SobolevSpace.toLp μ hQ h =ᵐ[μ] H)
    (A B E F : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ Fg x|≤A)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ Fh x|≤B)
    (hE : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dg x|≤E)
    (hF : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dh x|≤F)
    (hFg : SobolevSpace.toLp μ hQ Fg =ᵐ[μ.restrict Ω] localGamma μ hQ f g)
    (hFh : SobolevSpace.toLp μ hQ Fh =ᵐ[μ.restrict Ω] localGamma μ hQ f h)
    (hFz : SobolevSpace.toLp μ hQ Fz =ᵐ[μ.restrict Ω]
      localGamma μ hQ f (SobolevSpace.product μ hQ g h ‖G‖₊ ‖H‖₊))
    (Sg Sh Sz : SignedMeasure X)
    (hSg : IsMeasureLaplacianOn μ hQ Ω Fg (bochnerGramSource μ hQ K f g df dg Sg))
    (hSh : IsMeasureLaplacianOn μ hQ Ω Fh (bochnerGramSource μ hQ K f h df dh Sh))
    (hSz : IsMeasureLaplacianOn μ hQ Ω Fz
      (bochnerGramSource μ hQ K f (SobolevSpace.product μ hQ g h ‖G‖₊ ‖H‖₊) df
        (SobolevSpace.product μ hQ g dh ‖G‖₊ F+
          SobolevSpace.product μ hQ h dg ‖H‖₊ E+(2:ℝ) • Gh) Sz))
    (hS : MeasurableSet S) (χ : X →ᵇ ℝ) {Cχ : ℝ≥0} (hχ : LipschitzWith Cχ χ)
    (hχc : HasCompactSupport (χ : X → ℝ)) (hχΩ : tsupport χ ⊆ Ω)
    (hχ0 : ∀ x, 0≤χ x) (hχ1 : ∀ x ∈ S, χ x=1) :
    Sz.restrict S =
      (signedSourceWeight Sh G+signedSourceWeight Sg H+
        (2 : ℝ) • μ.withDensityᵥ (localHessianAction μ hQ f g h Fg Fh Gh)).restrict S := by
  apply signedMeasure_eq_restrict_of_tests Sz _ hS χ hχ hχc hχΩ hχ0 hχ1
  intro q
  obtain ⟨Cq,hq,hqc,hqs⟩ := q.property
  let ψ := compactTestSobolev μ hQ Ω q
  have ht := bochner_measure_product_test μ hQ hΩ K f g h df dg dh Fg Fh Gh Fz
    dg₀ dh₀ hdg hdh hdg₀ hdh₀ G H hG hH A B E F hA hB hE hF hFg hFh hFz
    Sg Sh Sz hSg hSh hSz ψ q hqc hqs (compactTestSobolev_coe μ hQ Ω q)
  have hw : signedTestIntegral (q : X →ᵇ ℝ)
      (signedSourceWeight Sh G+signedSourceWeight Sg H+
        (2 : ℝ) • μ.withDensityᵥ (localHessianAction μ hQ f g h Fg Fh Gh)) =
      signedTestIntegral ((q : X →ᵇ ℝ)*G) Sh+signedTestIntegral ((q : X →ᵇ ℝ)*H) Sg+
        2*(∫ x, (q : X →ᵇ ℝ) x*localHessianAction μ hQ f g h Fg Fh Gh x ∂μ) := by
    rw [map_add,map_add,map_smul]
    change (∫ᵛ x, (q : X →ᵇ ℝ) x ∂<•signedSourceWeight Sh G)+
      (∫ᵛ x, (q : X →ᵇ ℝ) x ∂<•signedSourceWeight Sg H)+
      2*(∫ᵛ x, (q : X →ᵇ ℝ) x ∂<•μ.withDensityᵥ (localHessianAction μ hQ f g h Fg Fh Gh)) = _
    rw [integral_signedSourceWeight,integral_signedSourceWeight,
      integral_signedDensity μ (localHessianAction_integrable μ hQ f g h Fg Fh Gh)]
    rfl
  exact ht.trans hw.symm

end RegularPointCoordinates

end

end OAI
