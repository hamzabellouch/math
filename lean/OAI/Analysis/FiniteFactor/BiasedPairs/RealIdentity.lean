import OAI.Analysis.FiniteFactor.BiasedPairs.CommonConull

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Almost-everywhere original-base properties transfer to every actual mixed endpoint. -/
theorem sourceBiasedEndpoint_ae (j : ℕ) (r : SourceCoordinate → Bool)
    {P : (SourceCoordinate → ℝ) → Prop} (hP : ∀ᵐ x ∂sourceBaseMeasure, P x) :
    ∀ᵐ ω ∂sourceBiasedLaw j, P (sourceBiasedEndpoint r ω) := by
  obtain ⟨g,_,_,_,hm,_⟩ := sourceBiasedEndpoint_density j r
  have ha : (sourceBiasedLaw j).map (sourceBiasedEndpoint r) ≪ sourceSamplingHaar := by
    rw [hm]
    exact withDensity_absolutelyContinuous _ _
  exact ae_of_ae_map (sourceBiasedEndpoint_measurable r).aemeasurable (ha.ae_le hP)

/-- The full uncapped pair identity on the actual augmented probability space,
with the original real endpoints and original operator fields. -/
theorem sourceProjection_biased_ratio_augmented (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j,
      ∃ D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert,
        ‖D‖ ≤ 1 ∧
        (∀ (v : SourceFiberHilbert) (k : ℤ), D v k =
          (sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
            sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) : ℂ) * v k) ∧
        (1-sourceOperatorField p (sourceBiasedEndpoint (fun _ => true) ω))*D*
          sourceOperatorField p (sourceBiasedEndpoint (fun _ => false) ω) = 0 := by
  have ht := sourceProjection_biased_ratio_identity θ hθ hs hp hproj hinv j
  have hr := ae_of_ae_map sourceSamplingTorusMap_continuous.measurable.aemeasurable ht
  have ha := ae_of_ae_map (sourceBiasedPair_measurable (fun _ => true)).aemeasurable hr
  filter_upwards [ha,sourceBiasedEndpoint_cube j (fun _ => false),
    sourceBiasedEndpoint_cube j (fun _ => true)] with ω hω hx hy
  obtain ⟨D,hDn,hDa,hD⟩ := hω
  have hxe : sourceTorusRepresentative
      (sourceSamplingTorusMap (sourceBiasedPair (fun _ => true) ω)).1 =
        sourceBiasedEndpoint (fun _ => false) ω := sourceTorusRepresentative_quotient _ hx
  have hye : sourceTorusRepresentative
      (sourceSamplingTorusMap (sourceBiasedPair (fun _ => true) ω)).2 =
        sourceBiasedEndpoint (fun _ => true) ω := sourceTorusRepresentative_quotient _ hy
  refine ⟨D,hDn,?_,?_⟩
  · simpa only [hxe,hye] using hDa
  · simpa only [sourceTorusOperatorField,hxe,hye] using hD

end
end FiniteFactor

end OAI
