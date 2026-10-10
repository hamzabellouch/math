import OAI.Analysis.FiniteFactor.BiasedPairs.PairIdentity

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- One invariant Borel conull set for the original projection works for every
actual biased law, with strict positivity and the full uncapped pair identity. -/
theorem sourceProjection_biased_common_conull
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∃ Q : Set SourceTorus, MeasurableSet Q ∧ (∀ᵐ z ∂sourceTorusHaar, z ∈ Q) ∧
      (∀ z ∈ Q,
        finiteFloorSupport θ (sourceTorusRepresentative z) ∧
        IsStarProjection (sourceTorusOperatorField p z) ∧
        (∀ r k m : ℤ, (sourceTorusOperatorField p (sourceTorusRotate θ r z)
          (lp.single 2 m (1 : ℂ))) k =
          (sourceTorusOperatorField p z (lp.single 2 (m+r) (1 : ℂ))) (k+r)) ∧
        (∀ n : ℕ, (∀ i, sourceTorusRepresentative z i ≤
          sourceTorusRepresentative (sourceTorusRotate θ n z) i) →
          (z,sourceTorusRotate θ n z) ∈ sourceCappedPairZeroSet θ p) ∧
        0 < (sourceCentralCoefficient p (sourceTorusRepresentative z)).re ∧
        (sourceCentralCoefficient p (sourceTorusRepresentative z)).re < 1 ∧
        (sourceCentralCoefficient p (sourceTorusRepresentative z)).im = 0) ∧
      (∀ n : ℤ, ∀ z ∈ Q, sourceTorusRotate θ n z ∈ Q) ∧
      ∀ j : ℕ, ∀ᵐ z ∂(sourceBiasedTorusMeasure j (fun _ => true) : Measure SourceSamplingTorus),
        z.1 ∈ Q ∧ z.2 ∈ Q ∧
        ∃ D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert,
          ‖D‖ ≤ 1 ∧
          (∀ (v : SourceFiberHilbert) (k : ℤ), D v k =
            (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.2) /
              sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.1) : ℂ) * v k) ∧
          (1-sourceTorusOperatorField p z.2)*D*sourceTorusOperatorField p z.1 = 0 := by
  obtain ⟨Q,hQ,hQa,hQp,hQi⟩ := sourceProjection_positive_common_conull θ hθ hr hp hproj hp0 hp1 hinv
  refine ⟨Q,hQ,hQa,hQp,hQi,?_⟩
  intro j
  filter_upwards [sourceBiasedTorusMeasure_endpoints_conull j (fun _ => true) Q hQa,
    sourceProjection_biased_ratio_identity θ hθ hs hp hproj hinv j] with z hQz hD
  exact ⟨hQz.1,hQz.2,hD⟩

end
end FiniteFactor

end OAI
