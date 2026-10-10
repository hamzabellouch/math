import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionPairIdentity

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The limiting endpoints have finite floor support, because both actual
lambda_I marginals are Haar-dominated. -/
theorem sourceLambda_endpoints_finiteFloor (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (I : Finset SourceCoordinate) :
    ∀ᵐ z ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus),
      finiteFloorSupport θ (sourceTorusRepresentative z.1) ∧
      finiteFloorSupport θ (sourceTorusRepresentative z.2) := by
  have hf := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (ae_finiteFloorSupport θ hθ.summable)
  have h₁ := ae_of_ae_map (sourceTorusEndpoint_measurable false).aemeasurable
    ((sourceSamplingLambdaTorus_marginal_ac I false).ae_le hf)
  have h₂ := ae_of_ae_map (sourceTorusEndpoint_measurable true).aemeasurable
    ((sourceSamplingLambdaTorus_marginal_ac I true).ae_le hf)
  exact h₁.and h₂

theorem sourceCappedRatio_eq_ratio (θ : SourceCoordinate → ℝ) (z : SourceSamplingTorus)
    (hx : finiteFloorSupport θ (sourceTorusRepresentative z.1))
    (hy : finiteFloorSupport θ (sourceTorusRepresentative z.2))
    (hord : ∀ i, sourceTorusRepresentative z.1 i ≤ sourceTorusRepresentative z.2 i) (k : ℤ) :
    sourceCappedRatio θ z k =
      (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.2) /
        sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.1) : ℝ) := by
  unfold sourceCappedRatio
  rw [min_eq_left ((div_le_one (sourceCocycle_pos ..)).mpr
    (sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hx hy hord k))]

theorem sourceProjection_lambda_ratio_identity (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (I : Finset SourceCoordinate) :
    ∀ᵐ z ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus),
      ∃ D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert,
        ‖D‖ ≤ 1 ∧
        (∀ (v : SourceFiberHilbert) (k : ℤ), D v k =
          (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.2) /
            sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.1) : ℂ) * v k) ∧
        (1-sourceTorusOperatorField p z.2)*D*sourceTorusOperatorField p z.1 = 0 := by
  filter_upwards [sourceProjection_lambda_pairs θ hθ hs hp hproj hinv I,
    sourceLambda_endpoints_finiteFloor θ hθ I,sourceSamplingLambdaTorus_ordered I]
    with z hz hf hord
  refine ⟨fiberDiagonal (sourceCappedRatio θ z) (sourceCappedRatio_norm θ z),
    fiberDiagonal_norm _ _,?_,hz⟩
  intro v k
  rw [fiberDiagonal_apply,sourceCappedRatio_eq_ratio θ z hf.1 hf.2 hord k,Complex.ofReal_div]

end
end FiniteFactor

end OAI
