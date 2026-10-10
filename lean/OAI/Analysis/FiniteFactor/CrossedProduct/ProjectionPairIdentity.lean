import OAI.Analysis.FiniteFactor.CrossedProduct.OrbitNormalization
import OAI.Analysis.FiniteFactor.CrossedProduct.CappedTransfer

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Every original invariant projection satisfies the normalized equation on
all its ordered positive orbit pairs, on one conull set. -/
theorem sourceProjection_ordered_orbits (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∀ᵐ z ∂sourceTorusHaar, ∀ n : ℕ,
      (∀ i, sourceTorusRepresentative z i ≤ sourceTorusRepresentative (sourceTorusRotate θ n z) i) →
      (z,sourceTorusRotate θ n z) ∈ sourceCappedPairZeroSet θ p := by
  let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  have hf := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (ae_finiteFloorSupport θ hθ.summable)
  have hc := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (sourceOperatorField_covariance θ hp)
  have hi : ∀ᵐ z ∂sourceTorusHaar, ∀ n : ℕ,
      (1-sourceTorusOperatorField p z)*sourceTorusOperatorField (T^n) z*sourceTorusOperatorField p z = 0 := by
    rw [ae_all_iff]
    intro n
    exact sourceTorusOperatorField_invariant θ hp (pow_mem (staged_sourceOperator_mem θ hθ) n)
      (invariant_projection_pow p T hproj.isIdempotentElem hinv n)
  have hw := ae_all_iff.mpr (sourceTorusOperatorField_sourceOperator_pow θ hθ)
  filter_upwards [hf,hc,hi,hw] with z hf hc hi hw n hord
  have hcov : fiberShift (-(n : ℤ))*sourceTorusOperatorField p z =
      sourceTorusOperatorField p (sourceTorusRotate θ n z)*fiberShift (-(n : ℤ)) := by
    apply fiber_covariance_operator
    intro k m
    change (sourceOperatorField p (sourceTorusRepresentative (sourceTorusRotate θ n z))
      (lp.single 2 m (1 : ℂ))) k = _
    rw [sourceTorusRepresentative_rotate]
    exact hc n m k
  have hrot := fiber_rotated_invariant _ _ (sourceTorusOperatorField (T^n) z) n hcov (hi n)
  change (1-sourceTorusOperatorField p (sourceTorusRotate θ n z))*
    fiberDiagonal (sourceCappedRatio θ (z,sourceTorusRotate θ n z))
      (sourceCappedRatio_norm θ (z,sourceTorusRotate θ n z))*sourceTorusOperatorField p z = 0
  rw [sourceCappedRatio_orbit_diagonal θ z n hf hord _ (hw n)]
  ext1 vector
  have hv := congrArg (fun operator : SourceFiberHilbert →L[ℂ] SourceFiberHilbert =>
    operator vector) hrot
  dsimp only [T] at hv
  simp only [mul_apply_eq_comp, zero_apply] at hv
  simp only [mul_apply_eq_comp, smul_apply, map_smul, zero_apply, hv, smul_zero]

/-- The approximant equations follow from the original invariant projection,
the actual positive orbit support, and absolute continuity of the first
marginal. They are not assumed as a transfer premise. -/
theorem sourceProjection_sampling_pairs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (I : Finset SourceCoordinate) (s : ℕ) :
    ∀ᵐ z ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ p := by
  obtain ⟨C,hC⟩ := hs.marginals I false
  obtain ⟨g,_,_,hg,_,_⟩ := hC s
  have hac : (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus).map Prod.fst ≪
      sourceTorusHaar := by
    change (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus).map
      (sourceTorusEndpoint false) ≪ _
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  have horbit := ae_of_ae_map measurable_fst.aemeasurable
    (hac.ae_le (sourceProjection_ordered_orbits θ hθ hp hproj hinv))
  filter_upwards [horbit,hs.support I s] with z hz hsupport
  obtain ⟨hord,n,hn,hnpos,he⟩ := hsupport
  have hn0 : 0 ≤ n := le_of_lt hnpos
  have hncast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have hh := hz n.toNat
  rw [hncast, ← he] at hh
  exact hh hord

theorem sourceProjection_lambda_pairs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (I : Finset SourceCoordinate) :
    ∀ᵐ z ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ p :=
  sourceCappedPair_limit_transfer hs I p (sourceProjection_sampling_pairs θ hθ hs hp hproj hinv I)

end
end FiniteFactor

end OAI
