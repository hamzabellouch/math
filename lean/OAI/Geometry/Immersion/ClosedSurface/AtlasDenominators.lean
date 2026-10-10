import OAI.Geometry.Immersion.ClosedSurface.AtlasDecomposition
import OAI.Geometry.Immersion.ClosedSurface.DenominatorBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set PhaseGrid WeightedEstimates Bundle Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {ι : Type*} [Fintype ι]




def AtlasPhaseDenominatorBounds (p : ι → M) (r : ι → ℝ) (ψ : ι → M → ℝ)
    (s : ι → Finset Index) (P : ∀ i, {a // a ∈ s i} → PhaseBasis)
    (z : ℝ) (F : M → Space) (w : AtlasCellPhase (ι := ι) → ℝ)
    (ε b C W : ℝ) : Prop :=
  ∀ G, CoordinateJetBall p r z F G → ∀ i (a : {a // a ∈ s i}) j q,
    q ∈ tsupport (refinedCutoff (p i) (ψ i) (s i) (z^6) a.val) →
    ‖secondQuadratic (atlasSecondTensor G (p i) q)
      (-(w (i,a.val,j) • (P i a).ξ j).2,(w (i,a.val,j) • (P i a).ξ j).1)‖⁻¹ ≤ 8/(ε*b) ∧
    ∃ hn : w (i,a.val,j) • (P i a).ξ j ≠ 0,
      ‖(phaseEquiv (w (i,a.val,j) • (P i a).ξ j) hn).symm.toContinuousLinearMap‖ ≤ 32*W*C/ε




omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
theorem fixed_atlas_phase_data_with_denominator_bounds_with_catalog (g : SmoothMetric M)
    (p : ι → M) (r : ι → ℝ) (ψ : ι → M → ℝ)
    (hball : ∀ i, Metric.closedBall (coordinateCenter (p i)) (r i) ⊆ coordinateDomain (p i))
    (hψ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i))
    (hcompact : ∀ i, HasCompactSupport (ψ i))
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hK : ∀ i, IsCompact (chartSupport (p i) (ψ i)))
    (hKU : ∀ i, chartSupport (p i) (ψ i) ⊆ Metric.ball (coordinateCenter (p i)) (r i))
    (hsquare : ∀ q, ∑ i, (ψ i q)^2 = 1)
    (R c A b : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) :
    ∃ phaseStock : Finset PhaseBasis, ∃ weightStock : Finset ℝ,
    ∃ z₀ D C ε δ W κ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < D ∧ 1 ≤ C ∧
      0 < ε ∧ 0 < δ ∧ 0 < W ∧ 0 < κ ∧
      ∃ J : ℕ → ℝ, (∀ j, 1 ≤ J j) ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedBound (Metric.ball (coordinateCenter (p i)) (r i)) z 3 A (coordinateMap F (p i))) →
      (∀ i y, y ∈ Metric.ball (coordinateCenter (p i)) (r i) →
        ‖firstJetPair (coordinateMap F (p i)) y‖ ≤ R ∧
        c ≤ NormalFrame.gramDet (firstJetPair (coordinateMap F (p i)) y).1
          (firstJetPair (coordinateMap F (p i)) y).2 ∧ b ≤ ‖realSecondTensor (coordinateMap F (p i)) y‖) →
      ∃ (s : ι → Finset Index) (P : ∀ i, {a // a ∈ s i} → PhaseBasis)
        (ξ : AtlasCellPhase (ι := ι) → SmallModes.Base) (w : AtlasCellPhase (ι := ι) → ℝ),
        (∀ i a, P i a ∈ phaseStock) ∧ (∀ a, w a ∈ weightStock) ∧
        (∑ i, ((s i).card : ℝ)) ≤ D/z^12 ∧
        (∀ i, chartSupport (p i) (ψ i) ⊆ coverRegion (s i) (z^6)) ∧
        (∀ i a j y, y ∈ coverRegion (s i) (z^6) →
          ‖iteratedFDeriv ℝ j (normalizedCutoff (s i) (z^6) a) y‖ ≤ J j/z^(6*j)) ∧
        (∀ i a, ContMDiff planeModel 𝓘(ℝ) ∞ (refinedCutoff (p i) (ψ i) (s i) (z^6) a)) ∧
        (∀ q, ∑ i, ∑ a ∈ s i, (refinedCutoff (p i) (ψ i) (s i) (z^6) a q)^2 = 1) ∧
        (∀ i (a : {a // a ∈ s i}) j, ξ (i,a.val,j) = (P i a).ξ j ∧
          ‖(P i a).ξ j‖ ≤ C ∧ ‖(P i a).Q j‖ ≤ C) ∧
        (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        (∀ G, CoordinateJetBall p r z F G → ∀ i (a : {a // a ∈ s i}) y H',
          y ∈ tsupport (cutoff (z^6) a.val) → ‖H'-coordinateMetric g (p i) y‖ ≤ δ →
          c/2 ≤ NormalFrame.gramDet (firstJetPair (coordinateMap G (p i)) y).1
            (firstJetPair (coordinateMap G (p i)) y).2 ∧
          b/2 ≤ ‖realSecondTensor (coordinateMap G (p i)) y‖ ∧ ∀ j,
            ε/2 ≤ (P i a).Q j H' ∧
            (ε/4)*‖realSecondTensor (coordinateMap G (p i)) y‖ ≤
              ‖secondQuadratic (realSecondTensor (coordinateMap G (p i)) y) (-((P i a).ξ j).2,((P i a).ξ j).1)‖ ∧
            Good (realSecondTensor (coordinateMap G (p i)) y) ((P i a).ξ j)) ∧
        (∀ G, CoordinateJetBall p r z F G → AtlasPairMargins p ψ s (z^6) κ ξ w G) ∧
        AtlasMetricDecomposition g p ψ s P z w ∧
        AtlasPhaseDenominatorBounds p r ψ s P z F w ε b C W := by
  classical
  obtain ⟨phaseStock,weightStock,z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,hselect⟩ :=
    fixed_atlas_polynomial_metric_decomposition_with_catalog g p r ψ hball hψ hcompact hsource hK hKU hsquare R c A b hc hA hb
  refine ⟨phaseStock,weightStock,z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,?_⟩
  intro z hz hzsmall F hF hFb hFm
  obtain ⟨s,P,ξ,w,hPstock,hwStock,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair,hdec⟩ :=
    hselect z hz hzsmall F hF hFb hFm
  refine ⟨s,P,ξ,w,hPstock,hwStock,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair,hdec,?_⟩
  intro G hG i a j q hq
  have hcoord : coordinateChart (p i) q ∈ tsupport (cutoff (z^6) a.val) :=
    normalizedCutoff_tsupport (s i) (z^6) a.val
      (refinedCutoff_tsupport_inner (p i) (hsource i) (s i) (z^6) a.val hq)
  have hp := hpoint G hG i a (coordinateChart (p i) q)
    (coordinateMetric g (p i) (coordinateChart (p i) q)) hcoord (by simpa using hδ.le)
  exact weighted_selected_denominators (atlasSecondTensor G (p i) q) ((P i a).ξ j)
    hε hb (zero_le_one.trans hC) hp.2.1 (hPB i a j).2.1
    (hw (i,a.val,j)).1 (hw (i,a.val,j)).2 (hp.2.2 j).2.1

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
theorem fixed_atlas_phase_data_with_denominator_bounds (g : SmoothMetric M)
    (p : ι → M) (r : ι → ℝ) (ψ : ι → M → ℝ)
    (hball : ∀ i, Metric.closedBall (coordinateCenter (p i)) (r i) ⊆ coordinateDomain (p i))
    (hψ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i))
    (hcompact : ∀ i, HasCompactSupport (ψ i))
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hK : ∀ i, IsCompact (chartSupport (p i) (ψ i)))
    (hKU : ∀ i, chartSupport (p i) (ψ i) ⊆ Metric.ball (coordinateCenter (p i)) (r i))
    (hsquare : ∀ q, ∑ i, (ψ i q)^2 = 1)
    (R c A b : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) :
    ∃ z₀ D C ε δ W κ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < D ∧ 1 ≤ C ∧
      0 < ε ∧ 0 < δ ∧ 0 < W ∧ 0 < κ ∧
      ∃ J : ℕ → ℝ, (∀ j, 1 ≤ J j) ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedBound (Metric.ball (coordinateCenter (p i)) (r i)) z 3 A (coordinateMap F (p i))) →
      (∀ i y, y ∈ Metric.ball (coordinateCenter (p i)) (r i) →
        ‖firstJetPair (coordinateMap F (p i)) y‖ ≤ R ∧
        c ≤ NormalFrame.gramDet (firstJetPair (coordinateMap F (p i)) y).1
          (firstJetPair (coordinateMap F (p i)) y).2 ∧ b ≤ ‖realSecondTensor (coordinateMap F (p i)) y‖) →
      ∃ (s : ι → Finset Index) (P : ∀ i, {a // a ∈ s i} → PhaseBasis)
        (ξ : AtlasCellPhase (ι := ι) → SmallModes.Base) (w : AtlasCellPhase (ι := ι) → ℝ),
        (∑ i, ((s i).card : ℝ)) ≤ D/z^12 ∧
        (∀ i, chartSupport (p i) (ψ i) ⊆ coverRegion (s i) (z^6)) ∧
        (∀ i a j y, y ∈ coverRegion (s i) (z^6) →
          ‖iteratedFDeriv ℝ j (normalizedCutoff (s i) (z^6) a) y‖ ≤ J j/z^(6*j)) ∧
        (∀ i a, ContMDiff planeModel 𝓘(ℝ) ∞ (refinedCutoff (p i) (ψ i) (s i) (z^6) a)) ∧
        (∀ q, ∑ i, ∑ a ∈ s i, (refinedCutoff (p i) (ψ i) (s i) (z^6) a q)^2 = 1) ∧
        (∀ i (a : {a // a ∈ s i}) j, ξ (i,a.val,j) = (P i a).ξ j ∧
          ‖(P i a).ξ j‖ ≤ C ∧ ‖(P i a).Q j‖ ≤ C) ∧
        (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
        (∀ G, CoordinateJetBall p r z F G → ∀ i (a : {a // a ∈ s i}) y H',
          y ∈ tsupport (cutoff (z^6) a.val) → ‖H'-coordinateMetric g (p i) y‖ ≤ δ →
          c/2 ≤ NormalFrame.gramDet (firstJetPair (coordinateMap G (p i)) y).1
            (firstJetPair (coordinateMap G (p i)) y).2 ∧
          b/2 ≤ ‖realSecondTensor (coordinateMap G (p i)) y‖ ∧ ∀ j,
            ε/2 ≤ (P i a).Q j H' ∧
            (ε/4)*‖realSecondTensor (coordinateMap G (p i)) y‖ ≤
              ‖secondQuadratic (realSecondTensor (coordinateMap G (p i)) y) (-((P i a).ξ j).2,((P i a).ξ j).1)‖ ∧
            Good (realSecondTensor (coordinateMap G (p i)) y) ((P i a).ξ j)) ∧
        (∀ G, CoordinateJetBall p r z F G → AtlasPairMargins p ψ s (z^6) κ ξ w G) ∧
        AtlasMetricDecomposition g p ψ s P z w ∧
        AtlasPhaseDenominatorBounds p r ψ s P z F w ε b C W := by
  obtain ⟨phaseStock,weightStock,z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,hselect⟩ :=
    fixed_atlas_phase_data_with_denominator_bounds_with_catalog g p r ψ hball hψ hcompact hsource hK hKU hsquare R c A b hc hA hb
  refine ⟨z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,?_⟩
  intro z hz hzsmall F hF hFb hFm
  obtain ⟨s,P,ξ,w,_,_,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair,hdec,hden⟩ :=
    hselect z hz hzsmall F hF hFb hFm
  exact ⟨s,P,ξ,w,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair,hdec,hden⟩

end ClosedSurfaceR4

end

end OAI
