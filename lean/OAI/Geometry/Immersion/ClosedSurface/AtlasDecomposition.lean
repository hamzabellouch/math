import OAI.Geometry.Immersion.ClosedSurface.PhaseDifferentials
import OAI.Geometry.Immersion.ClosedSurface.GoodAtlas
import OAI.Geometry.Immersion.ClosedSurface.TangentDecomposition

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] {ι : Type*}




omit [T2Space M] [CompactSpace M] in
theorem atlas_pair_margins_actual
    (p : ι → M) (ψ : ι → M → ℝ) (s : ι → Finset Index)
    (h κ : ℝ) (ξ : AtlasCellPhase (ι := ι) → SmallModes.Base)
    (w : AtlasCellPhase (ι := ι) → ℝ) (G : M → Space)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hm : AtlasPairMargins p ψ s h κ ξ w G)
    (a b : AtlasCellPhase (ι := ι)) (j : ι) (q : M)
    (hab : a ≠ b) (ha : atlasActive p ψ s h a q)
    (hb : atlasActive p ψ s h b q) (hq : q ∈ tsupport (ψ j)) :
    let u := phaseDerivative
      (((w a • atlasPhase (p a.1) (ξ a)) + (w b • atlasPhase (p b.1) (ξ b))) ∘
        (coordinateChart (p j)).symm) (coordinateChart (p j) q)
    let v := phaseDerivative
      (((w a • atlasPhase (p a.1) (ξ a)) - (w b • atlasPhase (p b.1) (ξ b))) ∘
        (coordinateChart (p j)).symm) (coordinateChart (p j) q)
    κ*‖atlasSecondTensor G (p j) q‖ ≤
      ‖secondQuadratic (atlasSecondTensor G (p j) q) (-u.2,u.1)‖ ∧
    κ*‖atlasSecondTensor G (p j) q‖ ≤
      ‖secondQuadratic (atlasSecondTensor G (p j) q) (-v.2,v.1)‖ ∧
    Good (atlasSecondTensor G (p j) q) u ∧ Good (atlasSecondTensor G (p j) q) v := by
  have hqa : q ∈ (coordinateChart (p a.1)).source := by
    rw [coordinateChart_source]
    exact hsource a.1 (refinedCutoff_tsupport_outer (p a.1) (ψ a.1) (s a.1) h a.2.1 ha.2)
  have hqb : q ∈ (coordinateChart (p b.1)).source := by
    rw [coordinateChart_source]
    exact hsource b.1 (refinedCutoff_tsupport_outer (p b.1) (ψ b.1) (s b.1) h b.2.1 hb.2)
  have hqj : q ∈ (coordinateChart (p j)).source := by
    rw [coordinateChart_source]
    exact hsource j hq
  dsimp only
  rw [atlasPhaseCovector_add _ _ _ _ _ _ _ hqj hqa hqb,
    atlasPhaseCovector_sub _ _ _ _ _ _ _ hqj hqa hqb]
  exact hm a b j q hab ha hb hq

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set PhaseGrid WeightedEstimates Bundle Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {ι : Type*} [Fintype ι]


def selectedAmplitude (g : SmoothMetric M) (p : ι → M) (ψ : ι → M → ℝ)
    (s : ι → Finset Index) (P : ∀ i, {a // a ∈ s i} → PhaseBasis)
    (z : ℝ) (w : AtlasCellPhase (ι := ι) → ℝ)
    (k : Σ i, {a // a ∈ s i}) (j : Fin 3) : M → ℝ :=
  metricPhaseAmplitude g (p k.1) ((P k.1 k.2).Q j)
    (refinedCutoff (p k.1) (ψ k.1) (s k.1) (z^6) k.2.val) (w (k.1,k.2.val,j))


def AtlasMetricDecomposition (g : SmoothMetric M) (p : ι → M) (ψ : ι → M → ℝ)
    (s : ι → Finset Index) (P : ∀ i, {a // a ∈ s i} → PhaseBasis)
    (z : ℝ) (w : AtlasCellPhase (ι := ι) → ℝ) : Prop :=
  (∀ k j, ContMDiff planeModel 𝓘(ℝ) ∞ (selectedAmplitude g p ψ s P z w k j)) ∧
  (∀ k j, HasCompactSupport (selectedAmplitude g p ψ s P z w k j)) ∧
  ∀ (q : M) (v u : TangentSpace planeModel q),
    ∑ (k : Σ i, {a // a ∈ s i}), ∑ j,
      (selectedAmplitude g p ψ s P z w k j q)^2 *
        scalarDifferential (atlasPhase (p k.1) (w (k.1,k.2.val,j) • (P k.1 k.2).ξ j)) q v *
        scalarDifferential (atlasPhase (p k.1) (w (k.1,k.2.val,j) • (P k.1 k.2).ξ j)) q u =
      g.inner q v u

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
lemma assemble_selected_metric (g : SmoothMetric M) (p : ι → M) (ψ : ι → M → ℝ)
    (s : ι → Finset Index) (P : ∀ i, {a // a ∈ s i} → PhaseBasis)
    (z : ℝ) (w : AtlasCellPhase (ι := ι) → ℝ)
    (hsm : ∀ i a, ContMDiff planeModel 𝓘(ℝ) ∞ (refinedCutoff (p i) (ψ i) (s i) (z^6) a))
    (hcompact : ∀ i, HasCompactSupport (ψ i))
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hsquare : ∀ q, ∑ i, ∑ a ∈ s i, (refinedCutoff (p i) (ψ i) (s i) (z^6) a q)^2 = 1)
    (hw : ∀ a, 1 ≤ w a)
    (hpos : ∀ i (a : {a // a ∈ s i}) q,
      q ∈ tsupport (refinedCutoff (p i) (ψ i) (s i) (z^6) a.val) → ∀ j,
      0 < (P i a).Q j (coordinateMetric g (p i) (coordinateChart (p i) q))) :
    AtlasMetricDecomposition g p ψ s P z w := by
  classical
  apply global_metric_phase_decomposition g
    (fun k : Σ i, {a // a ∈ s i} => p k.1) (fun k => P k.1 k.2)
    (fun k => refinedCutoff (p k.1) (ψ k.1) (s k.1) (z^6) k.2.val)
    (fun k j => w (k.1,k.2.val,j))
  · exact fun k => hsm k.1 k.2.val
  · exact fun k => refinedCutoff_hasCompactSupport _ _ _ _ _ (hcompact k.1)
  · intro k q hq
    rw [coordinateChart_source]
    exact hsource k.1 (refinedCutoff_tsupport_outer _ _ _ _ _ hq)
  · intro q
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ i, ∑ a ∈ s i, (refinedCutoff (p i) (ψ i) (s i) (z^6) a q)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_coe_sort (s i) (fun a => (refinedCutoff (p i) (ψ i) (s i) (z^6) a q)^2)
      _ = 1 := hsquare q
  · intro k j
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hw _))
  · exact fun k q hq j => hpos k.1 k.2 q hq j



omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
theorem fixed_atlas_polynomial_metric_decomposition_with_catalog (g : SmoothMetric M)
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
        AtlasMetricDecomposition g p ψ s P z w := by
  classical
  obtain ⟨phaseStock,weightStock,z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,hselect⟩ :=
    fixed_atlas_polynomial_good_phases_with_catalog g p r ψ hball hψ hcompact hsource hK hKU hsquare R c A b hc hA hb
  refine ⟨phaseStock,weightStock,z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,?_⟩
  intro z hz hzsmall F hF hFb hFm
  obtain ⟨s,P,ξ,w,hPstock,hwStock,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair⟩ :=
    hselect z hz hzsmall F hF hFb hFm
  refine ⟨s,P,ξ,w,hPstock,hwStock,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair,?_⟩
  apply assemble_selected_metric g p ψ s P z w hsm hcompact hsource hsq (fun a => (hw a).1)
  intro i a q hq j
  have hfball : CoordinateJetBall p r z F F := by
    refine ⟨hF,fun i y hy => ?_⟩
    simp only [sub_self,norm_zero]
    exact ⟨by positivity,by positivity⟩
  have hcoord : coordinateChart (p i) q ∈ tsupport (cutoff (z^6) a.val) :=
    normalizedCutoff_tsupport (s i) (z^6) a.val
      (refinedCutoff_tsupport_inner (p i) (hsource i) (s i) (z^6) a.val hq)
  have hp := hpoint F hfball i a (coordinateChart (p i) q)
    (coordinateMetric g (p i) (coordinateChart (p i) q)) hcoord (by simpa using hδ.le)
  exact (half_pos hε).trans_le (hp.2.2 j).1

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
theorem fixed_atlas_polynomial_metric_decomposition (g : SmoothMetric M)
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
        AtlasMetricDecomposition g p ψ s P z w := by
  obtain ⟨phaseStock,weightStock,z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,hselect⟩ :=
    fixed_atlas_polynomial_metric_decomposition_with_catalog g p r ψ hball hψ hcompact hsource hK hKU hsquare R c A b hc hA hb
  refine ⟨z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,?_⟩
  intro z hz hzsmall F hF hFb hFm
  obtain ⟨s,P,ξ,w,_,_,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair,hdec⟩ :=
    hselect z hz hzsmall F hF hFb hFm
  exact ⟨s,P,ξ,w,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair,hdec⟩

end ClosedSurfaceR4

end

end OAI
