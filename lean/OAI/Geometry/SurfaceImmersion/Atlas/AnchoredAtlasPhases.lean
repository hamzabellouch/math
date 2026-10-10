import OAI.Geometry.SurfaceImmersion.Atlas.AnchoredGridPhases
import OAI.Geometry.SurfaceImmersion.Atlas.AnchoredGridCover
import OAI.Geometry.SurfaceImmersion.Atlas.MetricReadBounds
import OAI.Geometry.SurfaceImmersion.Atlas.GridCellGeometry
import OAI.Geometry.Immersion.ClosedSurface.GoodAtlas

namespace OAI

/-! Phase catalogs for a fixed smoothing atlas, using geometry only on its weight supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates PhaseGeometry PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def ReadJetBall (z : ℝ) (F G : M → Space) : Prop :=
  ContMDiff planeModel spaceModel ∞ G ∧ ∀ i x,
    x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
    ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x-
      firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤ z^4 ∧
    ‖secondJetTriple (spaceCoordinates ∘ A.vectorPlaneRead i F) x-
      secondJetTriple (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤ z^4

lemma readJetBall_self (z : ℝ) {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F) :
    A.ReadJetBall z F F := by
  refine ⟨hF,fun i x hx => ?_⟩
  simp only [sub_self,norm_zero]
  exact ⟨by positivity,by positivity⟩

omit [CompactSpace M] in
lemma read_gram_eq_atlas (F : M → Space) (i : A.centers)
    (houter : ∀ p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    NormalFrame.gramDet
      (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) (coordinateChart (i : M) p)).1
      (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) (coordinateChart (i : M) p)).2 =
      atlasGram F (i : M) p := by
  have he := (A.vectorPlaneRead_eventually_coordinateMap F i houter hp).fderiv_eq (𝕜 := ℝ)
  change NormalFrame.gramDet
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p)) SmallModes.dx)
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p)) SmallModes.dy) = _
  exact
    congrArg (fun L : SmallModes.Base →L[ℝ] RVec 4 => NormalFrame.gramDet (L SmallModes.dx) (L SmallModes.dy)) he

omit [CompactSpace M] in
lemma read_second_eq_atlas (F : M → Space) (i : A.centers)
    (houter : ∀ p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) (coordinateChart (i : M) p) =
      atlasSecondTensor F (i : M) p :=
  (realSecondTensor_eventuallyEq (A.vectorPlaneRead_eventually_coordinateMap F i houter hp)).eq_of_nhds

theorem anchored_atlas_phases (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ phaseStock : Finset PhaseBasis, ∃ weightStock : Finset ℝ,
    ∃ z₀ K C ε W κ : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < K ∧ 1 ≤ C ∧
      0 < ε ∧ 0 < W ∧ 0 < κ ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∃ (s : A.centers → Finset Index) (P : ∀ i, (s i) → PhaseBasis)
      (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
      (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ i a, P i a ∈ phaseStock) ∧ (∀ a, w a ∈ weightStock) ∧
      (∑ i, ((s i).card : ℝ)) ≤ K/z^12 ∧
      (∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (s i) (z^6)) ∧
      (∀ i a j, ξ (i,a.val,j) = (P i a).ξ j ∧
        ‖(P i a).ξ j‖ ≤ C ∧ ‖(P i a).Q j‖ ≤ C) ∧
      (∀ a, 1 ≤ w a ∧ w a ≤ W) ∧
      (∀ G, A.ReadJetBall z F G → ∀ i (a : s i) x,
        x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        x ∈ tsupport (cutoff (z^6) a.val) →
        c/4 ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).2 ∧
        b/2 ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ∧ ∀ j,
          ε/2 ≤ (P i a).Q j (A.tensorPlaneRead i g.inner x) ∧
          (ε/4)*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ≤
            ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x)
              (-((P i a).ξ j).2,((P i a).ξ j).1)‖ ∧
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x) ((P i a).ξ j)) ∧
      (∀ G, A.ReadJetBall z F G →
        AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s (z^6) κ ξ w G) := by
  classical
  obtain ⟨T,L,hT,hT0,hTd,hL,hTrange,_,hLip⟩ := A.metric_plane_read_bounds g
  obtain ⟨stock,ε,C,δ,z₁,W₁,κ₁,hε,hC,hδ,hz₁,hz₁1,_hW₁,_hκ₁,hselect⟩ :=
    anchored_polynomial_grid_phases hT hT0 hTd R c B b L hc hB hb (zero_le_one.trans hL)
  obtain ⟨weightStock,W,κ,hW,hκ,hweight⟩ :=
    atlas_phase_weight_constants_with_catalog (fun i : A.centers => (i : M)) A.weight
      (fun i => by simpa only [chart_source] using A.weight_support i)
      (fun i => (isClosed_tsupport _).isCompact) (C := C)
      (by positivity : 0 < ε/4) (M → Space)
  choose zi Ki hzi hzi1 hKi hgrid using fun i : A.centers =>
    compact_anchored_polynomial_grid (modeSupport (A.chartWeightCompact i)).isCompact
  obtain ⟨z₂,hz₂,hz₂1,hz₂i⟩ := finite_positive_threshold zi hzi
  let K : ℝ := 1+∑ i, Ki i
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => (hKi i).le)
    change 0 < 1+∑ i : A.centers, Ki i
    linarith
  refine ⟨stock,weightStock,min z₁ z₂,K,C,ε,W,κ,lt_min hz₁ hz₂,
    (min_le_left _ _).trans hz₁1,hK,hC,hε,hW,hκ,?_⟩
  intro z hz hzsmall F hF hFb hFm
  choose s hcard hcover hanchors using fun i : A.centers =>
    hgrid i z hz ((hzsmall.trans (min_le_right _ _)).trans (hz₂i i))
  have hchoose (i : A.centers) := hselect z hz (hzsmall.trans (min_le_left _ _))
    (spaceCoordinates ∘ A.vectorPlaneRead i F)
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) (hFb i)
    (A.tensorPlaneRead i g.inner) (hLip i) (s i) (by
      intro a ha
      obtain ⟨x,hx,hd⟩ := hanchors i a ha
      exact ⟨x,hd,(hFm i x hx).1,(hFm i x hx).2.1,(hFm i x hx).2.2,hTrange i x hx⟩)
  choose P wlocal hPstock hPB hwlocal hpoint hlocalPair using hchoose
  let ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base := fun a =>
    if ha : a.2.1 ∈ s a.1 then (P a.1 ⟨a.2.1,ha⟩).ξ a.2.2 else SmallModes.dx
  have hξ (a : AtlasCellPhase (ι := A.centers)) : ‖ξ a‖ ≤ C := by
    dsimp [ξ]
    split_ifs with ha
    · exact (hPB a.1 ⟨a.2.1,ha⟩ a.2.2).1
    · simpa [SmallModes.dx,Prod.norm_def] using hC
  have hpt (G : M → Space) (hG : A.ReadJetBall z F G) (i : A.centers) (a : s i)
      (x : SmallModes.Base) (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
      (ha : x ∈ tsupport (cutoff (z^6) a.val)) :=
    hpoint i a x (spaceCoordinates ∘ A.vectorPlaneRead i G) (A.tensorPlaneRead i g.inner x)
      ha (hG.2 i x hx).1 (hG.2 i x hx).2 (by simpa using hδ.le)
  let family : (M → Space) → M → Space := fun G => if A.ReadJetBall z F G then G else F
  have hfamily (G : M → Space) : A.ReadJetBall z F (family G) := by
    dsimp [family]
    split_ifs with h
    · exact h
    · exact A.readJetBall_self z hF
  have hmarg (G : M → Space) (a : AtlasCellPhase (ι := A.centers)) (p : M)
      (ha : atlasActive (fun i : A.centers => (i : M)) A.weight s (z^6) a p) :
      atlasGram (family G) (a.1 : M) p ≠ 0 ∧ atlasSecondTensor (family G) (a.1 : M) p ≠ 0 ∧
      (ε/4)*‖atlasSecondTensor (family G) (a.1 : M) p‖ ≤
        ‖secondQuadratic (atlasSecondTensor (family G) (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖ := by
    have hp := refinedCutoff_tsupport_outer (a.1 : M) (A.weight a.1) (s a.1) (z^6) a.2.1 ha.2
    have hx : coordinateChart (a.1 : M) p ∈
        (modeSupport (A.chartWeightCompact a.1) : Set SmallModes.Base) :=
      ⟨chart (a.1 : M) p,⟨p,hp,rfl⟩,rfl⟩
    have hcutt := normalizedCutoff_tsupport (s a.1) (z^6) a.2.1
      (refinedCutoff_tsupport_inner (a.1 : M)
        (by simpa only [chart_source] using A.weight_support a.1) (s a.1) (z^6) a.2.1 ha.2)
    have hh := hpt (family G) (hfamily G) a.1 ⟨a.2.1,ha.1⟩ _ hx hcutt
    rw [A.read_gram_eq_atlas (family G) a.1 (houter a.1) hp,
      A.read_second_eq_atlas (family G) a.1 (houter a.1) hp] at hh
    refine ⟨ne_of_gt ((by positivity : 0 < c/4).trans_le hh.1),
      norm_pos_iff.mp ((half_pos hb).trans_le hh.2.1),?_⟩
    simpa only [ξ,dite_eq_left ha.1] using (hh.2.2 a.2.2).2.1
  obtain ⟨w,hwStock,hw,hpairs⟩ := hweight (z^6) (pow_pos hz _) s ξ hξ family
    (fun G => (hfamily G).1) hmarg
  refine ⟨s,P,ξ,w,hPstock,hwStock,?_,hcover,?_,hw,hpt,?_⟩
  · calc
      (∑ i, ((s i).card : ℝ)) ≤ ∑ i, Ki i/z^12 := Finset.sum_le_sum (fun i _ => hcard i)
      _ = (∑ i, Ki i)/z^12 := (Finset.sum_div _ _ _).symm
      _ ≤ K/z^12 := div_le_div_of_nonneg_right (by
        change (∑ i : A.centers, Ki i) ≤ 1+∑ i : A.centers, Ki i
        linarith) (pow_pos hz _).le
  · intro i a j
    exact ⟨by simp only [ξ,dite_eq_left a.property],hPB i a j⟩
  · intro G hG a d j p had ha hd hp
    have he : family G = G := ite_eq_left hG
    simpa only [he] using hpairs G a d j p had ha hd hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
