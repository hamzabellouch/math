import OAI.Geometry.Immersion.ClosedSurface.GridPhases
import OAI.Geometry.Immersion.ClosedSurface.AtlasWeights
import OAI.Geometry.Immersion.ClosedSurface.MetricBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set PhaseGrid WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {ι : Type*} [Fintype ι]




def CoordinateJetBall (p : ι → M) (r : ι → ℝ) (z : ℝ) (F G : M → Space) : Prop :=
  ContMDiff planeModel spaceModel ∞ G ∧ ∀ i y,
    y ∈ Metric.ball (coordinateCenter (p i)) (r i) →
    ‖firstJetPair (coordinateMap F (p i)) y-firstJetPair (coordinateMap G (p i)) y‖ ≤ z^4 ∧
    ‖secondJetTriple (coordinateMap F (p i)) y-secondJetTriple (coordinateMap G (p i)) y‖ ≤ z^4

def AtlasPairMargins (p : ι → M) (ψ : ι → M → ℝ) (s : ι → Finset Index)
    (h κ : ℝ) (ξ : AtlasCellPhase (ι := ι) → SmallModes.Base) (w : AtlasCellPhase (ι := ι) → ℝ)
    (G : M → Space) : Prop :=
  ∀ a b j q, a ≠ b → atlasActive p ψ s h a q → atlasActive p ψ s h b q →
    q ∈ tsupport (ψ j) →
    κ*‖atlasSecondTensor G (p j) q‖ ≤ ‖secondQuadratic (atlasSecondTensor G (p j) q)
      (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
         w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
        (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q +
         w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
    κ*‖atlasSecondTensor G (p j) q‖ ≤ ‖secondQuadratic (atlasSecondTensor G (p j) q)
      (-(w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
         w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).2,
        (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q -
         w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q).1)‖ ∧
    Good (atlasSecondTensor G (p j) q)
      (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q + w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q) ∧
    Good (atlasSecondTensor G (p j) q)
      (w a • atlasPhaseCovector (p a.1) (p j) (ξ a) q - w b • atlasPhaseCovector (p b.1) (p j) (ξ b) q)






omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
theorem fixed_atlas_polynomial_good_phases_with_catalog (g : SmoothMetric M)
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
        (∀ G, CoordinateJetBall p r z F G → AtlasPairMargins p ψ s (z^6) κ ξ w G) := by
  classical
  obtain ⟨T,L,hT,hT0,hTd,hL,hTrange,hLip⟩ := finite_atlas_metric_bounds g p r hball
  obtain ⟨phaseStock,ε,C,δ,z₁,W₁,κ₁,hε,hC,hδ,hz₁,hz₁1,hW₁,hκ₁,hphase⟩ :=
    actual_polynomial_grid_phases_with_catalog hT hT0 hTd R c A b L hc hA hb hL
  obtain ⟨weightStock,W,κ,hW,hκ,hweight⟩ := atlas_phase_weight_constants_with_catalog p ψ hsource hcompact
    (C := C) (div_pos hε (by norm_num : (0:ℝ) < 4)) (M → Space)
  have hpart (i : ι) := compact_polynomial_square_partition (hK i) Metric.isOpen_ball (hKU i)
  choose zi Di Ji hzi hzi1 hDi hJi hgrid using hpart
  obtain ⟨z₂,hz₂,hz₂1,hz₂i⟩ := finite_positive_threshold zi hzi
  let D : ℝ := 1 + ∑ i, Di i
  have hD : 0 < D := by
    have hh : 0 ≤ ∑ i, Di i := Finset.sum_nonneg (fun i _ => (hDi i).le)
    dsimp [D]; linarith
  let J : ℕ → ℝ := fun j => 1 + ∑ i, Ji i j
  have hJ (j : ℕ) : 1 ≤ J j := by
    have hh : 0 ≤ ∑ i, Ji i j := Finset.sum_nonneg (fun i _ => (by linarith [hJi i j]))
    dsimp [J]; linarith
  refine ⟨phaseStock,weightStock,min z₁ z₂,D,C,ε,δ,W,κ,lt_min hz₁ hz₂,(min_le_left _ _).trans hz₁1,
    hD,hC,hε,hδ,hW,hκ,J,hJ,?_⟩
  intro z hz hzsmall F hF hFb hFm
  have hgr (i : ι) := hgrid i z hz ((hzsmall.trans (min_le_right _ _)).trans (hz₂i i))
  choose s hcard hopen hinner houter hsub hsmooth hderiv hsquares hsupp using hgr
  have hchoose (i : ι) := hphase z hz (hzsmall.trans (min_le_left _ _))
    (coordinateMap F (p i)) (Metric.ball (coordinateCenter (p i)) (r i)) Metric.isOpen_ball
    (convex_ball _ _) ((coordinateMap_smoothOn hF (p i)).mono
      (Metric.ball_subset_closedBall.trans (hball i))) (hFb i) (hFm i)
    (coordinateMetric g (p i)) (hTrange i) (hLip i) (s i) (hsub i)
  choose P wlocal hPstock hPB hwlocal hpoint hpairlocal using hchoose
  let ξ : AtlasCellPhase (ι := ι) → SmallModes.Base := fun a =>
    if ha : a.2.1 ∈ s a.1 then (P a.1 ⟨a.2.1,ha⟩).ξ a.2.2 else dx
  have hξ (a : AtlasCellPhase (ι := ι)) : ‖ξ a‖ ≤ C := by
    dsimp [ξ]
    split_ifs with ha
    · exact (hPB a.1 ⟨a.2.1,ha⟩ a.2.2).1
    · simpa [dx,Prod.norm_def] using hC
  have hfball : CoordinateJetBall p r z F F := by
    refine ⟨hF,fun i y hy => ?_⟩
    simp only [sub_self,norm_zero]
    exact ⟨by positivity,by positivity⟩
  let family : (M → Space) → M → Space := fun G => if CoordinateJetBall p r z F G then G else F
  have hfamily (G : M → Space) : CoordinateJetBall p r z F (family G) := by
    dsimp [family]
    split_ifs with h
    · exact h
    · exact hfball
  have hmarg (G : M → Space) (a : AtlasCellPhase (ι := ι)) (q : M)
      (ha : atlasActive p ψ s (z^6) a q) :
      atlasGram (family G) (p a.1) q ≠ 0 ∧ atlasSecondTensor (family G) (p a.1) q ≠ 0 ∧
      (ε/4)*‖atlasSecondTensor (family G) (p a.1) q‖ ≤
        ‖secondQuadratic (atlasSecondTensor (family G) (p a.1) q) (-(ξ a).2,(ξ a).1)‖ := by
    have hcoord : coordinateChart (p a.1) q ∈ tsupport (cutoff (z^6) a.2.1) :=
      normalizedCutoff_tsupport (s a.1) (z^6) a.2.1
        (refinedCutoff_tsupport_inner (p a.1) (hsource a.1) (s a.1) (z^6) a.2.1 ha.2)
    have hd := (hfamily G).2 a.1 _ ((hsub a.1 a.2.1 ha.1).2 hcoord)
    have hp := hpoint a.1 ⟨a.2.1,ha.1⟩ (coordinateChart (p a.1) q)
      (coordinateMap (family G) (p a.1)) (coordinateMetric g (p a.1) (coordinateChart (p a.1) q))
      hcoord hd.1 hd.2 (by simpa using hδ.le)
    refine ⟨ne_of_gt ((half_pos hc).trans_le hp.1),?_,?_⟩
    · exact norm_pos_iff.mp ((half_pos hb).trans_le hp.2.1)
    · simpa only [atlasSecondTensor,ξ,dite_eq_left ha.1] using (hp.2.2 a.2.2).2.1
  obtain ⟨w,hwStock,hw,hpairs⟩ := hweight (z^6) (pow_pos hz _) s ξ hξ family (fun G => (hfamily G).1) hmarg
  obtain ⟨hsm,hcomp,hsp,hsq⟩ := global_grid_square_partition p ψ hψ hsource hcompact hsquare s
    (z^6) (pow_pos hz _) hinner
  refine ⟨s,P,ξ,w,hPstock,hwStock,?_,hinner,?_,hsm,hsq,?_,hw,?_,?_⟩
  · calc
      (∑ i, ((s i).card : ℝ)) ≤ ∑ i, Di i/z^12 := Finset.sum_le_sum (fun i _ => hcard i)
      _ = (∑ i, Di i)/z^12 := (Finset.sum_div _ _ _).symm
      _ ≤ D/z^12 := div_le_div_of_nonneg_right (by dsimp [D]; linarith) (pow_pos hz _).le
  · intro i a j y hy
    apply (hderiv i a j y hy).trans
    apply div_le_div_of_nonneg_right _ (pow_pos hz _).le
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun k _ => (show (0:ℝ) ≤ Ji k j from (by linarith [hJi k j]))) (Finset.mem_univ i)
    dsimp [J]; linarith
  · intro i a j
    exact ⟨by simp only [ξ,dite_eq_left a.property],hPB i a j⟩
  · intro G hG i a y H' hy hH'
    have hd := hG.2 i y ((hsub i a.val a.property).2 hy)
    exact hpoint i a y (coordinateMap G (p i)) H' hy hd.1 hd.2 hH'
  · intro G hG
    have he : family G = G := ite_eq_left hG
    intro a b j q hab ha hb hq
    simpa only [he] using hpairs G a b j q hab ha hb hq

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
theorem fixed_atlas_polynomial_good_phases (g : SmoothMetric M)
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
        (∀ G, CoordinateJetBall p r z F G → AtlasPairMargins p ψ s (z^6) κ ξ w G) := by
  obtain ⟨phaseStock,weightStock,z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,hselect⟩ :=
    fixed_atlas_polynomial_good_phases_with_catalog g p r ψ hball hψ hcompact hsource hK hKU hsquare R c A b hc hA hb
  refine ⟨z₀,D,C,ε,δ,W,κ,hz₀,hz₀1,hD,hC,hε,hδ,hW,hκ,J,hJ,?_⟩
  intro z hz hzsmall F hF hFb hFm
  obtain ⟨s,P,ξ,w,_,_,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair⟩ :=
    hselect z hz hzsmall F hF hFb hFm
  exact ⟨s,P,ξ,w,hcard,hcover,hder,hsm,hsq,hPB,hw,hpoint,hpair⟩

end ClosedSurfaceR4

end

end OAI
