import OAI.Geometry.SurfaceImmersion.Atlas.AnchoredAtlasPhases
import OAI.Geometry.Immersion.ClosedSurface.DenominatorBounds
import OAI.Geometry.Immersion.ClosedSurface.PhaseWeights

namespace OAI

/-! Exact support and denominator consequences of the selected anchored phases. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry PhaseGrid
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def SelectedGridPointMargins (g : SmoothMetric M) (z : ℝ)
    (s : A.centers → Finset Index) (P : ∀ i, (s i) → PhaseBasis)
    (G : M → Space) (c b ε : ℝ) : Prop :=
  ∀ i (a : s i) x,
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
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x) ((P i a).ξ j)

lemma cellChartCompact_cutoff {z : ℝ} (s : A.centers → Finset Index)
    (i : A.centers) (a : s i) {x : SmallModes.Base}
    (hx : x ∈ (modeSupport (A.cellChartCompact i (s i) (z^6) a.val) : Set SmallModes.Base)) :
    x ∈ tsupport (cutoff (z^6) a.val) := by
  obtain ⟨y,⟨p,hp,rfl⟩,rfl⟩ := hx
  exact normalizedCutoff_tsupport (s i) (z^6) a.val
    (refinedCutoff_tsupport_inner (i : M)
      (by simpa only [chart_source] using A.weight_support i) (s i) (z^6) a.val hp)

lemma selected_grid_cover_geometry {g : SmoothMetric M} {z c b ε : ℝ} (hz : 0 < z)
    (hc : 0 < c) {s : A.centers → Finset Index} {P : ∀ i, (s i) → PhaseBasis}
    {G : M → Space}
    (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coverRegion (s i) (z^6))
    (hp : A.SelectedGridPointMargins g z s P G c b ε) :
    ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i G) x) ∧
      b/2 ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x‖ ∧
      ‖(NormalFrame.gramDet
        (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i G) x)
        (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i G) x))⁻¹‖ ≤ 4/c := by
  intro i x hx
  obtain ⟨a,ha,hxa⟩ := coverRegion_covers (s i) (z^6) (hcover i hx)
  have hcut : x ∈ tsupport (cutoff (z^6) a) := by
    apply subset_tsupport
    change cutoff (z^6) a x ≠ 0
    rw [cutoff_one_on_cell (pow_pos hz 6) a hxa]
    exact one_ne_zero
  have hh := hp i ⟨a,ha⟩ x hx hcut
  have hDpos : 0 < NormalFrame.gramDet
      (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).1
      (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i G) x).2 :=
    (by positivity : 0 < c/4).trans_le hh.1
  refine ⟨injective_of_gramDet_ne_zero _ hDpos.ne',hh.2.1,?_⟩
  have hi := one_div_le_one_div_of_le (by positivity : 0 < c/4) hh.1
  change 0 < NormalFrame.gramDet
    (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead i G) x)
    (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead i G) x) at hDpos
  rw [norm_inv,Real.norm_eq_abs,abs_of_pos hDpos]
  calc
    _ ≤ (c/4)⁻¹ := by simpa only [one_div,firstJetPair] using hi
    _ = 4/c := inv_div c 4

lemma selected_grid_cell_geometry {g : SmoothMetric M} {z c b ε C W : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hC : 0 ≤ C)
    {s : A.centers → Finset Index} {P : ∀ i, (s i) → PhaseBasis} {G : M → Space}
    (w : AtlasCellPhase (ι := A.centers) → ℝ)
    (hp : A.SelectedGridPointMargins g z s P G c b ε)
    (hP : ∀ i a j, ‖(P i a).ξ j‖ ≤ C)
    (hw : ∀ a, 1 ≤ w a ∧ w a ≤ W) :
    ∀ i (a : s i) j x,
      x ∈ (modeSupport (A.cellChartCompact i (s i) (z^6) a.val) : Set SmallModes.Base) →
      ε/2 ≤ (P i a).Q j (A.tensorPlaneRead i g.inner x) ∧
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x) (w (i,a.val,j) • (P i a).ξ j) ∧
      ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) x)
        (-(w (i,a.val,j) • (P i a).ξ j).2,(w (i,a.val,j) • (P i a).ξ j).1)‖⁻¹ ≤ 8/(ε*b) ∧
      ∃ hn : w (i,a.val,j) • (P i a).ξ j ≠ 0,
        ‖(phaseEquiv (w (i,a.val,j) • (P i a).ξ j) hn).symm.toContinuousLinearMap‖ ≤ 32*W*C/ε := by
  intro i a j x hx
  have hxA := (Set.image_mono (A.cellChartCompact_subset i (s i) (z^6) a.val)) hx
  have hh := hp i a x hxA (A.cellChartCompact_cutoff s i a hx)
  have hd := weighted_selected_denominators _ ((P i a).ξ j) hε hb hC hh.2.1
    (hP i a j) (hw (i,a.val,j)).1 (hw (i,a.val,j)).2 (hh.2.2 j).2.1
  exact ⟨(hh.2.2 j).1,good_smul (by linarith [(hw (i,a.val,j)).1] : w (i,a.val,j) ≠ 0)
    (hh.2.2 j).2.2,hd⟩

lemma selected_grid_pure_geometry {g : SmoothMetric M} {z c b ε : ℝ}
    (hc : 0 < c) (hb : 0 < b)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {s : A.centers → Finset Index} {P : ∀ i, (s i) → PhaseBasis} {G : M → Space}
    (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
    (hξ : ∀ i a j, ξ (i,a.val,j) = (P i a).ξ j)
    (hp : A.SelectedGridPointMargins g z s P G c b ε) :
    ∀ a p, atlasActive (fun i : A.centers => (i : M)) A.weight s (z^6) a p →
      atlasGram G (a.1 : M) p ≠ 0 ∧ atlasSecondTensor G (a.1 : M) p ≠ 0 ∧
      (ε/4)*‖atlasSecondTensor G (a.1 : M) p‖ ≤
        ‖secondQuadratic (atlasSecondTensor G (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖ := by
  intro a p ha
  have hpw := refinedCutoff_tsupport_outer (a.1 : M) (A.weight a.1) (s a.1) (z^6) a.2.1 ha.2
  have hx : coordinateChart (a.1 : M) p ∈
      (modeSupport (A.chartWeightCompact a.1) : Set SmallModes.Base) :=
    ⟨chart (a.1 : M) p,⟨p,hpw,rfl⟩,rfl⟩
  have hcut := normalizedCutoff_tsupport (s a.1) (z^6) a.2.1
    (refinedCutoff_tsupport_inner (a.1 : M)
      (by simpa only [chart_source] using A.weight_support a.1) (s a.1) (z^6) a.2.1 ha.2)
  have hh := hp a.1 ⟨a.2.1,ha.1⟩ _ hx hcut
  rw [A.read_gram_eq_atlas G a.1 (houter a.1) hpw,
    A.read_second_eq_atlas G a.1 (houter a.1) hpw] at hh
  refine ⟨ne_of_gt ((by positivity : 0 < c/4).trans_le hh.1),
    norm_pos_iff.mp ((half_pos hb).trans_le hh.2.1),?_⟩
  rw [hξ a.1 ⟨a.2.1,ha.1⟩ a.2.2]
  exact (hh.2.2 a.2.2).2.1

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
