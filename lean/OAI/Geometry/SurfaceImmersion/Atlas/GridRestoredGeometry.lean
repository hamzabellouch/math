import OAI.Geometry.SurfaceImmersion.Atlas.RestoredPhaseGeometry
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPureMargins
import OAI.Geometry.SurfaceImmersion.Correction.GoodSmoothingAtlas
import OAI.Geometry.Immersion.ClosedSurface.GoodAtlas

namespace OAI

/-! Quantitative normal margins for the restored phases selected on a
variable grid in one fixed atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry PhaseGrid JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

abbrev GridPhaseIndex (s : A.centers → Finset Index) := Σ i : A.centers, (s i) × Fin 3

def gridPhaseLabel {s : A.centers → Finset Index} (a : A.GridPhaseIndex s) :
    AtlasCellPhase (ι := A.centers) := (a.1,a.2.1.val,a.2.2)

omit [CompactSpace M] in
lemma gridPhaseLabel_injective (s : A.centers → Finset Index) :
    Function.Injective (A.gridPhaseLabel (s := s)) := by
  rintro ⟨i,a,j⟩ ⟨k,b,l⟩ h
  have hik : i = k := congrArg Prod.fst h
  subst k
  have hab : a = b := Subtype.ext (congrArg (fun x => x.2.1) h)
  have hjl : j = l := congrArg (fun x => x.2.2) h
  subst b
  subst l
  rfl

def gridPhaseSupport (h : ℝ) {s : A.centers → Finset Index} (a : A.GridPhaseIndex s) : Set M :=
  tsupport (refinedCutoff (a.1 : M) (A.weight a.1) (s a.1) h a.2.1.val)

def gridRestoredPhase {s : A.centers → Finset Index}
    (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
    (w : AtlasCellPhase (ι := A.centers) → ℝ) (a : A.GridPhaseIndex s) : M → ℝ :=
  restore (a.1 : M) (A.outer a.1)
    (phaseLinear (w (A.gridPhaseLabel a) • ξ (A.gridPhaseLabel a)) ∘ planeCoordinateIsometry)

theorem grid_restored_quadratic_margin
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ e : ℝ, 0 < e ∧ ∀ (h : ℝ) (s : A.centers → Finset Index)
      (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
      (w : AtlasCellPhase (ι := A.centers) → ℝ), (∀ a, 1 ≤ w a) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      (∀ a p, atlasActive (fun i : A.centers => (i : M)) A.weight s h a p →
        atlasGram G (a.1 : M) p ≠ 0 ∧ atlasSecondTensor G (a.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor G (a.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor G (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s h κ ξ w G →
      ∀ k l y, y ∈ (modeSupport (A.quadraticOverlapCompact
        (A.gridPhaseSupport h (s := s)) (fun _ => isClosed_tsupport _) k l) : Set SmallModes.Base) →
        e*‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k G) y‖ ≤
          ‖secondQuadratic (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k G) y)
            (-(phaseDerivative (coordinatePhase
              (A.globalQuadraticPhase (A.gridRestoredPhase ξ w (s := s)) k l)) y).2,
              (phaseDerivative (coordinatePhase
                (A.globalQuadraticPhase (A.gridRestoredPhase ξ w (s := s)) k l)) y).1)‖ := by
  classical
  have hsource (i : A.centers) : tsupport (A.weight i) ⊆ (chartAt Plane (i : M)).source :=
    by simpa only [chart_source] using A.weight_support i
  obtain ⟨e,he,htransfer⟩ := finite_atlas_pure_margin
    (fun i : A.centers => (i : M)) A.weight hsource
    (fun i => HasCompactSupport.of_compactSpace (A.weight i)) hε
  refine ⟨min e κ,lt_min he hκ,?_⟩
  intro h s ξ w hw G hG hlocal hpairs
  have hlocalw (a : AtlasCellPhase (ι := A.centers)) (p : M)
      (ha : atlasActive (fun i : A.centers => (i : M)) A.weight s h a p) :
      atlasGram G (a.1 : M) p ≠ 0 ∧ atlasSecondTensor G (a.1 : M) p ≠ 0 ∧
      ε*‖atlasSecondTensor G (a.1 : M) p‖ ≤
        ‖secondQuadratic (atlasSecondTensor G (a.1 : M) p)
          (-(w a • ξ a).2,(w a • ξ a).1)‖ := by
    obtain ⟨hg,hb,hm⟩ := hlocal a p ha
    refine ⟨hg,hb,?_⟩
    rw [norm_secondQuadratic_rotated_smul]
    have hw2 : 1 ≤ (w a)^2 := by nlinarith [hw a]
    have hn := norm_nonneg
      (secondQuadratic (atlasSecondTensor G (a.1 : M) p) (-(ξ a).2,(ξ a).1))
    nlinarith
  have hS (a : A.GridPhaseIndex s) : A.gridPhaseSupport h a ⊆ tsupport (A.weight a.1) :=
    refinedCutoff_tsupport_outer (a.1 : M) (A.weight a.1) (s a.1) h a.2.1.val
  have hactive (a : A.GridPhaseIndex s) (p : M) (ha : p ∈ A.gridPhaseSupport h a) :
      atlasActive (fun i : A.centers => (i : M)) A.weight s h (A.gridPhaseLabel a) p :=
    ⟨a.2.1.property,ha⟩
  have hB (k : A.centers) (p : M) (hp : p ∈ tsupport (A.weight k)) :
      realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k G) (coordinateChart (k : M) p) =
        atlasSecondTensor G (k : M) p :=
    (realSecondTensor_eventuallyEq
      (A.vectorPlaneRead_eventually_coordinateMap G k (houter k) hp)).eq_of_nhds
  apply A.restored_quadratic_margin (fun a : A.GridPhaseIndex s => a.1)
    (fun a => w (A.gridPhaseLabel a) • ξ (A.gridPhaseLabel a))
    (A.gridPhaseSupport h) (fun _ => isClosed_tsupport _) hS houter G
  · intro a k p ha hp
    rw [hB k p hp]
    exact (mul_le_mul_of_nonneg_right (min_le_left e κ) (norm_nonneg _)).trans
      (htransfer h s (fun a => w a • ξ a) G hG hlocalw (A.gridPhaseLabel a) k p
        (hactive a p ha) hp)
  · intro a b k p hab ha hb hp
    have has := hsource a.1 (hS a ha)
    have hbs := hsource b.1 (hS b hb)
    have hks := hsource k hp
    have has' : p ∈ (coordinateChart (a.1 : M)).source := by
      simpa only [coordinateChart_source] using has
    have hbs' : p ∈ (coordinateChart (b.1 : M)).source := by
      simpa only [coordinateChart_source] using hbs
    have hks' : p ∈ (coordinateChart (k : M)).source := by
      simpa only [coordinateChart_source] using hks
    dsimp only
    rw [hB k p hp,
      atlasPhaseCovector_smul (a.1 : M) (k : M) _ _ hks' has',
      atlasPhaseCovector_smul (b.1 : M) (k : M) _ _ hks' hbs']
    have hh := hpairs (A.gridPhaseLabel a) (A.gridPhaseLabel b) k p
      (fun heq => hab (A.gridPhaseLabel_injective s heq)) (hactive a p ha) (hactive b p hb) hp
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right e κ) (norm_nonneg _)).trans hh.1,
      (mul_le_mul_of_nonneg_right (min_le_right e κ) (norm_nonneg _)).trans hh.2.1⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
