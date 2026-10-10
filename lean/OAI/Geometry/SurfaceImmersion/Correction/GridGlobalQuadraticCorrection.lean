import OAI.Geometry.SurfaceImmersion.Correction.CatalogGlobalQuadraticCorrection
import OAI.Geometry.SurfaceImmersion.Atlas.GridRestoredGeometry

namespace OAI

/-! Actual correction for the variable grid with a fixed polynomial budget. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance gridGlobalQuadraticFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridGlobalQuadraticFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridGlobalQuadraticDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridGlobalQuadraticDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridGlobalQuadraticSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridGlobalQuadraticSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

local instance {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _

theorem grid_global_quadratic_correction (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (B α β : ℕ → ℝ → ℝ)
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x)
    (hα : ∀ m, RealModes.HasPolynomialBound (α m))
    (hβ : ∀ m, RealModes.HasPolynomialBound (β m)) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ (h : ℝ) (s₀ : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ a, 1 ≤ w a) →
      (∀ a : A.GridPhaseIndex s₀, w (A.gridPhaseLabel a) • ξ (A.gridPhaseLabel a) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex s₀) ≤ n → ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (_hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ a p, atlasActive (fun i : A.centers => (i : M)) A.weight s₀ h a p →
        atlasGram F (a.1 : M) p ≠ 0 ∧ atlasSecondTensor F (a.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (a.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (a.1 : M) p) (-(ξ a).2,(ξ a).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight s₀ h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ (τ δ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ δ →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      ∀ (Z : A.GridPhaseIndex s₀ → M → Fin 4 → ℂ)
        (_hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a)),
      (∀ a, tsupport (Z a) ⊆ A.gridPhaseSupport h a) →
      (∀ k a m, WeightedEstimates.WeightedBound univ s (m+1)
        (α m x*(δ*τ)) (A.vectorPlaneRead k (Z a))) →
      (∀ k a m v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m
        (β m x) (SmallModes.coordDeriv v (A.vectorPlaneRead k (A.gridRestoredPhase (s := s₀) ξ w a)))) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(d m))))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) +
            A.tensorPlaneRestore (fun k y => (A.planeWeight k y)^2 •
              RealModes.nonzeroPhaseSum τ
                (fun a => A.vectorPlaneRead k (A.gridRestoredPhase (s := s₀) ξ w a))
                (fun a => A.vectorPlaneRead k (Z a)) y))) := by
  classical
  obtain ⟨e,he,hmargin⟩ := A.grid_restored_quadratic_margin houter hε hκ
  let D := max 1 (max D₀ (e*b)⁻¹)
  have hD : 1 ≤ D := le_max_left _ _
  have hD₀ : D₀ ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDB : (e*b)⁻¹ ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨d,E,hE,hcancel⟩ := A.catalog_global_quadratic_correction V he hb hD hDB
    B α β hB hB1 hα hβ q
  refine ⟨d,E,hE,?_⟩
  intro h s₀ ξ w hw hV n hn x hx F hF hlocal hpairs hImm hnormal hgram
    τ δ s hτ hs hτs hs1 hδ hFj Z hZ hSZ hz hp
  have hcat (a : A.GridPhaseIndex s₀) : A.gridRestoredPhase (s := s₀) ξ w a ∈ A.linearPhaseCatalog V :=
    A.restored_linear_phase_mem_catalog V a.1 (hV a)
  have hφ (a : A.GridPhaseIndex s₀) : ContMDiff planeModel 𝓘(ℝ) ∞ (A.gridRestoredPhase (s := s₀) ξ w a) :=
    A.linearPhaseCatalog_smooth V _ (hcat a)
  have hsub (k : A.centers) (l : RealModes.QuadraticLabel (A.GridPhaseIndex s₀)) :
      (modeSupport (A.quadraticOverlapCompact (A.gridPhaseSupport h)
        (fun _ => isClosed_tsupport _) k l) : Set SmallModes.Base) ⊆
        modeSupport (A.chartWeightCompact k) :=
    Set.image_mono (A.quadraticOverlapCompact_subset (A.gridPhaseSupport h)
      (fun _ => isClosed_tsupport _) k l)
  exact hcancel n hn x hx F hF (A.gridRestoredPhase (s := s₀) ξ w) Z hφ hZ
    (A.gridPhaseSupport h) (fun _ => isClosed_tsupport _) hcat hSZ
    (fun k l y hy => hImm k y (hsub k l hy))
    (fun k l y hy => hnormal k y (hsub k l hy))
    (hmargin h s₀ ξ w hw F hF hlocal hpairs)
    (fun k l y hy => (hgram k y (hsub k l hy)).trans hD₀)
    τ δ s hτ hs hτs hs1 hδ hFj hz hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
