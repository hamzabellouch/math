import OAI.Geometry.SurfaceImmersion.Correction.GridGlobalQuadraticCorrection
import OAI.Geometry.SurfaceImmersion.Correction.GridFreeSupport
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAtlasSeedProfile
import OAI.Geometry.SurfaceImmersion.Atlas.CatalogPhaseBounds
import OAI.Geometry.SurfaceImmersion.Atlas.FiniteAtlasIncrement

namespace OAI

/-! Quadratic correction for the actual free grid amplitudes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance gridFreeCorrectionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridFreeCorrectionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridFreeCorrectionDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridFreeCorrectionDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridFreeCorrectionSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridFreeCorrectionSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

open PhaseGeometry PhaseGrid

local instance {s : A.centers → Finset Index} : DecidableEq (A.GridPhaseIndex s) := Classical.decEq _


theorem grid_free_quadratic_correction (V : Finset SmallModes.Base)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    {ε κ b D₀ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hb : 0 < b)
    (FJ C J N B : ℕ → ℝ → ℝ)
    (hFJ : ∀ m, RealModes.HasPolynomialBound (FJ m))
    (hFJ1 : ∀ m x, 1 ≤ x → 1 ≤ FJ m x)
    (hC : ∀ m, RealModes.HasPolynomialBound (C m))
    (hJ : ∀ m, RealModes.HasPolynomialBound (J m))
    (hN : ∀ m, RealModes.HasPolynomialBound (N m))
    (hB : ∀ m, RealModes.HasPolynomialBound (B m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x)
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ (e : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ (h : ℝ) (a : A.centers → Finset Index)
        (ξ : AtlasCellPhase (ι := A.centers) → SmallModes.Base)
        (w : AtlasCellPhase (ι := A.centers) → ℝ),
      (∀ l, 1 ≤ w l) →
      (∀ l : A.GridPhaseIndex a, w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V) →
      ∀ n : ℕ, Fintype.card (A.GridPhaseIndex a) ≤ n → ∀ x : ℝ, 1 ≤ x →
      ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F),
      (∀ l p, atlasActive (fun i : A.centers => (i : M)) A.weight a h l p →
        atlasGram F (l.1 : M) p ≠ 0 ∧ atlasSecondTensor F (l.1 : M) p ≠ 0 ∧
        ε*‖atlasSecondTensor F (l.1 : M) p‖ ≤
          ‖secondQuadratic (atlasSecondTensor F (l.1 : M) p) (-(ξ l).2,(ξ l).1)‖) →
      AtlasPairMargins (fun i : A.centers => (i : M)) A.weight a h κ ξ w F →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) y)) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        b ≤ ‖RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) y‖) →
      (∀ k y, y ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) →
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (spaceCoordinates ∘ A.vectorPlaneRead k F) y)
          (SmallModes.coordDeriv SmallModes.dy (spaceCoordinates ∘ A.vectorPlaneRead k F) y))⁻¹‖ ≤ D₀) →
      ∀ {φ : ∀ i, ((a i) × Fin 3) → JetPolynomial.Base → ℝ}
        {τ : ℝ} {s : ℝ≥0}
        {c : ∀ i j, PolynomialSolveData emptyMetricPolynomial 0
          (A.jetChartMap i F) (A.jetChartMap_smooth i hF) (φ i j)
          (A.cellChartCompact i (a i) h j.1.val) τ s}
        {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
        (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)),
      (∀ i j, φ i j = phaseLinear (w (i,j.1.val,j.2) • ξ (i,j.1.val,j.2)) ∘
        planeCoordinateIsometry) →
      (∀ i j, (c i j).C = (fun m => C m x) ∧ (c i j).J = (fun m => J m x) ∧
        ∀ m, (c i j).D m = 0) →
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, ρ⁻¹ ≤ B m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.forms m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ N m x) →
      (∀ k m j, j ≤ m+3 → WeightedEstimates.WeightedBound univ 1 j
        (FJ m x/(s : ℝ)^(j-2)) (spaceCoordinates ∘ A.vectorPlaneRead k F)) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ u : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (u y)) →
      (∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u)) →
      (∀ i m, WeightedEstimates.WeightedBound univ s m (B m x) (A.tensorPlaneRead i u)) →
      ∃ W : M → RealModes.RVec 4, ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ W ∧
        (∀ m, A.WeightedBound τ m (δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(e m))) W) ∧
        (∀ m, A.TensorWeightedBound τ m
          ((τ/s)^(q+1)*(δ^2*((n : ℝ)+2*(n : ℝ)^2)*(E m*x^(e m))))
          (linearMetricTensor F (spaceCoordinates.symm ∘ W) + A.finiteAtlasNonzero d hρ δ q u)) := by
  obtain ⟨α,hα,hamp⟩ := A.polynomial_atlas_seed_profile q C J N B hC hJ hN hB hC1 hB1
  obtain ⟨P,hP,hphase⟩ := A.linearPhaseCatalog_derivative_bounds V
  obtain ⟨e,E,hE,hquad⟩ := A.grid_global_quadratic_correction V houter hε hκ hb
    FJ α (fun m _ => P m) hFJ hFJ1 hα (fun m => RealModes.polynomialBound_const
      (zero_le_one.trans (hP m))) q
  refine ⟨e,E,hE,?_⟩
  intro h a ξ w hw hV n hn x hx F hF hlocal hpairs hImm hnormal hgram
    φ τ s c r ρ R reference d hφ hc hρ hτ hs hτs hs1 hρB hbud hFjets δ hδ u hu hball hbu
  let Z := fun l : A.GridPhaseIndex a => A.finiteGlobalAmplitude d hρ δ q u l.1 l.2
  have hZ (l : A.GridPhaseIndex a) : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z l) :=
    restore_smooth (l.1 : M) (A.outer_smooth l.1) (A.outer_support l.1)
      ((d l.1 l.2).freeAmplitude hρ δ q (A.tensorPlaneRead l.1 u)).contDiff
  have hSZ (l : A.GridPhaseIndex a) : tsupport (Z l) ⊆ A.gridPhaseSupport h l :=
    A.finiteGlobalAmplitude_grid_support d hρ δ q u l.1 l.2
  have hbound := hamp x hx F hF d hc hρ hτ hs hτs hs1 hρB hbud δ hδ u hu hball hbu
  have hder (k : A.centers) (l : A.GridPhaseIndex a) (m : ℕ) (v : SmallModes.Base) (hv : ‖v‖ ≤ 1) :=
    hphase (A.gridRestoredPhase (s := a) ξ w l)
      (A.restored_linear_phase_mem_catalog V l.1 (hV l)) k s hs hs1 m v hv
  obtain ⟨W,hW,hsize,hres⟩ := hquad h a ξ w hw hV n hn x hx F hF
    hlocal hpairs hImm hnormal hgram τ δ s hτ hs hτs hs1 hδ hFjets Z hZ hSZ
    (fun k l m => hbound k l.1 l.2 m) hder
  have hphases : A.gridRestoredPhase (s := a) ξ w =
      (fun l : A.GridPhaseIndex a => A.finiteGlobalPhase (ι := fun i => (a i) × Fin 3) (φ := φ) l.1 l.2) := by
    funext l
    exact (A.finiteGlobalPhase_eq_gridRestoredPhase φ ξ w hφ l.1 l.2).symm
  refine ⟨W,hW,hsize,?_⟩
  intro m
  simpa only [hphases,finiteAtlasNonzero,Z] using hres m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
