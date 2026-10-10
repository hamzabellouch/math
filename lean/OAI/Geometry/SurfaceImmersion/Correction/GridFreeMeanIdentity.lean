import OAI.Geometry.SurfaceImmersion.Atlas.FiniteAtlasIncrement
import OAI.Geometry.SurfaceImmersion.Atlas.GridAtlasMetric
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAdjustedMean
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneWeight
import OAI.Geometry.SurfaceImmersion.Correction.TensorAtlasMean
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAtlasQuadraticResidual

namespace OAI

/-! Exact metric expansion for the variable grid of phases in a fixed atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry
open PhaseGrid (Index coverRegion supportedCellCutoff)
local instance gridFreeMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridFreeMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridFreeMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridFreeMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridFreeMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridFreeMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

local instance {a : A.centers → Finset Index} : DecidableEq (Σ i, ((a i) × Fin 3)) :=
  Classical.decEq _

theorem grid_free_mean_identity
    {a : A.centers → Finset Index} {h : ℝ} (hh : 0 < h)
    (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
      coverRegion (a i) h)
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ((a i) × Fin 3) → Base → ℝ}
    {K : ∀ i, ((a i) × Fin 3) → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ)
    (hw : ∀ i k j, w i k j ≠ 0)
    (hphase : ∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w i k j • (Q i k).ξ j))
    (hcutoff : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).cutoff ((c i (k,j)).e x) =
        supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val x / w i k j)
    (hform : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).form ((c i (k,j)).e x) = (Q i k).Q j)
    (hsupport : ∀ i k j, tsupport (supportedCellCutoff
      (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆ (c i (k,j)).e.source)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ p v v', u p v v' = u p v' v)
    (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) :
    A.finiteAtlasFreeMean d hρ δ q u =
      δ^2 • (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u) := by
  have hg := A.grid_atlas_free_metric hh hcover d hρ Q w hw hphase hcutoff hform
    hsupport hK u hu hsym hball hδ hτ q
  have hs := A.finite_atlas_metric_split d hρ hδ hτ q u hK
  change inducedTensor (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u) =
    δ^2 • (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u) +
      A.finiteAtlasNonzero d hρ δ q u at hg
  exact add_right_cancel (hs.symm.trans hg)

theorem grid_free_mean_residual
    {a : A.centers → Finset Index} {h : ℝ} (hh : 0 < h)
    (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
      coverRegion (a i) h)
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ((a i) × Fin 3) → Base → ℝ}
    {K : ∀ i, ((a i) × Fin 3) → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ)
    (hw : ∀ i k j, w i k j ≠ 0)
    (hphase : ∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w i k j • (Q i k).ξ j))
    (hcutoff : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).cutoff ((c i (k,j)).e x) =
        supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val x / w i k j)
    (hform : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).form ((c i (k,j)).e x) = (Q i k).Q j)
    (hsupport : ∀ i k j, tsupport (supportedCellCutoff
      (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆ (c i (k,j)).e.source)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ p v v', u p v v' = u p v' v)
    (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (f : ∀ x : M, CovariantTwoTensor x)
    (hf : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (f x)))
    {m : ℕ} {C : ℝ} (hτpos : 0 < τ) (hτs : τ ≤ s)
    (hres : A.TensorWeightedBound s m C
      (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f)) :

    A.TensorWeightedBound τ m (δ^2*C) (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • f) := by
  have hmean := A.grid_free_mean_identity hh hcover d hρ Q w hw hphase hcutoff hform
    hsupport hK u hu hsym hball hδ hτ q
  have hμ := A.tensorPlaneRestore_smooth
    (fun i => chartedFamilyMean_smooth (d i) hρ δ q (A.tensorPlaneRead i u))
  have hr := (hu.add_section hμ).sub_section hf
  have hb : A.TensorWeightedBound τ m C
      (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f) :=
    fun i => (hres i).shrink_scale hτpos.le hτs
  have hh := A.tensorWeightedBound_const_smul hr hb (δ^2)
  rw [abs_of_nonneg (sq_nonneg δ)] at hh
  rw [hmean,← smul_sub]
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
