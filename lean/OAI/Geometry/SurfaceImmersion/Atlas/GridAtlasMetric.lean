import OAI.Geometry.SurfaceImmersion.Correction.FiniteAtlasFreeMetric
import OAI.Geometry.SurfaceImmersion.Correction.GridMeanReconstruction
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneWeight

namespace OAI

/-! Exact metric expansion for the variable grid of phases in a fixed atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry
open PhaseGrid (Index coverRegion supportedCellCutoff)
local instance gridAtlasFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance gridAtlasFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance gridAtlasDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance gridAtlasDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance gridAtlasSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridAtlasSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

local instance {a : A.centers → Finset Index} : DecidableEq (Σ i, ((a i) × Fin 3)) :=
  Classical.decEq _

/-- The actual grid phases reconstruct the complete tensor in the fixed atlas. -/
theorem grid_atlas_free_metric
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
    inducedTensor (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u) =
      δ^2 • (u + A.tensorPlaneRestore (fun i =>
        chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u))) +
      A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.nonzeroPhaseSum τ
        (fun b : Σ i, ((a i) × Fin 3) => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) b.1 b.2))
        (fun b : Σ i, ((a i) × Fin 3) => A.vectorPlaneRead k
          (A.finiteGlobalAmplitude d hρ δ q u b.1 b.2)) x) := by
  classical
  have hleading (i : A.centers) :
      chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) = A.tensorPlaneEncode u i := by
    have hi := charted_grid_partition_leading (A.supportedPlaneWeight i) hh (hcover i)
      (fun k j => d i (k,j)) hρ (Q i) (w i) (hw i) (hphase i) (hcutoff i)
      (hform i) (hsupport i) (A.tensorPlaneRead_smooth i hu) (hball i)
    rw [hi]
    funext x
    exact (A.tensorPlaneEncode_weight i u x).symm
  have he : (fun i => chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
      chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) =
      A.tensorPlaneEncode u + (fun i => chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) := by
    funext i
    rw [hleading]
    rfl
  rw [A.finite_atlas_free_metric d hρ hδ hτ q u hK,he,
    A.tensorPlaneRestore_add,A.tensorPlaneRestore_encode u hsym]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
