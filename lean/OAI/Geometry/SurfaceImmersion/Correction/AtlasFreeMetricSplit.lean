import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricExpansion
import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeMetricSplit
import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeOscillation
import OAI.Geometry.SurfaceImmersion.Geometry.TensorPlaneReconstruction

namespace OAI

/-! The actual global free oscillation has the restored quadratic mean
plus its local oscillations and all cross-chart oscillations. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean JetPolynomial.Perturbation

local instance freeMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance freeMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance freeMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance freeMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance freeMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance freeMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}
  {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
  {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
  {reference : A.centers → SmallModes.Base → Tensor}

def atlasFreeQuadraticOscillation
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x) :
    ∀ x : M, CovariantTwoTensor x :=
  A.tensorPlaneRestore (fun i => (d i).quadraticOscillation hρ δ q (A.tensorPlaneRead i u)) +
    A.atlasMetricCross (fun i => spaceCoordinates.symm ∘
      chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u))

theorem atlas_free_metric_split
    (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u) =
      A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) +
        A.atlasFreeQuadraticOscillation d hρ δ q u := by
  have hsp (i : A.centers) :
      tsupport (chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u)) ⊆
        (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp
      ((chartedFreeSum_smooth_support (d i).data hρ δ q (A.tensorPlaneRead i u)).2 hx)
    exact hK i j hj
  rw [atlasFreeOscillation, A.euclidean_vectorPlaneRestore_metric _
    (fun i => (chartedFreeSum_smooth_support (d i).data hρ δ q (A.tensorPlaneRead i u)).1) hsp]
  have he : (fun i => RealModes.realMetricTensor
      (chartedFreeSum (d i).data hρ δ q (A.tensorPlaneRead i u))) =
      (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) +
        (fun i => (d i).quadraticOscillation hρ δ q (A.tensorPlaneRead i u)) := by
    funext i
    exact (d i).free_metric_split hρ δ q (A.tensorPlaneRead i u)
  rw [he,A.tensorPlaneRestore_add]
  change (_ + _) + _ = _ + (_ + _)
  exact add_assoc _ _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
