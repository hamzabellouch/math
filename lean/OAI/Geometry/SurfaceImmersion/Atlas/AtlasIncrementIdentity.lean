import OAI.Geometry.SurfaceImmersion.Correction.AtlasFreeMetricSplit

namespace OAI

/-! Exact global metric error after the free and forced displacements. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean JetPolynomial.Perturbation

local instance incrementMetricFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance incrementMetricFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance incrementMetricDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance incrementMetricDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance incrementMetricSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance incrementMetricSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}
  {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
  {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
  {reference : A.centers → SmallModes.Base → Tensor}

theorem atlas_free_forced_increment
    (d : ∀ i, ChartedMeanFamilyData (P i) 0 τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {F V : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hV : ContMDiff planeModel spaceModel ∞ V) (H : ∀ x : M, CovariantTwoTensor x) :
    let U := spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u
    inducedTensor (F+(U+V)) - inducedTensor F - δ^2 • H =
      linearMetricTensor F U +
        (linearMetricTensor F V + A.atlasFreeQuadraticOscillation d hρ δ q u) +
        (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) +
        linearMetricTensor U V + inducedTensor V := by
  let U := spaceCoordinates.symm ∘ A.atlasFreeOscillation d hρ δ q u
  have hU : ContMDiff planeModel spaceModel ∞ U :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (A.atlasFreeOscillation_smooth d hρ δ q u)
  have hm := A.atlas_free_metric_split d hρ δ q u hK
  dsimp only
  funext p
  ext v w
  have hmean := congrArg (fun t : ∀ x : M, CovariantTwoTensor x => t p v w) hm
  have he := inducedForm_free_forced ((hF p).mdifferentiableAt (by simp))
    ((hU p).mdifferentiableAt (by simp)) ((hV p).mdifferentiableAt (by simp)) v w (δ^2 * H p v w)
  change inducedForm U p v w =
    A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) p v w +
      A.atlasFreeQuadraticOscillation d hρ δ q u p v w at hmean
  change inducedForm (F+(U+V)) p v w - inducedForm F p v w - δ^2 * H p v w =
    linearMetricForm F U p v w +
      (linearMetricForm F V p v w + A.atlasFreeQuadraticOscillation d hρ δ q u p v w) +
      (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) p v w - δ^2 * H p v w) +
      linearMetricForm U V p v w + inducedForm V p v w
  linarith only [he,hmean]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
