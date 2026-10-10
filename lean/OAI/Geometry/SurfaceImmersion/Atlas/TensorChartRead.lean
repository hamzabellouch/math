import OAI.Geometry.SurfaceImmersion.Atlas.BundleCutoffCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.TensorPhaseDecomposition

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

local instance chartReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance chartReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance chartReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance chartReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance chartReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def tensorChartRead (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x) : Base → Tensor :=
  fiberToThree ∘ A.bundleCutoff A.tensorTriv i (A.outer i) u

lemma tensorChartRead_on_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorChartRead i u (chart (i : M) p) = fiberToThree (A.bundleComponent A.tensorTriv i u p) := by
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp]
  simp only [one_pow, one_smul]

lemma tensorEncode_read (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    fiberToThree (A.tensorEncode u (chart (i : M) p) i) =
      (A.weight i p)^2 • A.tensorChartRead i u (chart (i : M) p) := by
  change fiberToThree (localize (i : M) (A.weight i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ hp, map_smul]
  by_cases hz : A.weight i p = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_smul]
  · rw [A.tensorChartRead_on_weight i u (subset_tsupport _ hz)]

variable [CompactSpace M]

lemma tensorChartRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x))) :
    ContDiff ℝ ∞ (A.tensorChartRead i u) :=
  fiberToThree.contDiff.comp (A.bundleCutoff_smooth A.tensorTriv A.tensorTriv_domain i
    (A.outer_smooth i) (A.outer_support i) hu)

lemma tensorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ x : M, CovariantTwoTensor x) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) → A.TensorWeightedBound s m C u →
      WeightedBound univ s m (D * C) (A.tensorChartRead i u) := by
  obtain ⟨D,hD,hd⟩ := A.bundleCutoff_bound A.tensorTriv A.tensorTriv_domain i
    (A.outer_smooth i) (A.outer_support i) m
  refine ⟨‖fiberToThree‖ * D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro u s C hs hs1 hC hu hbu
  have hh := (hd u s C hs hs1 hC hu hbu).linear uniqueDiffOn_univ hs.le
    (A.bundleCutoff_smooth A.tensorTriv A.tensorTriv_domain i
      (A.outer_smooth i) (A.outer_support i) hu).contDiffOn fiberToThree
  simpa only [tensorChartRead, mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
