import OAI.Geometry.SurfaceImmersion.Atlas.TensorChartRead
import OAI.Geometry.SurfaceImmersion.Geometry.LocalIsometryBounds

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

local instance planeReadFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance planeReadFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance planeReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance planeReadDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance planeReadSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance planeReadSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def tensorPlaneRead (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x) : SmallModes.Base → Tensor :=
  A.tensorChartRead i u ∘ planeCoordinateIsometry.symm

def tensorPlaneRestore (f : A.centers → SmallModes.Base → Tensor) : ∀ x : M, CovariantTwoTensor x :=
  fun p => ∑ i : A.centers, A.bundleRestore A.tensorTriv i
    (fun y => fiberFromThree (f i (planeCoordinateIsometry y))) p

lemma tensorPlaneRead_sub (i : A.centers) (u v : ∀ x : M, CovariantTwoTensor x) :
    A.tensorPlaneRead i (u - v) = A.tensorPlaneRead i u - A.tensorPlaneRead i v := by
  funext x
  change fiberToThree (localize (i : M) (A.outer i) (A.bundleComponent A.tensorTriv i (u-v))
    (planeCoordinateIsometry.symm x)) = _
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [tensorPlaneRead, tensorChartRead, Function.comp_apply, bundleCutoff, localize,
      indicator_of_mem hx, bundleComponent, Pi.sub_apply, map_sub, smul_sub]
  · simp only [tensorPlaneRead, tensorChartRead, Function.comp_apply, bundleCutoff, localize,
      indicator_of_notMem hx, map_zero, Pi.sub_apply, sub_self]

lemma tensorPlaneRestore_sub (f g : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (f-g) = A.tensorPlaneRestore f - A.tensorPlaneRestore g := by
  funext p
  simp only [tensorPlaneRestore, Pi.sub_apply, map_sub, bundleRestore, smul_sub,
    Finset.sum_sub_distrib]

lemma tensorPlaneRestore_smooth {f : A.centers → SmallModes.Base → Tensor}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.tensorPlaneRestore f p)) := by
  apply ContMDiff.sum_section
  intro i _
  exact A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i
    (fiberFromThree.contDiff.comp ((hf i).comp planeCoordinateIsometry.contDiff))

lemma tensorPlaneRestore_symmetric (f : A.centers → SmallModes.Base → Tensor) :
    ∀ p v w, A.tensorPlaneRestore f p v w = A.tensorPlaneRestore f p w v := by
  apply A.tensorDecode_symmetric
  intro x i v w
  exact fiberFromThree_symmetric _ _ _

variable [CompactSpace M]

lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

lemma tensorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ x : M, CovariantTwoTensor x) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (u x)) → A.TensorWeightedBound s m C u →
      WeightedBound univ s m (D * C) (A.tensorPlaneRead i u) := by
  obtain ⟨D,hD,hd⟩ := A.tensorChartRead_bound i m
  refine ⟨D,hD,?_⟩
  intro u s C hs hs1 hC hu hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm (A.tensorChartRead_smooth i hu)
    (hd u s C hs hs1 hC hu hb)

lemma tensorPlaneRestore_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.bundle_restoration_bound A.tensorTriv A.tensorTriv_domain m
  refine ⟨D * ‖fiberFromThree‖, mul_nonneg hD (norm_nonneg _), ?_⟩
  intro f s C hs hs1 hC hf hb
  have hh := hd (fun i y => fiberFromThree (f i (planeCoordinateIsometry y))) s
    (‖fiberFromThree‖ * C) hs hs1 (mul_nonneg (norm_nonneg _) hC)
    (fun i => fiberFromThree.contDiff.comp ((hf i).comp planeCoordinateIsometry.contDiff))
    (fun i => (weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i)).linear
      uniqueDiffOn_univ hs.le ((hf i).comp planeCoordinateIsometry.contDiff).contDiffOn fiberFromThree)
  have hout : A.TensorWeightedBound s m (D * (‖fiberFromThree‖ * C))
      (A.tensorPlaneRestore f) := hh
  convert hout using 1
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
