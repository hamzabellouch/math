import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothing
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingLinearMaps

namespace OAI

/-! Tensor coordinate maps commute with transposition. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

local instance symmetryModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance symmetryModelSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance symmetryModelComplete : CompleteSpace TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance symmetryDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance symmetryDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

/-- Transpose a covariant tensor by interchanging its two arguments. -/
def tensorTranspose {p : M} (u : CovariantTwoTensor p) : CovariantTwoTensor p :=
  (show TensorFiber from u).flip

omit [IsManifold planeModel ∞ M] in
@[simp] lemma tensorTranspose_apply {p : M} (u : CovariantTwoTensor p)
    (v w : TangentSpace planeModel p) : tensorTranspose u v w = u w v := rfl

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorComponent_flip (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    A.bundleComponent A.tensorTriv i (fun p => tensorTranspose (u p)) p =
      (A.bundleComponent A.tensorTriv i u p).flip := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  have hs : p ∈ (trivializationAt ℝ (fun _ : M => ℝ) (i : M)).baseSet := mem_univ p
  unfold bundleComponent
  rw [(A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp),
    (A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp)]
  unfold tensorTriv
  simp only [hom_trivializationAt_apply]
  ext v w
  simp only [ContinuousLinearMap.flip_apply]
  rw [inCoordinates_apply_eq₂ ht ht hs, inCoordinates_apply_eq₂ ht ht hs]
  rfl

lemma tensorLocalize_flip (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p) :
    A.bundleLocalize A.tensorTriv i (fun p => tensorTranspose (u p)) =
      fun x => (A.bundleLocalize A.tensorTriv i u x).flip := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · unfold bundleLocalize localize
    rw [indicator_of_mem hx, indicator_of_mem hx,
      A.tensorComponent_flip i u ((chart (i : M)).map_target hx)]
    ext v w
    rfl
  · simp only [bundleLocalize, localize, indicator_of_notMem hx]
    rfl

lemma tensorRestore_flip (i : A.centers) (h : Base → TensorFiber) :
    A.bundleRestore A.tensorTriv i (fun x => (h x).flip) =
      fun p => tensorTranspose (A.bundleRestore A.tensorTriv i h p) := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · have hd := A.tensorTriv_domain i hp
    have hinj : Function.Injective ((A.tensorTriv i).continuousLinearMapAt ℝ p) := by
      intro v w heq
      have heq' := congrArg ((A.tensorTriv i).symmL ℝ p) heq
      simpa only [(A.tensorTriv i).symmL_continuousLinearMapAt hd] using heq'
    apply hinj
    have hflip := A.tensorComponent_flip i (A.bundleRestore A.tensorTriv i h) hp
    change (A.tensorTriv i).continuousLinearMapAt ℝ p
        (tensorTranspose (A.bundleRestore A.tensorTriv i h p)) =
      ((A.tensorTriv i).continuousLinearMapAt ℝ p (A.bundleRestore A.tensorTriv i h p)).flip at hflip
    have hcoord (f : Base → TensorFiber) :
        (A.tensorTriv i).continuousLinearMapAt ℝ p (A.bundleRestore A.tensorTriv i f p) =
          A.outer i p • f (chart (i : M) p) := by
      change (A.tensorTriv i).continuousLinearMapAt ℝ p
        (A.outer i p • (A.tensorTriv i).symmL ℝ p (f (chart (i : M) p))) = _
      rw [(A.tensorTriv i).continuousLinearMapAt ℝ p |>.map_smul]
      rw [(A.tensorTriv i).continuousLinearMapAt_symmL hd]
    rw [hflip, hcoord, hcoord]
    ext v w
    rfl
  · have ho : A.outer i p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hp (A.outer_support i hh))
    simp only [bundleRestore, ho, zero_smul]
    rfl

variable [CompactSpace M]

/-- The actual tensor smoother preserves transposition, so it acts on
symmetric tensors without any extra projection. -/
theorem tensorSmooth_flip (r : ℕ) {s : ℝ} (hs : 0 < s)
    {u : ∀ p : M, CovariantTwoTensor p}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    A.tensorSmooth r s (fun p => tensorTranspose (u p)) =
      fun p => tensorTranspose (A.tensorSmooth r s u p) := by
  have hflip (i : A.centers) :
      finiteSmooth r s (fun x => (A.bundleLocalize A.tensorTriv i u x).flip) =
        fun x => (finiteSmooth r s (A.bundleLocalize A.tensorTriv i u) x).flip :=
    finiteSmooth_clm r hs
      (ContinuousLinearMap.flipₗᵢ ℝ Plane Plane ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu)
  funext p
  simp only [tensorSmooth, bundleSmooth, A.tensorLocalize_flip, hflip]
  calc
    _ = ∑ i : A.centers, tensorTranspose
        (A.bundleRestore A.tensorTriv i (finiteSmooth r s (A.bundleLocalize A.tensorTriv i u)) p) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun (A.tensorRestore_flip i _) p
    _ = _ := by
      ext v w
      simp only [tensorTranspose_apply, sum_apply]

theorem tensorSmooth_symmetric (r : ℕ) {s : ℝ} (hs : 0 < s)
    {u : ∀ p : M, CovariantTwoTensor p}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hsymm : ∀ p v w, u p v w = u p w v) :
    ∀ p v w, A.tensorSmooth r s u p v w = A.tensorSmooth r s u p w v := by
  have heq : (fun p => tensorTranspose (u p)) = u := by
    funext p
    ext v w
    exact (hsymm p v w).symm
  have h := A.tensorSmooth_flip r hs hu
  rw [heq] at h
  intro p v w
  exact congrArg (fun b : CovariantTwoTensor p => b v w) (congrFun h p)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
