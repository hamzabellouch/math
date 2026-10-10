import OAI.Geometry.SurfaceImmersion.Geometry.GlobalMetricStep
import OAI.Geometry.SurfaceImmersion.Geometry.GlobalMetricStepBound

namespace OAI

/-! The initial contraction of an approximate immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance initialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance initialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
local instance initialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

lemma inducedTensor_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    inducedTensor (a • F) = a^2 • inducedTensor F := by
  funext p
  ext v w
  have hd : (mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) =
      a • (mfderiv planeModel spaceModel F p : Plane →L[ℝ] Space) :=
    const_smul_mfderiv ((hF p).mdifferentiableAt (by simp)) a
  change inner ℝ ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) v)
    ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) w) =
    a^2*inner ℝ (mfderiv planeModel spaceModel F p v) (mfderiv planeModel spaceModel F p w)
  have hv := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from v)) hd
  have hw := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from w)) hd
  change (mfderiv planeModel spaceModel (a • F) p v : Space) =
    a • (mfderiv planeModel spaceModel F p v : Space) at hv
  change (mfderiv planeModel spaceModel (a • F) p w : Space) =
    a • (mfderiv planeModel spaceModel F p w : Space) at hw
  calc
    _ = inner ℝ (a • (mfderiv planeModel spaceModel F p v : Space))
        (a • (mfderiv planeModel spaceModel F p w : Space)) :=
      congrArg₂ (fun x y : Space => inner ℝ x y) hv hw
    _ = _ := by rw [real_inner_smul_left,real_inner_smul_right]; ring

/-- The normalized defect after the initial scalar contraction has exactly
the reference metric plus a scaled copy of the old metric error. -/
theorem normalizedTensorDefect_initial {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (target : ∀ p : M, CovariantTwoTensor p) {δ : ℝ} (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) :
    normalizedTensorDefect target δ (Real.sqrt (1-δ^2) • F) =
      target+(1-(δ^2)⁻¹) • (inducedTensor F-target) := by
  rw [normalizedTensorDefect,inducedTensor_const_smul hF,Real.sq_sqrt (sub_nonneg.mpr hδ1)]
  funext p
  ext v w
  change (δ^2)⁻¹*(target p v w-(1-δ^2)*inducedTensor F p v w) =
    target p v w+(1-(δ^2)⁻¹)*(inducedTensor F p v w-target p v w)
  field_simp
  ring

lemma initial_contraction_displacement {δ : ℝ} (hδ1 : δ^2 ≤ 1) :
    |Real.sqrt (1-δ^2)-1| ≤ δ^2 := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr hδ1)
  have hn := Real.sqrt_nonneg (1-δ^2)
  have hu : Real.sqrt (1-δ^2) ≤ 1 := by nlinarith [sq_nonneg δ]
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  nlinarith

lemma initial_normalized_coefficient_bound {δ C : ℝ} (hδ : δ ≠ 0)
    (hδ1 : δ^2 ≤ 1) (hC : 0 ≤ C) :
    |1-(δ^2)⁻¹| * (δ^2*C) ≤ C := by
  have hinv : 1 ≤ (δ^2)⁻¹ := (one_le_inv₀ (sq_pos_of_ne_zero hδ)).mpr hδ1
  rw [abs_of_nonpos (sub_nonpos.mpr hinv)]
  have he : -(1-(δ^2)⁻¹)*(δ^2*C) = (1-δ^2)*C := by
    field_simp
    ring
  rw [he]
  nlinarith [sq_nonneg δ]

variable [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas

/-- Finite metric accuracy before contraction becomes the normalized
accuracy required to start the correction iteration. -/
theorem normalized_initial_error_bound (A : SmoothingAtlas M)
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    {target : ∀ p : M, CovariantTwoTensor p}
    (htarget : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    {δ C s : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) (hC : 0 ≤ C)
    (hb : A.TensorWeightedBound s m (δ^2*C) (inducedTensor F-target)) :
    A.TensorWeightedBound s m C
      (normalizedTensorDefect target δ (Real.sqrt (1-δ^2) • F)-target) := by
  have he : normalizedTensorDefect target δ (Real.sqrt (1-δ^2) • F)-target =
      (1-(δ^2)⁻¹) • (inducedTensor F-target) := by
    rw [normalizedTensorDefect_initial hF target hδ hδ1]
    abel
  rw [he]
  have hh := A.tensorWeightedBound_const_smul
    ((A.inducedTensor_smooth hF).sub_section htarget) hb (1-(δ^2)⁻¹)
  intro i
  exact (hh i).mono_const (initial_normalized_coefficient_bound hδ hδ1 hC)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
