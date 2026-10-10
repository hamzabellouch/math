import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricBounds

namespace OAI

/-! Exact normalized-defect identity for the unsmoothed global map update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance metricStepFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricStepFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
local instance metricStepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricStepDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricStepSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricStepSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

lemma linearMetricTensor_sub_left {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G)
    (U : M → Space) : linearMetricTensor (F-G) U = linearMetricTensor F U - linearMetricTensor G U := by
  funext p
  ext v w
  change linearMetricForm (F-G) U p v w = linearMetricForm F U p v w - linearMetricForm G U p v w
  have hd : surfaceDifferential (F-G) p = surfaceDifferential F p - surfaceDifferential G p :=
    mfderiv_sub ((hF p).mdifferentiableAt (by simp)) ((hG p).mdifferentiableAt (by simp))
  simp only [linearMetricForm,hd,sub_apply,inner_sub_left,inner_sub_right]
  ring

lemma metric_increment_difference {F G U : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G)
    (hU : ContMDiff planeModel spaceModel ∞ U) :
    (inducedTensor (F+U)-inducedTensor F) - (inducedTensor (G+U)-inducedTensor G) =
      linearMetricTensor (F-G) U := by
  rw [inducedTensor_add hF hU,inducedTensor_add hG hU,linearMetricTensor_sub_left hF hG]
  abel

def normalizedTensorDefect (target : ∀ p : M, CovariantTwoTensor p) (δ : ℝ) (F : M → Space) :
    ∀ p : M, CovariantTwoTensor p := (δ^2)⁻¹ • (target - inducedTensor F)

def realizedTensorError (target Hs : ∀ p : M, CovariantTwoTensor p)
    (δ δ' : ℝ) (G U : M → Space) : ∀ p : M, CovariantTwoTensor p :=
  inducedTensor (G+U)-inducedTensor G-(δ^2 • Hs-δ'^2 • target)

lemma square_smul_normalizedTensorDefect (target : ∀ p : M, CovariantTwoTensor p)
    {δ : ℝ} (hδ : δ ≠ 0) (F : M → Space) :
    δ^2 • normalizedTensorDefect target δ F = target - inducedTensor F := by
  rw [normalizedTensorDefect,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 hδ),one_smul]

/-- The smoothing tail enters only through the mixed term with the increment. -/
theorem global_normalized_defect_identity
    (target Hs : ∀ p : M, CovariantTwoTensor p) {δ δ' : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    {F G U : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U) :
    δ'^2 • (normalizedTensorDefect target δ' (F+U)-target) =
      δ^2 • (normalizedTensorDefect target δ F-Hs) - realizedTensorError target Hs δ δ' G U -
        linearMetricTensor (F-G) U := by
  rw [smul_sub,smul_sub,square_smul_normalizedTensorDefect target hδ',
    square_smul_normalizedTensorDefect target hδ]
  rw [← metric_increment_difference hF hG hU]
  unfold realizedTensorError
  abel

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
