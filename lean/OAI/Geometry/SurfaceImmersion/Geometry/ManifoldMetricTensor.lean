import OAI.Geometry.SurfaceImmersion.Atlas.SupportedAtlasMetric

namespace OAI

/-! The actual metric tensors and cross tensors of manifold displacements.
Cross tensors vanish away from the intersection of the two supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

local instance metricTensorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricTensorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
local instance metricTangentNormed (p : M) : NormedAddCommGroup (TangentSpace planeModel p) :=
  inferInstanceAs (NormedAddCommGroup Plane)
local instance metricTangentSpace (p : M) : NormedSpace ℝ (TangentSpace planeModel p) :=
  inferInstanceAs (NormedSpace ℝ Plane)
local instance metricTensorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricTensorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricTensorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricTensorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

def metricPairTensor (F U : M → Space) (p : M) : CovariantTwoTensor p :=
  (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).bilinearComp
    (E' := TangentSpace planeModel p) (F' := TangentSpace planeModel p)
    (σ₁' := RingHom.id ℝ) (σ₂' := RingHom.id ℝ)
    (σ₁₃' := RingHom.id ℝ) (σ₂₃' := RingHom.id ℝ)
    (surfaceDifferential F p) (surfaceDifferential U p)

def inducedTensor (F : M → Space) (p : M) : CovariantTwoTensor p := metricPairTensor F F p

def linearMetricTensor (F U : M → Space) (p : M) : CovariantTwoTensor p :=
  metricPairTensor F U p + metricPairTensor U F p

lemma metricPairTensor_apply (F U : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    metricPairTensor F U p v w = inner ℝ (surfaceDifferential F p v) (surfaceDifferential U p w) := rfl

lemma inducedTensor_apply (F : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    inducedTensor F p v w = inducedForm F p v w := rfl

lemma linearMetricTensor_apply (F U : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    linearMetricTensor F U p v w = linearMetricForm F U p v w := rfl

lemma inducedTensor_symmetric (F : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    inducedTensor F p v w = inducedTensor F p w v := by
  change inner ℝ (surfaceDifferential F p v) (surfaceDifferential F p w) =
    inner ℝ (surfaceDifferential F p w) (surfaceDifferential F p v)
  exact real_inner_comm _ _

lemma inducedTensor_add {F U : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hU : ContMDiff planeModel spaceModel ∞ U) :
    inducedTensor (F+U) = inducedTensor F + linearMetricTensor F U + inducedTensor U := by
  funext p
  ext v w
  have h := inducedForm_add ((hF p).mdifferentiableAt (by simp))
    ((hU p).mdifferentiableAt (by simp)) v w
  change inducedForm (F+U) p v w = inducedForm F p v w +
    linearMetricForm F U p v w + inducedForm U p v w
  linarith

lemma inducedTensor_finite_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → M → Space) (hf : ∀ i, ContMDiff planeModel spaceModel ∞ (f i)) :
    inducedTensor (∑ i, f i) = (fun p => ∑ i, inducedTensor (f i) p) +
      (fun p => ∑ i, ∑ j ∈ Finset.univ.erase i, metricPairTensor (f i) (f j) p) := by
  funext p
  ext v w
  simpa only [Pi.add_apply,add_apply,sum_apply,inducedTensor_apply,metricPairTensor_apply] using
    inducedForm_finite_sum f (fun i => ((hf i) p).mdifferentiableAt (by simp)) v w

lemma metricPairTensor_zero_off_left (F U : M → Space) {p : M} (hp : p ∉ tsupport F) :
    metricPairTensor F U p = 0 := by
  unfold metricPairTensor
  rw [surfaceDifferential_zero_off_support F hp]
  exact ContinuousLinearMap.bilinearComp_zero_left

lemma metricPairTensor_zero_off_right (F U : M → Space) {p : M} (hp : p ∉ tsupport U) :
    metricPairTensor F U p = 0 := by
  unfold metricPairTensor
  rw [surfaceDifferential_zero_off_support U hp]
  exact ContinuousLinearMap.bilinearComp_zero_right

lemma metricPairTensor_zero_off_intersection (F U : M → Space) {p : M}
    (hp : p ∉ tsupport F ∩ tsupport U) : metricPairTensor F U p = 0 := by
  by_cases hF : p ∈ tsupport F
  · exact metricPairTensor_zero_off_right F U (fun hU => hp ⟨hF,hU⟩)
  · exact metricPairTensor_zero_off_left F U hF

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
