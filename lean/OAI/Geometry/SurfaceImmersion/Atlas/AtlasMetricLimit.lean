import OAI.Geometry.SurfaceImmersion.Correction.AtlasCorrectionLimit
import OAI.Geometry.SurfaceImmersion.Geometry.GlobalMetricStep
import OAI.Geometry.SurfaceImmersion.Correction.TensorMeanCoordinates

namespace OAI

/-! The normalized atlas defect controls the actual metric of the limit. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection

local instance metricLimitFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricLimitFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance metricLimitDualAdd :
    ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricLimitDualSmul :
    ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricLimitSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricLimitSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- The genuine finite atlas reconstruction carries coordinate convergence
to convergence in each tensor fiber. -/
lemma tensor_tendsto_zero_of_encode
    {H : ℕ → ∀ p : M, CovariantTwoTensor p}
    (hH : ∀ i x, Tendsto (fun n => A.tensorEncode (H n) x i) atTop (𝓝 0))
    (p : M) : Tendsto (fun n => H n p) atTop (𝓝 0) := by
  have hi (i : A.centers) : Tendsto
      (fun n => A.bundleRestore A.tensorTriv i
        (A.bundleLocalize A.tensorTriv i (H n)) p) atTop (𝓝 0) := by
    have h := ((A.tensorTriv i).symmL ℝ p).continuous.tendsto 0 |>.comp
      (hH i (chart (i : M) p))
    simpa only [Function.comp_apply, bundleRestore, tensorEncode, map_zero, smul_zero] using
      h.const_smul (A.outer i p)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [A.bundle_sum_restore_localize A.tensorTriv A.tensorTriv_domain,
    Finset.sum_const_zero] using hs

omit [CompactSpace M] in
/-- A bounded normalized defect and a vanishing amplitude imply convergence
of the actual pullback metrics. No convergence of normalized defects is needed. -/
theorem metric_tendsto_of_normalized_coordinates_bound
    {G : ℕ → M → Space} {δ : ℕ → ℝ} {B : ℝ}
    (target : ∀ p : M, CovariantTwoTensor p)
    (hδ : ∀ n, δ n ≠ 0) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ n i x,
      ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i-
        A.tensorEncode target x i‖ ≤ B)
    (p : M) (v w : TangentSpace planeModel p) :
    Tendsto (fun n => inner ℝ (mfderiv planeModel spaceModel (G n) p v)
      (mfderiv planeModel spaceModel (G n) p w)) atTop (𝓝 (target p v w)) := by
  have hlocal (i : A.centers) (x : JetPolynomial.Base) : Tendsto
      (fun n => A.tensorEncode (target-inducedTensor (G n)) x i) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => show ‖A.tensorEncode (target-inducedTensor (G n)) x i‖ ≤
        (δ n)^2*(B+‖A.tensorEncode target x i‖) from ?_)
      (by simpa only [zero_pow (by decide : 2 ≠ 0),zero_mul] using
        (hδ0.pow 2).mul_const (B+‖A.tensorEncode target x i‖))
    have hb := hbound n i x
    have hn : ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i‖ ≤
        B+‖A.tensorEncode target x i‖ := by
      calc
        _ = ‖(A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i-
          A.tensorEncode target x i)+A.tensorEncode target x i‖ := by rw [sub_add_cancel]
        _ ≤ ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i-
          A.tensorEncode target x i‖+‖A.tensorEncode target x i‖ := norm_add_le _ _
        _ ≤ B+‖A.tensorEncode target x i‖ := add_le_add hb le_rfl
    have heq := congrArg (fun T => A.tensorEncode T x i)
      (square_smul_normalizedTensorDefect target (hδ n) (G n))
    rw [A.tensorEncode_smul] at heq
    change (δ n)^2 • A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i =
      A.tensorEncode (target-inducedTensor (G n)) x i at heq
    rw [← heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (δ n))]
    exact mul_le_mul_of_nonneg_left hn (sq_nonneg (δ n))
  have ht := A.tensor_tendsto_zero_of_encode hlocal p
  have ht' : Tendsto (fun n => (target-inducedTensor (G n)) p : ℕ → TensorFiber)
      atTop (𝓝 0) := ht
  have hv := ((ContinuousLinearMap.apply ℝ (Plane →L[ℝ] ℝ) (show Plane from v)).continuous.tendsto 0).comp ht'
  have hvw := ((ContinuousLinearMap.apply ℝ ℝ (show Plane from w)).continuous.tendsto 0).comp hv
  have hmetric : Tendsto (fun n => target p v w-
      (target-inducedTensor (G n)) p v w) atTop (𝓝 (target p v w-0)) :=
    tendsto_const_nhds.sub hvw
  convert hmetric using 1
  · ext n
    change inner ℝ (mfderiv planeModel spaceModel (G n) p v)
      (mfderiv planeModel spaceModel (G n) p w) =
      target p v w-(target p v w-inducedTensor (G n) p v w)
    rw [sub_sub_cancel]
    rfl
  · simp

omit [CompactSpace M] in
/-- The tensor weighted norm used by the correction step supplies the
coordinate bound required for metric convergence. -/
theorem metric_tendsto_of_normalized_bound
    {G : ℕ → M → Space} {δ s : ℕ → ℝ} {B : ℝ}
    (target : ∀ p : M, CovariantTwoTensor p)
    (hδ : ∀ n, δ n ≠ 0) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ n, A.TensorWeightedBound (s n) 0 B
      (normalizedTensorDefect target (δ n) (G n)-target))
    (p : M) (v w : TangentSpace planeModel p) :
    Tendsto (fun n => inner ℝ (mfderiv planeModel spaceModel (G n) p v)
      (mfderiv planeModel spaceModel (G n) p w)) atTop (𝓝 (target p v w)) := by
  apply A.metric_tendsto_of_normalized_coordinates_bound (B := B) target hδ hδ0 ?_ p v w
  intro n i x
  have hb := (hbound n i).norm_le (mem_univ x)
  change ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)-target) x i‖ ≤ B at hb
  simpa only [A.tensorEncode_sub,Pi.sub_apply] using hb

omit [CompactSpace M] in
/-- The encoded zeroth-order invariant of the iteration bounds the normalized
metric defect. -/
theorem metric_tendsto_of_encoded_normalized_bound
    {G : ℕ → M → Space} {δ : ℕ → ℝ} {B : ℝ}
    (target : ∀ p : M, CovariantTwoTensor p)
    (hδ : ∀ n, δ n ≠ 0) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ n x,
      ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x-
        A.tensorEncode target x‖ ≤ B)
    (p : M) (v w : TangentSpace planeModel p) :
    Tendsto (fun n => inner ℝ (mfderiv planeModel spaceModel (G n) p v)
      (mfderiv planeModel spaceModel (G n) p w)) atTop (𝓝 (target p v w)) := by
  apply A.metric_tendsto_of_normalized_coordinates_bound (B := B) target hδ hδ0 ?_ p v w
  intro n i x
  exact (norm_le_pi_norm _ i).trans (hbound n x)

/-- Actual atlas correction bounds and bounded normalized defects suffice
for an exact smooth isometric immersion at the series limit. -/
theorem correction_limit_isometric
    {F : M → Space} {U : ℕ → M → Space} {ρ δ s : ℕ → ℝ} {B : ℝ}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hU : ∀ n, ContMDiff planeModel spaceModel ∞ (U n))
    (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop, A.WeightedBound 1 m (ρ n) (U n))
    (houter : ∀ i x, x ∈ tsupport (A.weight i) →
      A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (g : SmoothMetric M) (hδ : ∀ n, δ n ≠ 0) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hdefect : ∀ n, A.TensorWeightedBound (s n) 0 B
      (normalizedTensorDefect g.inner (δ n) (manifoldPartialMap F U n)-g.inner)) :
    IsSmoothIsometricImmersion M g (manifoldLimitMap F U) := by
  obtain ⟨hs,hd⟩ := A.correction_limit hF hU hρ hbound houter
  refine ⟨hs,?_⟩
  intro p v w
  have hv := ((ContinuousLinearMap.apply ℝ Space (show Plane from v)).continuous.tendsto _).comp (hd p)
  have hw := ((ContinuousLinearMap.apply ℝ Space (show Plane from w)).continuous.tendsto _).comp (hd p)
  exact tendsto_nhds_unique (hv.inner hw)
    (A.metric_tendsto_of_normalized_bound g.inner hδ hδ0 hdefect p v w)

/-- The stage invariant in encoded tensor coordinates produces the same
isometric limit directly. -/
theorem correction_limit_isometric_of_encoded_bound
    {F : M → Space} {U : ℕ → M → Space} {ρ δ : ℕ → ℝ} {B : ℝ}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hU : ∀ n, ContMDiff planeModel spaceModel ∞ (U n))
    (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop, A.WeightedBound 1 m (ρ n) (U n))
    (houter : ∀ i x, x ∈ tsupport (A.weight i) →
      A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (g : SmoothMetric M) (hδ : ∀ n, δ n ≠ 0) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hdefect : ∀ n x,
      ‖A.tensorEncode (normalizedTensorDefect g.inner (δ n) (manifoldPartialMap F U n)) x-
        A.tensorEncode g.inner x‖ ≤ B) :
    IsSmoothIsometricImmersion M g (manifoldLimitMap F U) := by
  obtain ⟨hs,hd⟩ := A.correction_limit hF hU hρ hbound houter
  refine ⟨hs,?_⟩
  intro p v w
  have hv := ((ContinuousLinearMap.apply ℝ Space (show Plane from v)).continuous.tendsto _).comp (hd p)
  have hw := ((ContinuousLinearMap.apply ℝ Space (show Plane from w)).continuous.tendsto _).comp (hd p)
  exact tendsto_nhds_unique (hv.inner hw)
    (A.metric_tendsto_of_encoded_normalized_bound g.inner hδ hδ0 hdefect p v w)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
