import OAI.Geometry.SurfaceImmersion.Correction.AdaptiveCorrectionSequence
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricLimit

namespace OAI

/-! The adaptive construction produces a smooth isometric immersion
from admissible finite initial data by choosing a correction sequence. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection
local instance exactFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance exactFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance exactDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance exactDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance exactSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance exactSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection

/-- Construction, growth of derivative order, and passage to the actual
metric limit are combined here. Only finite initial input data remain. -/
theorem sequence_limit_isometric (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F) {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)
    (seed : c.Stage t 0) : IsSmoothIsometricImmersion M g
      (manifoldLimitMap seed.map (c.increment hF ht htsmall seed)) := by
  let U := c.increment hF ht htsmall seed
  let δ := fun n => (correctionScale t n)^
    (correctionOrder (c.sequence hF ht htsmall seed n).order : ℝ)
  change IsSmoothIsometricImmersion M g (manifoldLimitMap seed.map U)
  apply d.A.correction_limit_isometric_of_encoded_bound seed.smooth
    (c.increment_smooth hF ht htsmall seed)
    ((correctionScale_summable ht.le htsmall).1.mul_left c.ρ)
    (c.increment_eventual_bound hF ht htsmall seed) d.outer_locally_one g
    (δ := δ) (B := c.a/8)
  · intro n
    exact ne_of_gt (Real.rpow_pos_of_pos (correctionScale_pos ht n) _)
  · exact c.sequence_amplitude_tendsto hF ht htsmall seed
  · intro n x
    have hh := (c.sequence hF ht htsmall seed n).metric x
    rw [c.sequence_partialMap hF ht htsmall seed n] at hh
    exact hh


theorem exists_isometric_of_stage (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F) {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)
    (seed : c.Stage t 0) : ∃ G : M → Space, IsSmoothIsometricImmersion M g G :=
  ⟨_,c.sequence_limit_isometric hF ht htsmall seed⟩

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {g : SmoothMetric M} {F : M → Space}

namespace MetricGoodPhaseData
/-- Finite quantitative initial conditions suffice for an exact smooth
correction. The derivative order is exactly the initial order 440, and all
later higher norms are dealt with by the constructed adaptive sequence. -/
theorem finite_input_exact_correction (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ a ρ B ε : ℝ, 0 < a ∧ 0 < ρ ∧ 0 < B ∧ 0 < ε ∧ ε ≤ 1/32 ∧
    ∀ (t : ℝ), 0 < t → t < ε → ∀ G : M → Space,
    ContMDiff planeModel spaceModel ∞ G →
    d.A.InputBound t 440 B G (normalizedTensorDefect g.inner (t^(10 : ℝ)) G) →
    d.A.WeightedBound 1 2 (ρ/8) (G-F) →
    (∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner (t^(10 : ℝ)) G) x-
      d.A.tensorEncode g.inner x‖ ≤ a/8) →
    ∃ G' : M → Space, IsSmoothIsometricImmersion M g G' := by
  classical
  let c := Classical.choice (d.preparedCorrection_nonempty hF)
  refine ⟨c.a,c.ρ,c.budget,min (c.ε 0) (1/32),c.a_pos,c.ρ_pos,c.budget_pos,
    lt_min (c.ε_pos 0) (by norm_num),min_le_right _ _,?_⟩
  intro t ht htε G hG hin hnear hmetric
  apply c.exists_isometric_of_stage hF ht (htε.le.trans (min_le_right _ _))
  refine ⟨0,G,hG,?_,?_,?_,?_⟩
  · exact htε.trans_le (min_le_left _ _)
  · simpa only [ExactCorrection.correctionScale,correctionInputOrder,correctionOrder,
      Nat.zero_add,Nat.cast_ofNat,show 40*(10+1) = 440 from rfl] using hin
  · simpa only [PreparedCorrection.stageRadius,Finset.range_zero,Finset.sum_empty,
      mul_zero,add_zero] using hnear
  · simpa only [ExactCorrection.correctionScale,correctionOrder,Nat.zero_add,Nat.cast_ofNat] using hmetric
end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
