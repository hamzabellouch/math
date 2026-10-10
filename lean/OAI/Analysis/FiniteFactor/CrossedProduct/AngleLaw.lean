import OAI.Analysis.FiniteFactor.CrossedProduct.StageOperator
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The source angle interval has length 1/N_s, where N_s=m_s K_s. -/
def sourceAngleUnit (i : SourceCoordinate) : ℝ :=
  1 / ((sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K)

theorem sourceAngleUnit_pos (i : SourceCoordinate) : 0 < sourceAngleUnit i :=
  one_div_pos.mpr (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))

def sourceAngleInterval (i : SourceCoordinate) : Set ℝ :=
  Set.Icc (sourceAngleUnit i) (2 * sourceAngleUnit i)

/-- Normalized Lebesgue measure on the actual source interval. -/
def sourceAngleMarginal (i : SourceCoordinate) : Measure ℝ :=
  cond volume (sourceAngleInterval i)

theorem sourceAngleInterval_volume (i : SourceCoordinate) :
    volume (sourceAngleInterval i) = ENNReal.ofReal (sourceAngleUnit i) := by
  simp [sourceAngleInterval, Real.volume_Icc, show 2 * sourceAngleUnit i - sourceAngleUnit i = sourceAngleUnit i by ring]

instance sourceAngleMarginal_probability (i : SourceCoordinate) :
    IsProbabilityMeasure (sourceAngleMarginal i) := by
  unfold sourceAngleMarginal
  apply cond_isProbabilityMeasure_of_finite
  · rw [sourceAngleInterval_volume]; exact (ENNReal.ofReal_pos.mpr (sourceAngleUnit_pos i)).ne'
  · rw [sourceAngleInterval_volume]; exact ENNReal.ofReal_ne_top

instance sourceAngleMarginal_atomless (i : SourceCoordinate) :
    NullSingletonClass (sourceAngleMarginal i) := by
  constructor
  intro x
  exact cond_absolutelyContinuous (measure_singleton x)

/-- This law is selected before any invariant projection is considered. -/
def sourceAngleLaw : Measure (SourceCoordinate → ℝ) :=
  Measure.infinitePi sourceAngleMarginal

instance sourceAngleLaw_probability : IsProbabilityMeasure sourceAngleLaw := by
  unfold sourceAngleLaw
  infer_instance

theorem sourceAngleLaw_coordinate (i : SourceCoordinate) :
    sourceAngleLaw.map (fun θ => θ i) = sourceAngleMarginal i :=
  Measure.infinitePi_map_eval _ _

theorem sourceAngleLaw_independent :
    iIndepFun (fun i (θ : SourceCoordinate → ℝ) => θ i) sourceAngleLaw :=
  iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)

theorem sourceAngleLaw_cylinder (I : Finset SourceCoordinate)
    (S : SourceCoordinate → Set ℝ) (hS : ∀ i ∈ I, MeasurableSet (S i)) :
    sourceAngleLaw (Set.pi (I : Set SourceCoordinate) S) =
      ∏ i ∈ I, sourceAngleMarginal i (S i) :=
  Measure.infinitePi_pi _ hS

theorem sourceAngleMarginal_ae (i : SourceCoordinate) :
    ∀ᵐ t ∂sourceAngleMarginal i, t ∈ sourceAngleInterval i := by
  exact ae_cond_mem measurableSet_Icc

/-- All interval constraints hold simultaneously, not just coordinatewise. -/
theorem sourceAngleLaw_admissible : ∀ᵐ θ ∂sourceAngleLaw, SourceAngles θ := by
  have h (i : SourceCoordinate) : ∀ᵐ θ ∂sourceAngleLaw, θ i ∈ sourceAngleInterval i := by
    have hh := sourceAngleMarginal_ae i
    rw [← sourceAngleLaw_coordinate i] at hh
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Icc).mp hh
  filter_upwards [ae_all_iff.mpr h] with θ hθ
  intro i
  change (1 : ℝ) / ((sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K) ≤ θ i ∧
    θ i ≤ 2 / ((sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K)
  simpa [sourceAngleInterval, sourceAngleUnit, div_eq_mul_inv] using hθ i

theorem sourceAngleLaw_operator : ∀ᵐ θ ∂sourceAngleLaw, ∃ hθ : SourceAngles θ,
    let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
    T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
      Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  filter_upwards [sourceAngleLaw_admissible] with θ hθ
  exact ⟨hθ, staged_sourceOperator_properties θ hθ⟩

end
end FiniteFactor

end OAI
