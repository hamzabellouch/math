import OAI.Analysis.IrrationalRotation.Rotation.CircleBackgroundBumps

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open InvariantProjection.Continuity

namespace Invariant233.BackgroundCost

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : NullSingletonClass circleMeasure := ⟨circleMeasure_singleton⟩
local instance : IsFiniteMeasure circleMeasure := by
  change IsFiniteMeasure (volume : Measure (AddCircle (1 : ℝ)))
  infer_instance

theorem backgroundNegative_eq_finiteAverage {θ : ℝ} (d : BackgroundBumpData θ)
    (n : ℕ) (x : Circle) :
    backgroundNegative d n x =
      (∑ i : Fin (2 ^ (n + 2)),
        d.bump n (x - ((i : ℕ) + 1) • (θ : Circle))) / (2 : ℝ) ^ (n + 2) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => d.bump n (x - (i + 1) • (θ : Circle))) (2 ^ (n + 2))]
  unfold backgroundNegative backwardAverage backwardSum
  simp only [Equiv.addRight_symm, Equiv.coe_addRight, add_right_iterate,
    smul_neg, Nat.cast_pow, Nat.cast_ofNat, sub_eq_add_neg, div_eq_mul_inv, mul_comm]

theorem backgroundNegative_bounds {θ : ℝ} (d : BackgroundBumpData θ)
    (n : ℕ) (x : Circle) :
    0 ≤ backgroundNegative d n x ∧
      backgroundNegative d n x ≤ 1 / (2 : ℝ) ^ (n + 2) := by
  let T : Fin (2 ^ (n + 2)) → Circle ≃ Circle :=
    fun i => Equiv.addRight (((i : ℕ) + 1) • (θ : Circle))
  have hd := disjoint_support_comp_symm T (d.bump n)
    (Metric.closedBall 0 (d.radius n)) (d.bump_support n) (d.disjoint_translates n)
  have h := average_bounds_of_disjoint_support Finset.univ
    (fun i x => d.bump n ((T i).symm x))
    (fun i x => (d.bump_bounds n _).1) (fun i x => (d.bump_bounds n _).2)
    hd (W := (2 : ℝ) ^ (n + 2)) (by positivity) x
  rw [backgroundNegative_eq_finiteAverage]
  simpa only [T, Equiv.addRight_symm, Equiv.coe_addRight, sub_eq_add_neg] using h

theorem continuous_backgroundNegative {θ : ℝ} (d : BackgroundBumpData θ) (n : ℕ) :
    Continuous (backgroundNegative d n) := by
  have heq : backgroundNegative d n = fun x =>
      (∑ i : Fin (2 ^ (n + 2)),
        d.bump n (x - ((i : ℕ) + 1) • (θ : Circle))) / (2 : ℝ) ^ (n + 2) :=
    funext (backgroundNegative_eq_finiteAverage d n)
  rw [heq]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact (d.continuous_bump n).comp (continuous_id.sub continuous_const)

theorem measurable_backgroundCost {θ : ℝ} (d : BackgroundBumpData θ) :
    Measurable (backgroundCost d) := by
  exact (measurable_const.add
    (Measurable.tsum (fun n => (d.continuous_bump n).measurable))).sub
    (Measurable.tsum (fun n => (continuous_backgroundNegative d n).measurable))

theorem backgroundCost_ge_half {θ : ℝ} (d : BackgroundBumpData θ) (x : Circle) :
    1 / 2 ≤ backgroundCost d x := by
  apply background_cost_ge_half (d.bump) (backgroundNegative d)
    (fun n => 1 / (2 : ℝ) ^ (n + 2)) hasSum_background_majorant.summable
    hasSum_background_majorant.tsum_eq.le
    (fun n x => (d.bump_bounds n x).1)
    (fun n x => (backgroundNegative_bounds d n x).1)
    (fun n x => (backgroundNegative_bounds d n x).2)

theorem continuousOn_backgroundCost {θ : ℝ} (d : BackgroundBumpData θ) :
    ContinuousOn (backgroundCost d) ({0}ᶜ : Set Circle) := by
  exact background_cost_continuousOn 0 d.bump (backgroundNegative d) d.radius
    (fun n => 1 / (2 : ℝ) ^ (n + 2)) d.continuous_bump
    (continuous_backgroundNegative d) (BackgroundBumpData.radius_tendsto_zero d)
    (fun n x hx => d.bump_support n hx) hasSum_background_majorant.summable
    (fun n x => (backgroundNegative_bounds d n x).1)
    (fun n x => (backgroundNegative_bounds d n x).2)

theorem tendsto_backgroundCost_atTop {θ : ℝ} (d : BackgroundBumpData θ) :
    Tendsto (backgroundCost d) (𝓝[≠] (0 : Circle)) atTop := by
  exact tendsto_background_atTop 0 d.bump (backgroundNegative d)
    (fun n => 1 / (2 : ℝ) ^ (n + 2)) d.continuous_bump d.bump_zero
    (fun n x => (d.bump_bounds n x).1)
    (fun x hx => summable_of_support_shrinks 0 d.bump d.radius
      (BackgroundBumpData.radius_tendsto_zero d) (fun n y hy => d.bump_support n hy) hx)
    hasSum_background_majorant.summable
    (fun n x => (backgroundNegative_bounds d n x).1)
    (fun n x => (backgroundNegative_bounds d n x).2)

theorem integrable_backgroundCost {θ : ℝ} (d : BackgroundBumpData θ) :
    Integrable (backgroundCost d) circleMeasure := by
  have hμsum : (∑' n, circleMeasure (Metric.closedBall 0 (d.radius n))) < ∞ := by
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_))
      (d.weighted_support_bound.trans_lt (by norm_num))
    have hW : (1 : ℝ≥0∞) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using mul_le_mul_left hW
      (circleMeasure (Metric.closedBall 0 (d.radius n)))
  apply integrable_background_cost circleMeasure d.bump (backgroundNegative d)
    (fun n => Metric.closedBall 0 (d.radius n)) (fun n => 1 / (2 : ℝ) ^ (n + 2))
    (fun n => (d.continuous_bump n).measurable)
    (fun n => (continuous_backgroundNegative d n).measurable)
    (fun n x => (d.bump_bounds n x).1) (fun n x => (d.bump_bounds n x).2)
    d.bump_support ?_ hμsum hasSum_background_majorant.summable
    (fun n x => (backgroundNegative_bounds d n x).1)
    (fun n x => (backgroundNegative_bounds d n x).2)
  exact (circleMeasure.ae_ne 0).mono fun x hx =>
    summable_of_support_shrinks 0 d.bump d.radius
      (BackgroundBumpData.radius_tendsto_zero d) (fun n y hy => d.bump_support n hy) hx

theorem exists_background_cost (θ : ℝ) (hθ : Irrational θ) :
    ∃ g : Circle → ℝ, Measurable g ∧ ContinuousOn g ({0}ᶜ : Set Circle) ∧
      (∀ x, 1 / 2 ≤ g x) ∧ Tendsto g (𝓝[≠] (0 : Circle)) atTop ∧
      Integrable g circleMeasure := by
  obtain ⟨d⟩ := exists_backgroundBumpData θ hθ
  exact ⟨backgroundCost d, measurable_backgroundCost d, continuousOn_backgroundCost d,
    backgroundCost_ge_half d, tendsto_backgroundCost_atTop d, integrable_backgroundCost d⟩

end Invariant233.BackgroundCost

end

end OAI
