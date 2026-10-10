import OAI.Analysis.IrrationalRotation.Analysis.ExponentialExtension
import OAI.Analysis.IrrationalRotation.Model.Analytic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

namespace OAI

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem tendsto_integral_min_atTop [IsFiniteMeasure μ] {g : X → ℝ}
    (hg : Measurable g) (hpos : ∀ x, 0 ≤ g x)
    (hinf : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ∞) :
    Tendsto (fun n : ℕ => ∫ x, min (g x) (n : ℝ) ∂μ) atTop atTop := by
  have hnonneg (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ min (g x) (n : ℝ) :=
    Eventually.of_forall fun x => le_min (hpos x) (Nat.cast_nonneg n)
  have hint (n : ℕ) : Integrable (fun x => min (g x) (n : ℝ)) μ :=
    (integrable_const (n : ℝ)).mono_nonneg
      (hg.min measurable_const).aestronglyMeasurable (hnonneg n)
      (Eventually.of_forall fun x => min_le_right _ _)
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  simp_rw [ofReal_integral_eq_lintegral_ofReal (hint _) (hnonneg _)]
  rw [← hinf]
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (hg.min measurable_const).ennreal_ofReal.aemeasurable
  · exact Eventually.of_forall fun x i j hij =>
      ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hij))
  · apply Eventually.of_forall
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (g x)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [min_eq_left (hN.trans (Nat.cast_le.mpr hn))]

variable {x₀ x : X} {g : X → ℝ}

omit [MeasurableSpace X] in
theorem truncatedLog_exponentialWeight_of_ne (hx : x ≠ x₀) (M : ℝ) :
    Real.log (max (exponentialWeight x₀ g x) (Real.exp (-M))) =
      -min (g x) M := by
  rw [exponentialWeight_of_ne hx]
  by_cases h : g x ≤ M
  · rw [min_eq_left h, max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp]
  · have h' : M ≤ g x := le_of_not_ge h
    rw [min_eq_right h', max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h')),
      Real.log_exp]

theorem lintegral_neg_log_exponentialWeight
    (hpoint : μ {x₀} = 0) :
    (∫⁻ x, ENNReal.ofReal (-Real.log (exponentialWeight x₀ g x)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  apply lintegral_congr_ae
  have hne : ∀ᵐ x ∂μ, x ≠ x₀ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hpoint
  filter_upwards [hne] with x hx
  rw [log_exponentialWeight_of_ne hx, neg_neg]

theorem tendsto_integral_truncatedLog_atBot [IsFiniteMeasure μ]
    (hpoint : μ {x₀} = 0) (hg : Measurable g) (hpos : ∀ x, 0 ≤ g x)
    (hinf : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ∞) :
    Tendsto (fun n : ℕ => ∫ x,
      Real.log (max (exponentialWeight x₀ g x) (Real.exp (-(n : ℝ)))) ∂μ)
      atTop atBot := by
  have hne : ∀ᵐ x ∂μ, x ≠ x₀ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hpoint
  have heq (n : ℕ) :
      (∫ x, Real.log (max (exponentialWeight x₀ g x) (Real.exp (-(n : ℝ)))) ∂μ) =
        -(∫ x, min (g x) (n : ℝ) ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hne] with x hx
    exact truncatedLog_exponentialWeight_of_ne hx _
  simp_rw [heq]
  exact tendsto_neg_atTop_atBot.comp (tendsto_integral_min_atTop hg hpos hinf)

theorem exists_truncatedLog_integral_lt [IsFiniteMeasure μ]
    (hpoint : μ {x₀} = 0) (hg : Measurable g) (hpos : ∀ x, 0 ≤ g x)
    (hinf : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ∞) (a : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (exponentialWeight x₀ g x) (Real.exp (-M))) ∂μ) < -2 * a := by
  have hlim := tendsto_integral_truncatedLog_atBot hpoint hg hpos hinf
  have hev := hlim.eventually (eventually_lt_atBot (-2 * a))
  obtain ⟨n, hn, hi⟩ := ((eventually_gt_atTop (0 : ℕ)).and hev).exists
  exact ⟨n, Nat.cast_pos.mpr hn, hi⟩

omit [MeasurableSpace X] in

theorem negLogCost_exponentialWeight_of_ne (hx : x ≠ x₀) :
    negLogCost (exponentialWeight x₀ g x) = ENNReal.ofReal (g x) := by
  rw [exponentialWeight_of_ne hx, negLogCost,
    ite_eq_right (Real.exp_ne_zero _), abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]

theorem hasNegInfiniteLogIntegral_exponentialWeight
    (hpoint : μ {x₀} = 0)
    (hinf : ∫⁻ x, ENNReal.ofReal (g x) ∂μ = ∞) :
    HasNegInfiniteLogIntegral μ (exponentialWeight x₀ g) := by
  unfold HasNegInfiniteLogIntegral
  rw [← hinf]
  apply lintegral_congr_ae
  have hne : ∀ᵐ x ∂μ, x ≠ x₀ := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hpoint
  filter_upwards [hne] with x hx
  exact negLogCost_exponentialWeight_of_ne hx

theorem scalarWeightDeterminant_eq_zero_of_log {f : X → ℝ}
    (hf : HasNegInfiniteLogIntegral μ f) : scalarWeightDeterminant μ f = 0 := by
  simp [scalarWeightDeterminant, HasNegInfiniteLogIntegral] at hf ⊢
  rw [hf]

theorem isContinuousCircleWeight_exponentialWeight {g : Circle → ℝ}
    (hg : ContinuousOn g {0}ᶜ) (hpos : ∀ x ≠ 0, 0 ≤ g x)
    (hlim : Tendsto g (𝓝[≠] 0) atTop)
    (hinf : ∫⁻ x, ENNReal.ofReal (g x) ∂circleMeasure = ∞) :
    IsContinuousCircleWeight (exponentialWeight 0 g) := by
  refine ⟨continuous_exponentialWeight hg hlim,
    fun x => exponentialWeight_mem_Icc hpos x,
    fun x => exponentialWeight_eq_zero_iff, ?_⟩
  apply hasNegInfiniteLogIntegral_exponentialWeight _ hinf
  change volume ({0} : Set (AddCircle (1 : ℝ))) = 0
  rw [← Metric.closedBall_zero (x := (0 : AddCircle (1 : ℝ))), AddCircle.volume_closedBall]
  norm_num

end Invariant233

end OAI
