import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Moments.SubGaussian

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma condExp_exp_le_of_abs_le [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Y : Ω → ℝ} {a : ℝ}
    (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) (θ : ℝ) :
    μ[fun ω ↦ exp (θ * Y ω) | m] ≤ᵐ[μ]
      fun _ ↦ exp (a ^ 2 * θ ^ 2 / 2) := by
  have hIcc : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-a) a := by
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hYi : Integrable Y μ := Integrable.of_mem_Icc (-a) a (hY.measurable.aemeasurable (μ := μ)) hIcc
  have hEi : Integrable (fun ω ↦ exp (θ * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc (hY.measurable.aemeasurable (μ := μ)) hIcc
  let b : ℝ := sinh (a * θ) / a
  have hlin : Integrable (fun ω ↦ cosh (a * θ) + b * Y ω) μ :=
    (integrable_const _).add (hYi.const_mul b)
  have hpoint : (fun ω ↦ exp (θ * Y ω)) ≤ᵐ[μ]
      fun ω ↦ cosh (a * θ) + b * Y ω := by
    filter_upwards [hb] with ω hω
    have hdiv : |Y ω / a| ≤ 1 := by
      rw [abs_div, abs_of_pos ha, div_le_one ha]
      exact hω
    have he := exp_mul_le_cosh_add_mul_sinh hdiv (a * θ)
    convert he using 1
    · congr 1
      field_simp
    · dsimp [b]
      ring
  have hmono := condExp_mono (m := m) hEi hlin hpoint
  have hlinear : μ[fun ω ↦ cosh (a * θ) + b * Y ω | m] =ᵐ[μ]
      fun _ ↦ cosh (a * θ) := by
    have hAdd := condExp_add (integrable_const (cosh (a * θ))) (hYi.const_mul b) m
    have hMul := condExp_smul (μ := μ) b Y m
    filter_upwards [hAdd, hMul, hzero] with ω hA hM hZ
    change μ[fun ω ↦ b * Y ω | m] ω = b * μ[Y | m] ω at hM
    change μ[Y | m] ω = 0 at hZ
    simp only [Pi.add_def] at hA
    simpa only [condExp_const hm, hM, hZ, mul_zero, add_zero] using hA
  filter_upwards [hmono, hlinear] with ω hM hL
  rw [hL] at hM
  exact hM.trans (by simpa only [mul_pow] using cosh_le_exp_half_sq (a * θ))

lemma subGaussian_add_of_bounded_difference [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X Y : Ω → ℝ} {c : ℝ≥0} {a : ℝ}
    (hX : HasSubgaussianMGF X c μ) (hXm : StronglyMeasurable[m] X)
    (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) :
    HasSubgaussianMGF (X + Y) (c + NNReal.mk (a ^ 2) (sq_nonneg a)) μ := by
  have hEY (θ : ℝ) : Integrable (fun ω ↦ exp (θ * Y ω)) μ := by
    apply integrable_exp_mul_of_mem_Icc (hY.measurable.aemeasurable (μ := μ))
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hProd (θ : ℝ) : Integrable
      ((fun ω ↦ exp (θ * X ω)) * fun ω ↦ exp (θ * Y ω)) μ := by
    apply (hX.integrable_exp_mul θ).mul_bdd (hEY θ).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      θ * Y ω ≤ |θ * Y ω| := le_abs_self _
      _ = |θ| * |Y ω| := abs_mul _ _
      _ ≤ |θ| * a := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · intro θ
    simpa only [Pi.add_apply, mul_add, exp_add, Pi.mul_def] using hProd θ
  · intro θ
    have hPull := condExp_mul_of_stronglyMeasurable_left
      (f := fun ω ↦ exp (θ * X ω)) (g := fun ω ↦ exp (θ * Y ω))
      (by exact continuous_exp.comp_stronglyMeasurable (hXm.const_mul θ))
      (hProd θ) (hEY θ)
    have hPullInt : Integrable
        ((fun ω ↦ exp (θ * X ω)) * μ[fun ω ↦ exp (θ * Y ω) | m]) μ :=
      integrable_condExp.congr hPull
    have hcond := condExp_exp_le_of_abs_le hm ha hY hb hzero θ
    calc
      mgf (X + Y) μ θ = ∫ ω, exp (θ * X ω) * exp (θ * Y ω) ∂μ := by
        simp only [mgf, Pi.add_apply, mul_add, exp_add]
      _ = ∫ ω, exp (θ * X ω) * μ[fun ω ↦ exp (θ * Y ω) | m] ω ∂μ := by
        change (∫ ω, ((fun ω ↦ exp (θ * X ω)) * fun ω ↦ exp (θ * Y ω)) ω ∂μ) = _
        rw [← integral_condExp hm]
        exact integral_congr_ae hPull
      _ ≤ ∫ ω, exp (θ * X ω) * exp (a ^ 2 * θ ^ 2 / 2) ∂μ := by
        apply integral_mono_ae hPullInt ((hX.integrable_exp_mul θ).mul_const _)
        filter_upwards [hcond] with ω hω
        exact mul_le_mul_of_nonneg_left hω (exp_nonneg _)
      _ = mgf X μ θ * exp (a ^ 2 * θ ^ 2 / 2) := by rw [integral_mul_const]; rfl
      _ ≤ exp ((c : ℝ) * θ ^ 2 / 2) * exp (a ^ 2 * θ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (hX.mgf_le θ) (exp_nonneg _)
      _ = exp (((c + NNReal.mk (a ^ 2) (sq_nonneg a) : ℝ≥0) : ℝ) * θ ^ 2 / 2) := by
        rw [← exp_add]
        congr 1
        change (c : ℝ) * θ ^ 2 / 2 + a ^ 2 * θ ^ 2 / 2 = ((c : ℝ) + a ^ 2) * θ ^ 2 / 2
        ring

lemma subGaussian_sum_of_bounded_differences [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (n : ℕ)
    (hY : ∀ j < n, StronglyMeasurable[ℱ (j + 1)] (Y j))
    (hb : ∀ j < n, ∀ᵐ ω ∂μ, |Y j ω| ≤ a)
    (hzero : ∀ j < n, μ[Y j | ℱ j] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω)
      ((n : ℝ≥0) * NNReal.mk (a ^ 2) (sq_nonneg a)) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun j hj ↦ hY j (by omega))
      (fun j hj ↦ hb j (by omega)) (fun j hj ↦ hzero j (by omega))
    have hsum : StronglyMeasurable[ℱ n] (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      exact (hY j (by omega)).mono (ℱ.mono (by omega))
    have hnext := subGaussian_add_of_bounded_difference (ℱ.le n) hprev hsum ha
      ((hY n (by omega)).mono (ℱ.le (n + 1))) (hb n (by omega)) (hzero n (by omega))
    simpa only [Finset.sum_range_succ, Pi.add_def, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul] using hnext

lemma measure_abs_ge_le_of_subGaussian [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {c : ℝ≥0} (hY : HasSubgaussianMGF Y c μ)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |Y ω|} ≤ 2 * exp (-u ^ 2 / (2 * c)) := by
  have hset : {ω | u ≤ |Y ω|} = {ω | u ≤ Y ω} ∪ {ω | u ≤ -Y ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  have hp := hY.measure_ge_le hu
  have hn := hY.neg.measure_ge_le hu
  have huL := measureReal_union_le (μ := μ) {ω | u ≤ Y ω} {ω | u ≤ -Y ω}
  simp only [Pi.neg_apply] at hn
  linarith

end Balanced

end OAI
