import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Summable cold-jet datum bounds

Section 4 of the supplied manuscript bounds the mass and energy of each annulus by a constant
times `s_j²`, and its absolute entropy by a constant times `s_j² (1 + |log s_j|)`.
Those scalar bounds are summable for the stated geometric scales, and their tails converge
to zero. Indices start at zero; the manuscript's indices starting at one
are obtained by removing the first term.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace BoltzmannNonuniqueness.DatumBounds

/-- The annular scale `s₀ exp(-jη)`. -/
def scale (s₀ η : ℝ) (j : ℕ) : ℝ := s₀ * Real.exp (-(j : ℝ) * η)

/-- The summable majorant for the absolute entropy of one annulus. -/
def entropyBound (s₀ η : ℝ) (j : ℕ) : ℝ :=
  scale s₀ η j ^ 2 * (1 + |Real.log (scale s₀ η j)|)

theorem scale_pos {s₀ η : ℝ} (hs₀ : 0 < s₀) (j : ℕ) : 0 < scale s₀ η j :=
  mul_pos hs₀ (Real.exp_pos _)

theorem scale_pow (s₀ η : ℝ) (j p : ℕ) :
    scale s₀ η j ^ p = s₀ ^ p * Real.exp (-((p : ℝ) * η) * j) := by
  rw [scale, mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

theorem log_scale {s₀ η : ℝ} (hs₀ : 0 < s₀) (j : ℕ) :
    Real.log (scale s₀ η j) = Real.log s₀ - (j : ℝ) * η := by
  rw [scale, Real.log_mul hs₀.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem abs_log_scale_le {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η) (j : ℕ) :
    |Real.log (scale s₀ η j)| ≤ |Real.log s₀| + (j : ℝ) * η := by
  rw [log_scale hs₀]
  calc
    |Real.log s₀ - (j : ℝ) * η| ≤ |Real.log s₀| + |(j : ℝ) * η| := abs_sub _ _
    _ = |Real.log s₀| + (j : ℝ) * η := by
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hη)]

/-- Polynomial factors in the index remain summable against every positive power of the
geometric scale. This is used with `p = 2` and index powers zero and one below. -/
theorem summable_scale_pow_mul_nat_pow (s₀ : ℝ) {η : ℝ} (hη : 0 < η)
    (p k : ℕ) (hp : 0 < p) :
    Summable (fun j : ℕ => scale s₀ η j ^ p * (j : ℝ) ^ k) := by
  have hrate : 0 < (p : ℝ) * η := mul_pos (by exact_mod_cast hp) hη
  have h := (Real.summable_pow_mul_exp_neg_nat_mul k hrate).mul_left (s₀ ^ p)
  apply h.congr
  intro j
  rw [scale_pow]
  ring

theorem summable_scale_pow (s₀ : ℝ) {η : ℝ} (hη : 0 < η)
    (p : ℕ) (hp : 0 < p) : Summable (fun j : ℕ => scale s₀ η j ^ p) := by
  simpa only [pow_zero, mul_one] using summable_scale_pow_mul_nat_pow s₀ hη p 0 hp

theorem summable_scale_sq (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun j : ℕ => scale s₀ η j ^ 2) :=
  summable_scale_pow s₀ hη 2 (by norm_num)

theorem summable_index_mul_scale_sq (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun j : ℕ => scale s₀ η j ^ 2 * (j : ℝ)) := by
  simpa only [pow_one] using summable_scale_pow_mul_nat_pow s₀ hη 2 1 (by norm_num)

theorem entropyBound_nonneg (s₀ η : ℝ) (j : ℕ) : 0 ≤ entropyBound s₀ η j := by
  unfold entropyBound
  positivity

theorem entropyBound_le {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η) (j : ℕ) :
    entropyBound s₀ η j ≤
      scale s₀ η j ^ 2 * (1 + |Real.log s₀|) + scale s₀ η j ^ 2 * (j : ℝ) * η := by
  have h := mul_le_mul_of_nonneg_left
    (add_le_add_left (abs_log_scale_le hs₀ hη j) 1) (sq_nonneg (scale s₀ η j))
  unfold entropyBound
  nlinarith only [h]

/-- A positive scale power also absorbs the absolute logarithm; power four applies to the
vanishing hot-seed entropy estimate in the same datum lemma. -/
theorem summable_scale_pow_log {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (p : ℕ) (hp : 0 < p) :
    Summable (fun j : ℕ => scale s₀ η j ^ p * (1 + |Real.log (scale s₀ η j)|)) := by
  have hindex : Summable (fun j : ℕ => scale s₀ η j ^ p * (j : ℝ)) := by
    simpa only [pow_one] using summable_scale_pow_mul_nat_pow s₀ hη p 1 hp
  have hmajor := ((summable_scale_pow s₀ hη p hp).mul_right (1 + |Real.log s₀|)).add
    (hindex.mul_right η)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmajor
  · exact mul_nonneg (pow_nonneg (scale_pos (η := η) hs₀ j).le p) (by positivity)
  · have h := mul_le_mul_of_nonneg_left
      (add_le_add_left (abs_log_scale_le hs₀ hη.le j) 1)
      (pow_nonneg (scale_pos (η := η) hs₀ j).le p)
    nlinarith only [h]

theorem summable_entropyBound {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) :
    Summable (entropyBound s₀ η) := by
  exact summable_scale_pow_log hs₀ hη 2 (by norm_num)

theorem scale_tendsto_zero (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (scale s₀ η) atTop (𝓝 0) := by
  simpa only [pow_one] using (summable_scale_pow s₀ hη 1 (by norm_num)).tendsto_atTop_zero

theorem scale_pow_log_tendsto_zero {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (p : ℕ) (hp : 0 < p) :
    Tendsto (fun j : ℕ => scale s₀ η j ^ p * (1 + |Real.log (scale s₀ η j)|))
      atTop (𝓝 0) :=
  (summable_scale_pow_log hs₀ hη p hp).tendsto_atTop_zero

/-- The mass and energy scalar remainder after the first `N` annuli. -/
def massTail (s₀ η : ℝ) (N : ℕ) : ℝ := ∑' j : ℕ, scale s₀ η (j + N) ^ 2

/-- The absolute-entropy scalar remainder after the first `N` annuli. -/
def entropyTail (s₀ η : ℝ) (N : ℕ) : ℝ := ∑' j : ℕ, entropyBound s₀ η (j + N)

theorem massTail_nonneg (s₀ η : ℝ) (N : ℕ) : 0 ≤ massTail s₀ η N :=
  tsum_nonneg fun _ => sq_nonneg _

theorem entropyTail_nonneg (s₀ η : ℝ) (N : ℕ) : 0 ≤ entropyTail s₀ η N :=
  tsum_nonneg fun _ => entropyBound_nonneg _ _ _

theorem massTail_eq_tsum_sub_sum (s₀ : ℝ) {η : ℝ} (hη : 0 < η) (N : ℕ) :
    massTail s₀ η N = (∑' j : ℕ, scale s₀ η j ^ 2) - ∑ j ∈ range N, scale s₀ η j ^ 2 := by
  have h := (summable_scale_sq s₀ hη).sum_add_tsum_nat_add N
  unfold massTail
  linarith only [h]

theorem entropyTail_eq_tsum_sub_sum {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) (N : ℕ) :
    entropyTail s₀ η N = (∑' j : ℕ, entropyBound s₀ η j) -
      ∑ j ∈ range N, entropyBound s₀ η j := by
  have h := (summable_entropyBound hs₀ hη).sum_add_tsum_nat_add N
  unfold entropyTail
  linarith only [h]

theorem massTail_tendsto_zero (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (massTail s₀ η) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => ∑' j : ℕ, scale s₀ η j ^ 2) atTop
      (𝓝 (∑' j : ℕ, scale s₀ η j ^ 2)) := tendsto_const_nhds
  change Tendsto (fun N => massTail s₀ η N) atTop (𝓝 0)
  simp_rw [massTail_eq_tsum_sub_sum s₀ hη]
  simpa only [sub_self] using
    hconst.sub (summable_scale_sq s₀ hη).hasSum.tendsto_sum_nat

theorem entropyTail_tendsto_zero {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) :
    Tendsto (entropyTail s₀ η) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => ∑' j : ℕ, entropyBound s₀ η j) atTop
      (𝓝 (∑' j : ℕ, entropyBound s₀ η j)) := tendsto_const_nhds
  change Tendsto (fun N => entropyTail s₀ η N) atTop (𝓝 0)
  simp_rw [entropyTail_eq_tsum_sub_sum hs₀ hη]
  simpa only [sub_self] using
    hconst.sub (summable_entropyBound hs₀ hη).hasSum.tendsto_sum_nat

/-- Finite annular mass/energy bounds converge to their full sum. -/
theorem mass_partial_sums_tendsto (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N => ∑ j ∈ range N, scale s₀ η j ^ 2) atTop
      (𝓝 (∑' j : ℕ, scale s₀ η j ^ 2)) :=
  (summable_scale_sq s₀ hη).hasSum.tendsto_sum_nat

/-- Finite annular absolute-entropy bounds converge to their full sum. -/
theorem entropy_partial_sums_tendsto {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) :
    Tendsto (fun N => ∑ j ∈ range N, entropyBound s₀ η j) atTop
      (𝓝 (∑' j : ℕ, entropyBound s₀ η j)) :=
  (summable_entropyBound hs₀ hη).hasSum.tendsto_sum_nat

end BoltzmannNonuniqueness.DatumBounds

end

end OAI
