import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open Filter Topology

def savingExponent : ℝ := 1 / 10000000000
def witnessConstant : ℝ := 1 / (9 * 2 ^ 57)
def graphScaleConstant : ℝ := 9 * 2 ^ 58
def densityScale (q : ℝ) : ℝ := q ^ savingExponent
def graphScale (U : ℝ) : ℝ := graphScaleConstant * U ^ 39
def expansionScale (V : ℝ) : ℝ := 2 ^ 23 * V ^ 24

@[simp] theorem savingExponent_pos : 0 < savingExponent := by
  norm_num [savingExponent]
theorem savingExponent_lt_tenth : savingExponent < 1 / 10 := by
  norm_num [savingExponent]
theorem witnessConstant_pos : 0 < witnessConstant := by
  norm_num [witnessConstant]
theorem graphScaleConstant_pos : 0 < graphScaleConstant := by
  norm_num [graphScaleConstant]
theorem graphScaleConstant_eq : graphScaleConstant = 2 / witnessConstant := by
  norm_num [graphScaleConstant, witnessConstant]

theorem graphScale_pos {U : ℝ} (hU : 0 < U) : 0 < graphScale U :=
  mul_pos graphScaleConstant_pos (pow_pos hU _)
theorem expansionScale_pos {V : ℝ} (hV : 0 < V) : 0 < expansionScale V :=
  mul_pos (by norm_num) (pow_pos hV _)

theorem scaled_power_identity (A U : ℝ) (a b c : ℕ) :
    A * U ^ a * (graphScale U) ^ b * (expansionScale (graphScale U)) ^ c =
      (A * graphScaleConstant ^ b * (2 ^ 23 * graphScaleConstant ^ 24) ^ c) *
        U ^ (a + 39 * b + 936 * c) := by
  simp only [graphScale, expansionScale, mul_pow, pow_add, pow_mul]
  rw [show (936 : ℕ) = 39 * 24 from rfl, pow_mul]
  ring

theorem eventually_coefficient_density_power_lt_sqrt
    (A : ℝ) (m : ℕ) (hm : savingExponent * m < 1 / 2) :
    ∀ᶠ q : ℝ in atTop, A * densityScale q ^ m < Real.sqrt q := by
  have hgap : 0 < (1 / 2 : ℝ) - savingExponent * m := sub_pos.mpr hm
  have hgrow := (tendsto_rpow_atTop hgap).eventually_gt_atTop A
  filter_upwards [eventually_gt_atTop (0 : ℝ), hgrow] with q hq hbound
  have hpow : 0 < q ^ (savingExponent * m) := Real.rpow_pos_of_pos hq _
  have hmul := mul_lt_mul_of_pos_right hbound hpow
  have hid : q ^ ((1 / 2 : ℝ) - savingExponent * m) *
      q ^ (savingExponent * m) = Real.sqrt q := by
    rw [← Real.rpow_add hq, sub_add_cancel, Real.sqrt_eq_rpow]
  rw [hid] at hmul
  simpa only [densityScale, Real.rpow_mul_natCast hq.le] using hmul

theorem eventually_scaled_powers_lt_sqrt (A : ℝ) (a b c : ℕ)
    (hExp : savingExponent * (a + 39 * b + 936 * c : ℕ) < 1 / 2) :
    ∀ᶠ q : ℝ in atTop,
      A * densityScale q ^ a * (graphScale (densityScale q)) ^ b *
        (expansionScale (graphScale (densityScale q))) ^ c < Real.sqrt q := by
  have h := eventually_coefficient_density_power_lt_sqrt
    (A * graphScaleConstant ^ b * (2 ^ 23 * graphScaleConstant ^ 24) ^ c)
    (a + 39 * b + 936 * c) hExp
  filter_upwards [h] with q hq
  simpa only [scaled_power_identity] using hq

def LargeEnough (q : ℝ) : Prop :=
  let U := densityScale q
  let V := graphScale U
  let K := expansionScale V
  0 < q ∧ 2 ≤ U ∧
    16 * U ^ 2 ≤ Real.sqrt q ∧
    4096 * U ^ 7 ≤ Real.sqrt q ∧
    (96 / witnessConstant) * U ^ 42 ≤ Real.sqrt q ∧
    32 * V ^ 2 * K ^ 127942 < 3 * Real.sqrt q ∧
    4096 * V ^ 6 * K ^ 3 < 27 * Real.sqrt q ∧
    2 * K ^ 527 * V ≤ Real.sqrt q

theorem eventually_largeEnough : ∀ᶠ q : ℝ in atTop, LargeEnough q := by
  have hU := (tendsto_rpow_atTop savingExponent_pos).eventually_ge_atTop 2
  have h2 := eventually_scaled_powers_lt_sqrt 16 2 0 0 (by norm_num [savingExponent])
  have h7 := eventually_scaled_powers_lt_sqrt 4096 7 0 0 (by norm_num [savingExponent])
  have h42 := eventually_scaled_powers_lt_sqrt (96 / witnessConstant) 42 0 0
    (by norm_num [savingExponent])
  have hfirst := eventually_scaled_powers_lt_sqrt (32 / 3) 0 2 127942
    (by norm_num [savingExponent])
  have hsecond := eventually_scaled_powers_lt_sqrt (4096 / 27) 0 6 3
    (by norm_num [savingExponent])
  have hthird := eventually_scaled_powers_lt_sqrt 2 0 1 527
    (by norm_num [savingExponent])
  filter_upwards [eventually_gt_atTop (0 : ℝ), hU, h2, h7, h42,
    hfirst, hsecond, hthird] with q hq hu h2q h7q h42q hf hs ht
  simp only [pow_zero, pow_one, mul_one] at h2q h7q h42q hf hs ht
  refine ⟨hq, hu, h2q.le, h7q.le, h42q.le, ?_, ?_, ?_⟩
  · nlinarith only [hf]
  · nlinarith only [hs]
  · have heq : 2 * expansionScale (graphScale (densityScale q)) ^ 527 *
        graphScale (densityScale q) =
      2 * graphScale (densityScale q) * expansionScale (graphScale (densityScale q)) ^ 527 := by
        ring
    rw [heq]
    exact ht.le

theorem exists_threshold_largeEnough :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → LargeEnough (q : ℝ) := by
  have h : ∀ᶠ q : ℕ in atTop, LargeEnough (q : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually eventually_largeEnough
  exact eventually_atTop.mp h

def incidenceThreshold : ℕ := Classical.choose exists_threshold_largeEnough

theorem largeEnough_of_threshold {q : ℕ} (hq : incidenceThreshold ≤ q) :
    LargeEnough (q : ℝ) :=
  Classical.choose_spec exists_threshold_largeEnough q hq

end
end RyserCoveringCounterexample.Incidence

end OAI
