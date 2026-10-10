import OAI.NumberTheory.Ostmann.QuadraticCenter.RepeatAverage
import OAI.NumberTheory.Ostmann.QuadraticCenter.ThresholdPower

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem weighted_distinct_moment_error {α ι : Type*} [DecidableEq ι]
    (w : α → ℝ) (hw : ∀ n, 0 ≤ w n) (hsw : Summable w)
    (P : Finset ι) (hP : 0 < P.card) (y : α → ι → ℤ)
    (hy : ∀ n, ∀ p ∈ P, y n p = -1 ∨ y n p = 0 ∨ y n p = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) {τ : ℝ} (hτ : 0 < τ) :
    |(∑' n, w n * distinctSignAverage P (y n) k) -
      (∑' n, w n * signAverage P (y n) ^ k)| ≤
    (((k : ℝ) + 1) * (k : ℝ) ^ 2 / P.card) *
      (τ + (k : ℝ) / Real.sqrt (P.card : ℝ)) ^ (k - 2) *
        ((∑' n, w n) + (∑' n, w n * signAverage P (y n) ^ k) / τ ^ k) := by
  let H : α → ℝ := fun n => signAverage P (y n)
  let D : α → ℝ := fun n => distinctSignAverage P (y n) k
  let C : ℝ := ((k : ℝ) + 1) * (k : ℝ) ^ 2 / P.card
  let a : ℝ := (k : ℝ) / Real.sqrt (P.card : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hH (n : α) : |H n| ≤ 1 := abs_signAverage_le_one P hP (y n) (hy n)
  have hp0 (n : α) : 0 ≤ H n ^ k := heven.pow_nonneg _
  have hp1 (n : α) : H n ^ k ≤ 1 := by
    rw [← heven.pow_abs]
    exact pow_le_one₀ (abs_nonneg _) (hH n)
  have hsI : Summable (fun n => w n * H n ^ k) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (hp0 n))
      (fun n => mul_le_of_le_one_right (hw n) (hp1 n)) hsw
  have hsU : Summable (fun n => w n * (|H n| + a) ^ (k - 2)) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hw n) (pow_nonneg (add_nonneg (abs_nonneg _) ha) _)) ?_
      (hsw.mul_right ((1 + a) ^ (k - 2)))
    intro n
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) ha) (add_le_add (hH n) le_rfl) _) (hw n)
  have herror (n : α) : |D n - H n ^ k| ≤ C * (|H n| + a) ^ (k - 2) :=
    distinctSignAverage_error P hP (y n) (hy n) hk heven
  let e : α → ℝ := fun n => w n * (D n - H n ^ k)
  have he_bound (n : α) : ‖e n‖ ≤ C * (w n * (|H n| + a) ^ (k - 2)) := by
    have hb := mul_le_mul_of_nonneg_left (herror n) (hw n)
    simpa only [e, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw n), mul_left_comm] using hb
  have hsNorm : Summable (fun n => ‖e n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) he_bound (hsU.mul_left C)
  have hsE : Summable e := Summable.of_norm hsNorm
  have hsD : Summable (fun n => w n * D n) := by
    apply (hsE.add hsI).congr
    intro n
    dsimp [e]
    ring
  have heq : (∑' n, w n * D n) - (∑' n, w n * H n ^ k) = ∑' n, e n := by
    rw [← hsD.tsum_sub hsI]
    apply tsum_congr
    intro n
    dsimp [e]
    ring
  have hsAbs : Summable (fun n => w n * |H n| ^ k) := by
    simpa only [heven.pow_abs] using hsI
  have ht := weighted_shifted_power_le_threshold w (fun n => |H n|)
    hw (fun _ => abs_nonneg _) hsw ha hτ k hsAbs
  simp only [heven.pow_abs] at ht
  change |(∑' n, w n * D n) - (∑' n, w n * H n ^ k)| ≤
    C * (τ + a) ^ (k - 2) * ((∑' n, w n) + (∑' n, w n * H n ^ k) / τ ^ k)
  rw [heq]
  calc
    _ ≤ ∑' n, ‖e n‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsNorm
    _ ≤ ∑' n, C * (w n * (|H n| + a) ^ (k - 2)) :=
      hsNorm.tsum_le_tsum he_bound (hsU.mul_left C)
    _ = C * ∑' n, w n * (|H n| + a) ^ (k - 2) := tsum_mul_left
    _ ≤ C * ((τ + a) ^ (k - 2) *
        ((∑' n, w n) + (∑' n, w n * H n ^ k) / τ ^ k)) :=
      mul_le_mul_of_nonneg_left ht hC
    _ = _ := by ring

end Ostmann.QuadraticCenter

end OAI
