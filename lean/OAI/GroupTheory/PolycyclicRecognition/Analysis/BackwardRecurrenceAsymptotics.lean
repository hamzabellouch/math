import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialBounds
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BackwardSwitchProbability

namespace OAI

/-! # Subexponential mass and success probability in backward recurrence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal ENNReal

/-- A fixed number of backward recurrence steps retains subexponential
normalized mass. Both the initial mass and the enlargements may vary with
the scale. -/
theorem subexponential_backward_masses (h : ℕ) (a D : ℕ → ℝ → ℝ)
    (hlast : HasSubexponentialLowerBound (a h))
    (hD : ∀ j, j < h → HasSubexponentialUpperBound (D j))
    (hDpos : ∀ j, j < h → ∀ᶠ r in atTop, 0 < D j r)
    (hstep : ∀ j, j < h → ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D j r) ≤ a j r) :
    ∀ j, j ≤ h → HasSubexponentialLowerBound (a j) := by
  induction h with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    simpa only [this] using hlast
  | succ h ih =>
    have hah : HasSubexponentialLowerBound (a h) := by
      have hnum := hlast.mul hlast
      have hden := (subexponential_upper_const 2).mul (hD h (by omega))
        (Eventually.of_forall (fun _ => by norm_num))
      have hp : ∀ᶠ r in atTop, 0 < 2 * D h r :=
        (hDpos h (by omega)).mono (fun _ hr => mul_pos (by norm_num) hr)
      have hl := hnum.div hden hp
      apply hl.mono
      filter_upwards [hstep h (by omega)] with r hr
      simpa only [pow_two] using hr
    intro j hj
    by_cases he : j = h + 1
    · simpa only [he] using hlast
    · exact ih hah (fun k hk => hD k (by omega))
        (fun k hk => hDpos k (by omega)) (fun k hk => hstep k (by omega)) j (by omega)

/-- A fixed ordered product of transition probabilities retains a
subexponential lower bound. -/
theorem subexponential_switch_product (τ : ℕ → ℝ → ℝ≥0) (n k : ℕ)
    (hτ : ∀ j, n ≤ j → j < n + k →
      HasSubexponentialLowerBound (fun r => (τ j r : ℝ))) :
    HasSubexponentialLowerBound (fun r => (switchThresholdProduct (fun j => τ j r) n k).toReal) := by
  induction k generalizing n with
  | zero => simpa only [switchThresholdProduct, ENNReal.toReal_one] using
      subexponential_lower_const (by norm_num : (0 : ℝ) < 1)
  | succ k ih =>
    have htail := ih (n + 1) (fun j hj hj' => hτ j (by omega) (by omega))
    have hhead := hτ n le_rfl (by omega)
    simpa only [switchThresholdProduct, ENNReal.toReal_mul, ENNReal.coe_toReal] using
      hhead.mul htail

/-- The normalized masses supplied by recurrence give the required lower
bound on each threshold, with the same enlargement factors. -/
theorem subexponential_backward_thresholds (h : ℕ) (a D : ℕ → ℝ → ℝ)
    (hlast : HasSubexponentialLowerBound (a h))
    (hD : ∀ j, j < h → HasSubexponentialUpperBound (D j))
    (hDpos : ∀ j, j < h → ∀ᶠ r in atTop, 0 < D j r)
    (hstep : ∀ j, j < h → ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D j r) ≤ a j r) :
    ∀ j, j < h → HasSubexponentialLowerBound (fun r => a (j + 1) r / (2 * D j r)) := by
  intro j hj
  apply (subexponential_backward_masses h a D hlast hD hDpos hstep (j + 1) (by omega)).div
  · exact (subexponential_upper_const 2).mul (hD j hj)
      (Eventually.of_forall (fun _ => by norm_num))
  · exact (hDpos j hj).mono (fun _ hr => mul_pos (by norm_num) hr)

end PolycyclicRecognition

end OAI
