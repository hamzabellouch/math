import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BackwardSwitchProbability

namespace OAI

/-! # Subexponential mass and success probability in backward recurrence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology NNReal ENNReal

/-- A fixed number of backward recurrence steps retains subexponential
normalized mass. Both the initial mass and the enlargements may vary with
the scale. -/
theorem subexponential_backward_masses_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (h : ℕ) (a D : ℕ → ℕ → ℝ)
    (hlast : HasSubexponentialLowerBoundSeq scale (a h))
    (hD : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (D j))
    (hDpos : ∀ j, j < h → ∀ᶠ r in atTop, 0 < D j r)
    (hstep : ∀ j, j < h → ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D j r) ≤ a j r) :
    ∀ j, j ≤ h → HasSubexponentialLowerBoundSeq scale (a j) := by
  induction h with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    simpa only [this] using hlast
  | succ h ih =>
    have hah : HasSubexponentialLowerBoundSeq scale (a h) := by
      have hnum := hlast.mul hlast
      have hden := (sequence_subexponential_upper_const hscale 2).mul (hD h (by omega))
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
theorem subexponential_switch_product_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (τ : ℕ → ℕ → ℝ≥0) (n k : ℕ)
    (hτ : ∀ j, n ≤ j → j < n + k →
      HasSubexponentialLowerBoundSeq scale (fun r => (τ j r : ℝ))) :
    HasSubexponentialLowerBoundSeq scale (fun r => (switchThresholdProduct (fun j => τ j r) n k).toReal) := by
  induction k generalizing n with
  | zero => simpa only [switchThresholdProduct, ENNReal.toReal_one] using
      sequence_subexponential_lower_const hscale (by norm_num : (0 : ℝ) < 1)
  | succ k ih =>
    have htail := ih (n + 1) (fun j hj hj' => hτ j (by omega) (by omega))
    have hhead := hτ n le_rfl (by omega)
    simpa only [switchThresholdProduct, ENNReal.toReal_mul, ENNReal.coe_toReal] using
      hhead.mul htail

/-- The normalized masses supplied by recurrence give the required lower
bound on each threshold, with the same enlargement factors. -/
theorem subexponential_backward_thresholds_sequence
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (h : ℕ) (a D : ℕ → ℕ → ℝ)
    (hlast : HasSubexponentialLowerBoundSeq scale (a h))
    (hD : ∀ j, j < h → HasSubexponentialUpperBoundSeq scale (D j))
    (hDpos : ∀ j, j < h → ∀ᶠ r in atTop, 0 < D j r)
    (hstep : ∀ j, j < h → ∀ᶠ r in atTop,
      a (j + 1) r ^ 2 / (2 * D j r) ≤ a j r) :
    ∀ j, j < h → HasSubexponentialLowerBoundSeq scale (fun r => a (j + 1) r / (2 * D j r)) := by
  intro j hj
  apply (subexponential_backward_masses_sequence scale hscale h a D hlast hD hDpos hstep (j + 1) (by omega)).div
  · exact (sequence_subexponential_upper_const hscale 2).mul (hD j hj)
      (Eventually.of_forall (fun _ => by norm_num))
  · exact (hDpos j hj).mono (fun _ hr => mul_pos (by norm_num) hr)

end PolycyclicRecognition

end OAI
