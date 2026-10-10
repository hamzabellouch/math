import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialBounds

namespace OAI

/-! # Powers, sums, minima and reciprocals of subexponential bounds -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem HasSubexponentialLowerBound.pow {f : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) (n : ℕ) :
    HasSubexponentialLowerBound (fun r => f r ^ n) := by
  induction n with
  | zero => simpa using subexponential_lower_const zero_lt_one
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem HasSubexponentialLowerBound.min {f g : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) (hg : HasSubexponentialLowerBound g) :
    HasSubexponentialLowerBound (fun r => min (f r) (g r)) := by
  intro ε hε
  filter_upwards [hf ε hε, hg ε hε] with r hr hs
  exact le_min hr hs

theorem HasSubexponentialLowerBound.inv {f : ℝ → ℝ}
    (hf : HasSubexponentialLowerBound f) :
    HasSubexponentialUpperBound (fun r => (f r)⁻¹) := by
  intro ε hε
  filter_upwards [hf ε hε] with r hr
  calc
    (f r)⁻¹ ≤ (Real.exp (-ε * r))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hr
    _ = Real.exp (ε * r) := by rw [← Real.exp_neg]; congr 1; ring

theorem HasSubexponentialUpperBound.pow {f : ℝ → ℝ}
    (hf : HasSubexponentialUpperBound f) (hf0 : ∀ᶠ r in atTop, 0 ≤ f r) (n : ℕ) :
    HasSubexponentialUpperBound (fun r => f r ^ n) := by
  induction n with
  | zero => simpa using subexponential_upper_const 1
  | succ n ih =>
    simpa only [pow_succ] using ih.mul hf (hf0.mono (fun _ h => pow_nonneg h n))

theorem HasSubexponentialUpperBound.add {f g : ℝ → ℝ}
    (hf : HasSubexponentialUpperBound f) (hg : HasSubexponentialUpperBound g) :
    HasSubexponentialUpperBound (fun r => f r + g r) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by positivity), hg (ε / 2) (by positivity),
    subexponential_upper_const 2 (ε / 2) (by positivity)] with r hr hs htwo
  have he : Real.exp (ε * r) = Real.exp (ε / 2 * r) * Real.exp (ε / 2 * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  nlinarith [Real.exp_pos (ε / 2 * r)]

end PolycyclicRecognition

end OAI
