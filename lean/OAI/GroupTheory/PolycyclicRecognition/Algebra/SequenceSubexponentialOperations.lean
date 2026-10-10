import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Finite algebra of losses along the profile-scale sequence -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {scale : ℕ → ℝ}

theorem sequence_subexponential_lower_const (hs : Tendsto scale atTop atTop)
    {c : ℝ} (hc : 0 < c) : HasSubexponentialLowerBoundSeq scale (fun _ => c) := by
  simpa only [Function.comp_def] using (subexponential_lower_const hc).along_sequence hs

theorem sequence_subexponential_upper_const (hs : Tendsto scale atTop atTop)
    (c : ℝ) : HasSubexponentialUpperBoundSeq scale (fun _ => c) := by
  simpa only [Function.comp_def] using (subexponential_upper_const c).along_sequence hs

theorem HasSubexponentialLowerBoundSeq.pow {f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hs : Tendsto scale atTop atTop) (n : ℕ) :
    HasSubexponentialLowerBoundSeq scale (fun j => f j ^ n) := by
  induction n with
  | zero => simpa using sequence_subexponential_lower_const hs zero_lt_one
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem HasSubexponentialLowerBoundSeq.min {f g : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hg : HasSubexponentialLowerBoundSeq scale g) :
    HasSubexponentialLowerBoundSeq scale (fun n => min (f n) (g n)) := by
  intro ε hε
  filter_upwards [hf ε hε, hg ε hε] with n hn hm
  exact le_min hn hm

theorem HasSubexponentialLowerBoundSeq.inv {f : ℕ → ℝ}
    (hf : HasSubexponentialLowerBoundSeq scale f) :
    HasSubexponentialUpperBoundSeq scale (fun n => (f n)⁻¹) := by
  intro ε hε
  filter_upwards [hf ε hε] with n hn
  calc
    (f n)⁻¹ ≤ (Real.exp (-ε * scale n))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hn
    _ = Real.exp (ε * scale n) := by rw [← Real.exp_neg]; congr 1; ring

theorem HasSubexponentialUpperBoundSeq.mul {f g : ℕ → ℝ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hf0 : ∀ᶠ n in atTop, 0 ≤ f n) :
    HasSubexponentialUpperBoundSeq scale (fun n => f n * g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε), hf0]
    with n hn hm h0
  calc
    f n * g n ≤ f n * Real.exp (ε / 2 * scale n) := mul_le_mul_of_nonneg_left hm h0
    _ ≤ Real.exp (ε / 2 * scale n) * Real.exp (ε / 2 * scale n) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ = Real.exp (ε * scale n) := by rw [← Real.exp_add]; congr 1; ring

theorem HasSubexponentialUpperBoundSeq.pow {f : ℕ → ℝ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hs : Tendsto scale atTop atTop)
    (hf0 : ∀ᶠ n in atTop, 0 ≤ f n) (k : ℕ) :
    HasSubexponentialUpperBoundSeq scale (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using sequence_subexponential_upper_const hs 1
  | succ k ih =>
    simpa only [pow_succ] using ih.mul hf (hf0.mono (fun _ h => pow_nonneg h k))

theorem HasSubexponentialUpperBoundSeq.add {f g : ℕ → ℝ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hg : HasSubexponentialUpperBoundSeq scale g)
    (hs : Tendsto scale atTop atTop) :
    HasSubexponentialUpperBoundSeq scale (fun n => f n + g n) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε),
    sequence_subexponential_upper_const hs 2 (ε / 2) (half_pos hε)] with n hn hm htwo
  have he : Real.exp (ε * scale n) =
      Real.exp (ε / 2 * scale n) * Real.exp (ε / 2 * scale n) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  nlinarith [Real.exp_pos (ε / 2 * scale n)]

end PolycyclicRecognition

end OAI
