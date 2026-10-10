import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Vanishing exponential rates are subexponential -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem sequence_subexponential_exp_of_vanishing_rate
    {scale η : ℕ → ℝ} (hscale0 : ∀ n, 0 ≤ scale n)
    (hη : Tendsto η atTop (𝓝 0)) :
    HasSubexponentialUpperBoundSeq scale (fun n => Real.exp (η n * scale n)) := by
  intro ε hε
  filter_upwards [hη.eventually (eventually_lt_nhds hε)] with n hn
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hn.le (hscale0 n))

end PolycyclicRecognition

end OAI
