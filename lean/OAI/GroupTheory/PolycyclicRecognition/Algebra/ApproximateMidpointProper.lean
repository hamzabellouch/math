import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Properness of locally compact invariant metrics with approximate midpoints -/

namespace PolycyclicRecognition

open Set Metric Filter
open scoped Pointwise Topology

/-- The length-space consequence needed for properness and minimizing segments. -/
def HasApproximateMidpoints (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∀ ε : ℝ, 0 < ε → ∃ z : X,
    dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G]

omit [IsTopologicalGroup G] in
theorem closedBall_subset_mul_of_approximateMidpoints
    (hmid : HasApproximateMidpoints G) {r : ℝ} (hr : 0 < r) :
    closedBall (1 : G) (3 * r / 2) ⊆ closedBall 1 r * closedBall 1 r := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hmid 1 x (r / 8) (by positivity)
  have hx' : dist (1 : G) x ≤ 3 * r / 2 := by
    simpa only [mem_closedBall, dist_comm] using hx
  refine ⟨z, ?_, z⁻¹ * x, ?_, by simp⟩
  · rw [mem_closedBall, dist_comm z 1]
    linarith
  · have heq : dist (z⁻¹ * x) 1 = dist z x := by
      rw [← dist_mul_left z, mul_inv_cancel_left, mul_one, dist_comm]
    rw [mem_closedBall, heq]
    linarith

theorem properSpace_of_approximateMidpoints [LocallyCompactSpace G]
    (hmid : HasApproximateMidpoints G) : ProperSpace G := by
  obtain ⟨r, hr, hcompact⟩ := exists_isCompact_closedBall (1 : G)
  have hc : ∀ n : ℕ, IsCompact (closedBall (1 : G) ((3 / 2 : ℝ) ^ n * r)) := by
    intro n
    induction n with
    | zero => simpa using hcompact
    | succ n ih =>
      apply (ih.mul ih).of_isClosed_subset isClosed_closedBall
      rw [show (3 / 2 : ℝ) ^ (n + 1) * r = 3 * ((3 / 2 : ℝ) ^ n * r) / 2 by
        rw [pow_succ]; ring]
      exact closedBall_subset_mul_of_approximateMidpoints hmid (by positivity)
  apply ProperSpace.of_seq_closedBall
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3 / 2)).atTop_mul_const hr)
  exact Filter.Eventually.of_forall hc

end PolycyclicRecognition

end OAI
