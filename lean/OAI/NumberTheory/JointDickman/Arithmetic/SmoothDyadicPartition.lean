import OAI.NumberTheory.JointDickman.Probability.TensorCutoff
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! # A concrete smooth geometric partition of unity -/

namespace JointDickman
open Finset
open scoped SchwartzMap

noncomputable def dyadicPartitionWeight (x : ℝ) : ℝ :=
  Real.smoothTransition (2-x)-Real.smoothTransition (2-2*x)

theorem dyadicPartitionWeight_zero {x : ℝ} (hx : x ≤ 1/2 ∨ 2 < x) :
    dyadicPartitionWeight x = 0 := by
  unfold dyadicPartitionWeight
  rcases hx with h | h
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith),sub_self]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith),sub_self]

theorem dyadicPartitionWeight_bounds (x : ℝ) :
    0 ≤ dyadicPartitionWeight x ∧ dyadicPartitionWeight x ≤ 1 := by
  by_cases hx : x ≤ 1/2
  · rw [dyadicPartitionWeight_zero (Or.inl hx)]
    norm_num
  · have hx0 : 0 ≤ x := by linarith
    unfold dyadicPartitionWeight
    have hm := Real.smoothTransition.monotone (show 2-2*x ≤ 2-x by linarith)
    have h0 := Real.smoothTransition.nonneg (2-2*x)
    have h1 := Real.smoothTransition.le_one (2-x)
    constructor <;> linarith

theorem dyadicPartitionWeight_smooth : ContDiff ℝ (⊤ : ℕ∞) dyadicPartitionWeight := by
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).sub
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem dyadicPartitionWeight_compact : HasCompactSupport dyadicPartitionWeight := by
  apply HasCompactSupport.intro (K := Set.Icc (1/2 : ℝ) 2) isCompact_Icc
  intro x hx
  apply dyadicPartitionWeight_zero
  by_cases h : x ≤ 1/2
  · exact Or.inl h
  · exact Or.inr (lt_of_not_ge (fun h2 => hx ⟨by linarith,h2⟩))

noncomputable def dyadicPartitionSchwartz : 𝓢(ℝ,ℝ) :=
  dyadicPartitionWeight_compact.toSchwartzMap dyadicPartitionWeight_smooth

theorem dyadicPartition_step (z : ℝ) (k : ℕ) :
    dyadicPartitionWeight (z/(2 : ℝ)^(k+1)) =
      Real.smoothTransition (2-z/(2 : ℝ)^(k+1))-
        Real.smoothTransition (2-z/(2 : ℝ)^k) := by
  unfold dyadicPartitionWeight
  have he : 2*(z/(2 : ℝ)^(k+1)) = z/(2 : ℝ)^k := by rw [pow_succ]; field_simp
  rw [he]

theorem dyadicPartition_sum {L U : ℕ} (hLU : L ≤ U) (z : ℝ)
    (hlo : 2 ≤ z/(2 : ℝ)^L) (hhi : z/(2 : ℝ)^U ≤ 1) :
    (∑ k ∈ Ico L U, dyadicPartitionWeight (z/(2 : ℝ)^(k+1))) = 1 := by
  simp_rw [dyadicPartition_step]
  rw [sum_Ico_sub (fun k => Real.smoothTransition (2-z/(2 : ℝ)^k)) hLU]
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

end JointDickman

end OAI
