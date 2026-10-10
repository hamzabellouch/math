import OAI.NumberTheory.JointDickman.Amplification.LatentEdgeSquareBound
import OAI.NumberTheory.JointDickman.Probability.CandidateSiteMean

namespace OAI

/-! # Symmetry and lag support of the integrated edge square -/

namespace JointDickman
open Finset Classical

theorem candidateSquareMoment_symm (B L T H : ℕ) (τ C : ℝ) {M : ℕ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) :
    candidateSquareMoment B L T H τ C χ i t = candidateSquareMoment B L T H τ C χ t i := by
  unfold candidateSquareMoment
  rw [sum_comm]
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro S _
  rw [candidateSiteKernel_symm]
  ring

theorem candidateSiteKernel_zero_of_short {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (S R : Finset ℕ)
    (hshort : Nat.dist i.val t.val ≤ H) :
    candidateSiteKernel B L T H M τ C χ i t S R = 0 := by
  have hf (i t : Fin M) (hit : i < t) (S R : Finset ℕ)
      (hshort : t.val-i.val ≤ H) : candidateSiteKernel B L T H M τ C χ i t S R = 0 := by
    rw [candidateSiteKernel_factor_sum χ i t hit]
    apply sum_eq_zero
    intro ab hab
    have he := (mem_filter.mp hab).2
    have hlag := he.2.1
    change H < t.val-i.val at hlag
    omega
  rcases lt_trichotomy i t with hit | rfl | hti
  · apply hf i t hit S R
    simpa only [Nat.dist_eq_sub_of_le hit.le] using hshort
  · exact candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _
  · rw [candidateSiteKernel_symm]
    apply hf t i hti R S
    simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hshort

theorem candidateSquareMoment_diag (B L T H : ℕ) (τ C : ℝ) {M : ℕ}
    (χ : BlockCandidateIndex M → ℝ) (i : Fin M) :
    candidateSquareMoment B L T H τ C χ i i = 0 := by
  unfold candidateSquareMoment
  simp only [candidateSiteKernel_diag,zero_pow (by norm_num : 2 ≠ 0),mul_zero,sum_const_zero]

theorem candidateSquareMoment_zero_of_short {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hshort : Nat.dist i.val t.val ≤ H) :
    candidateSquareMoment B L T H τ C χ i t = 0 := by
  unfold candidateSquareMoment
  simp only [candidateSiteKernel_zero_of_short χ i t _ _ hshort,
    zero_pow (by norm_num : 2 ≠ 0),mul_zero,sum_const_zero]

theorem candidateSquareMoment_zero_of_far {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hfar : T ≤ Nat.dist i.val t.val) :
    candidateSquareMoment B L T H τ C χ i t = 0 := by
  unfold candidateSquareMoment
  simp only [candidateSiteKernel_zero_of_far χ i t _ _ hfar,
    zero_pow (by norm_num : 2 ≠ 0),mul_zero,sum_const_zero]

end JointDickman

end OAI
