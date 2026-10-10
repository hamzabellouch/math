import OAI.NumberTheory.JointDickman.Amplification.CandidateReverseConditional
import OAI.NumberTheory.JointDickman.Amplification.CandidateForwardMass

namespace OAI

/-! # The latent graph as a kernel of its two endpoint types -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentCandidateKernel_symm (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) :
    latentCandidateKernel B L T H M τ C S χ i k =
      latentCandidateKernel B L T H M τ C S χ k i := by
  unfold latentCandidateKernel candidateMatrix
  apply sum_congr rfl
  intro e _
  dsimp only
  split_ifs <;> simp_all

theorem latentCandidateKernel_diag (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i : Fin M) :
    latentCandidateKernel B L T H M τ C S χ i i = 0 := by
  unfold latentCandidateKernel candidateMatrix
  apply sum_eq_zero
  intro e _
  have hord := (mem_blockCandidates.mp e.property).2.1
  dsimp only
  by_cases hi : i = e.val.1.1 <;> by_cases hk : i = e.val.1.2
  · have hh : e.val.1.1 = e.val.1.2 := hi.symm.trans hk
    rw [hh] at hord
    exact False.elim (lt_irrefl _ hord)
  all_goals simp [hi,hk,ne_of_lt hord,Ne.symm (ne_of_lt hord)]

theorem latentCandidateKernel_nonneg (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (i k : Fin M) :
    0 ≤ latentCandidateKernel B L T H M τ C S χ i k := by
  unfold latentCandidateKernel
  apply candidateMatrix_nonneg
  intro e
  exact candidateMeanWeight_nonneg B L τ C S χ hχ e.val

/-- Other endpoint types have no effect on this entry, even though the
full candidate list depends on the entire configuration. -/
theorem latentCandidateKernel_local {B L T H M : ℕ} {τ C : ℝ}
    (S R : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (i k : Fin M) (hi : S i = R i) (hk : S k = R k) :
    latentCandidateKernel B L T H M τ C S χ i k =
      latentCandidateKernel B L T H M τ C R χ i k := by
  have hf (i k : Fin M) (hik : i < k) (hi : S i = R i) (hk : S k = R k) :
      latentCandidateKernel B L T H M τ C S χ i k =
        latentCandidateKernel B L T H M τ C R χ i k := by
    rw [latentCandidateKernel_pair B L T H τ C S χ i k hik,
      latentCandidateKernel_pair B L T H τ C R χ i k hik]
    simp_rw [candidateMeanWeight_eq]
    rw [hi,hk]
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hf i k hik hi hk
  · rw [latentCandidateKernel_diag,latentCandidateKernel_diag]
  · rw [latentCandidateKernel_symm B L T H M τ C S χ,
      latentCandidateKernel_symm B L T H M τ C R χ]
    exact hf k i hki hk hi

noncomputable def candidateSiteKernel (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (a b : Finset ℕ) : ℝ :=
  latentCandidateKernel B L T H M τ C (Function.update (fun _ => a) k b) χ i k

theorem candidateSiteKernel_realizes (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (S : Fin M → Finset ℕ) (i k : Fin M) :
    candidateSiteKernel B L T H M τ C χ i k (S i) (S k) =
      latentCandidateKernel B L T H M τ C S χ i k := by
  apply latentCandidateKernel_local
  · by_cases h : i = k <;> simp [h]
  · simp

theorem candidateSiteKernel_diag (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i : Fin M) (a b : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i i a b = 0 :=
  latentCandidateKernel_diag _ _ _ _ _ _ _ _ _ _

theorem candidateSiteKernel_nonneg (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (hχ : ∀ e, 0 ≤ χ e)
    (i k : Fin M) (a b : Finset ℕ) :
    0 ≤ candidateSiteKernel B L T H M τ C χ i k a b :=
  latentCandidateKernel_nonneg _ _ _ _ _ _ _ _ _ hχ _ _

theorem candidateSiteKernel_symm (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (a b : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i k a b =
      candidateSiteKernel B L T H M τ C χ k i b a := by
  by_cases h : i = k
  · subst k
    rw [candidateSiteKernel_diag,candidateSiteKernel_diag]
  · unfold candidateSiteKernel
    rw [latentCandidateKernel_symm]
    apply latentCandidateKernel_local <;> simp [h,Ne.symm h]

end JointDickman

end OAI
