import OAI.NumberTheory.JointDickman.Amplification.ArithmeticGraphSymmetry
import OAI.NumberTheory.JointDickman.Amplification.FiniteCutoffMean

namespace OAI

/-! # Both orientations of the original finite graph kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def finiteGraphKernel (B L T H M N u : ℕ) (τ C : ℝ) (i k : Fin M) : ℝ :=
  if H < ((k.val : ℤ)-i.val).natAbs then
    rawArithmeticGraphKernel B L τ C T N ((k.val : ℤ)-i.val) (u+(i.val+1))/(B : ℝ)
  else 0

theorem finiteGraphKernel_symm (B L T H M N u : ℕ) (τ C : ℝ) (i k : Fin M) :
    finiteGraphKernel B L T H M N u τ C i k = finiteGraphKernel B L T H M N u τ C k i := by
  have habs : ((i.val : ℤ)-k.val).natAbs = ((k.val : ℤ)-i.val).natAbs := by
    rw [show (i.val : ℤ)-k.val = -((k.val : ℤ)-i.val) by ring,Int.natAbs_neg]
  unfold finiteGraphKernel
  rw [habs]
  split_ifs
  · exact congrArg (fun x : ℝ => x/(B : ℝ)) (rawArithmeticGraphKernel_block_reverse i k).symm
  · rfl

theorem actualCandidateKernel_symm (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) (i k : Fin M) :
    actualCandidateKernel B L T H M τ C χ u i k = actualCandidateKernel B L T H M τ C χ u k i := by
  rw [actualCandidateKernel_explicit]
  unfold candidateMatrix
  apply sum_congr rfl
  intro e _
  dsimp only
  split_ifs <;> simp_all

theorem actualCandidateKernel_diag (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) (i : Fin M) :
    actualCandidateKernel B L T H M τ C χ u i i = 0 := by
  rw [actualCandidateKernel_explicit]
  unfold candidateMatrix
  apply sum_eq_zero
  intro e _
  have hord := (mem_blockCandidates.mp e.property).2.1
  dsimp only
  by_cases hi : i = e.val.1.1 <;> by_cases hk : i = e.val.1.2
  · have hh : e.val.1.1 = e.val.1.2 := hi.symm.trans hk
    rw [hh] at hord
    exact False.elim (lt_irrefl _ hord)
  all_goals simp [hi,hk,ne_of_lt hord,Ne.symm (ne_of_lt hord)]

theorem actualCandidateKernel_short {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) {i k : Fin M}
    (hik : i < k) (hH : k.val-i.val ≤ H) :
    actualCandidateKernel B L T H M τ C χ u i k = 0 := by
  rw [actualCandidateKernel_pair χ i k hik]
  apply sum_eq_zero
  intro e he
  have ha := (mem_blockCandidates.mp he).2
  have hp : e.1 ≠ (i,k) := by
    intro hp
    have heH := ha.2.1
    change H < e.1.2.val-e.1.1.val at heH
    rw [hp] at heH
    dsimp only at heH
    omega
  exact ite_eq_right hp

theorem finiteGraphKernel_eq_candidate {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    (hsq : ¬ BlockSquareHit B M u) :
    finiteGraphKernel B L T H M N u τ C =
      actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u := by
  have hforward (i k : Fin M) (hik : i < k) :
      finiteGraphKernel B L T H M N u τ C i k =
        actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u i k := by
    have hdiff : ((k.val : ℤ)-i.val) = ((k.val-i.val : ℕ) : ℤ) := (Int.ofNat_sub hik.le).symm
    unfold finiteGraphKernel
    rw [hdiff,Int.natAbs_natCast]
    split_ifs with hh
    · exact rawArithmeticGraphKernel_finiteCandidate hB hT hTP hik hh hsq
    · exact (actualCandidateKernel_short _ u hik (Nat.le_of_not_gt hh)).symm
  funext i k
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hforward i k hik
  · simp only [finiteGraphKernel,sub_self,Int.natAbs_zero,not_lt_zero,ite_false,
      actualCandidateKernel_diag]
  · rw [finiteGraphKernel_symm,actualCandidateKernel_symm]
    exact hforward k i hki

theorem finiteGraphKernel_entry_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M N u : ℕ), 0 < T →
      ∀ i k : Fin M, |finiteGraphKernel B L T H M N u τ C i k| ≤ (B : ℝ)^2 := by
  filter_upwards [rawArithmeticGraphKernel_forward_cap hL hτ hτsmall] with B hcap
  intro C T H M N u hT
  have hf (i k : Fin M) (hik : i < k) :
      |finiteGraphKernel B L T H M N u τ C i k| ≤ (B : ℝ)^2 := by
    have hdiff : ((k.val : ℤ)-i.val) = ((k.val-i.val : ℕ) : ℤ) := (Int.ofNat_sub hik.le).symm
    unfold finiteGraphKernel
    split_ifs
    · rw [abs_of_nonneg (div_nonneg (rawArithmeticGraphKernel_nonneg _ _ _ _ _ _ _ _)
        (Nat.cast_nonneg B)),hdiff]
      exact hcap C T M N u hT i k hik
    · simp only [abs_zero]
      positivity
  intro i k
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hf i k hik
  · simp only [finiteGraphKernel,sub_self,Int.natAbs_zero,not_lt_zero,ite_false,abs_zero]
    positivity
  · rw [finiteGraphKernel_symm]
    exact hf k i hki

end JointDickman

end OAI
