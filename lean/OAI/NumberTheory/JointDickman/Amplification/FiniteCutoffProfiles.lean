import OAI.NumberTheory.JointDickman.Probability.FiniteArithmeticKernel
import OAI.NumberTheory.JointDickman.Counting.PeriodicProfileMeans

namespace OAI

/-! # Finite interval profiles for the original graph cutoffs -/

namespace JointDickman
open Finset Classical

noncomputable def primeCandidatePool (B M : ℕ) : Finset (BlockCandidateIndex M) :=
  univ ×ˢ ((auxiliaryPrimes B).powerset ×ˢ (auxiliaryPrimes B).powerset)

theorem blockCandidates_subset_primePool {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (hS : ∀ i, S i ⊆ auxiliaryPrimes B) :
    blockCandidates B L T H M τ C S ⊆ primeCandidatePool B M := by
  intro e he
  have hs := (mem_blockCandidates.mp he).1
  exact mem_product.mpr ⟨mem_univ _,mem_product.mpr
    ⟨mem_powerset.mpr ((mem_endpointSplits.mp hs.1).1.trans (hS _)),
      mem_powerset.mpr ((mem_endpointSplits.mp hs.2).1.trans (hS _))⟩⟩

noncomputable def finiteCutProfile (B M N u : ℕ) : primeCandidatePool B M → Bool :=
  fun e => decide (candidateQuotient e.val*(u+(e.val.1.1.val+1)) < candidateLow e.val*(N+1))

noncomputable def profileCandidateCutoff (B T M : ℕ) (s : primeCandidatePool B M → Bool)
    (e : BlockCandidateIndex M) : ℝ :=
  if he : e ∈ primeCandidatePool B M then
    if s ⟨e,he⟩ then candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e else 0
  else 0

theorem profileCandidateCutoff_bounds (B T M : ℕ) (s : primeCandidatePool B M → Bool)
    (e : BlockCandidateIndex M) :
    0 ≤ profileCandidateCutoff B T M s e ∧ profileCandidateCutoff B T M s e ≤ 1 := by
  unfold profileCandidateCutoff
  split_ifs
  · unfold candidateCutoff amplificationOuterWeight amplificationInnerWeight
    have h1 := amplificationBump_bounds (Real.log (candidateQuotient e)/(B : ℝ))
    have h2 := amplificationBump_bounds ((candidateHigh e : ℝ)/(T*candidateQuotient e))
    have h3 := amplificationBump_bounds ((candidateLow e : ℝ)/(T*candidateQuotient e))
    exact ⟨mul_nonneg (mul_nonneg h1.1 h2.1) h3.1,
      (mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 (by norm_num)) h3.2 h3.1
        (by norm_num)).trans_eq (by norm_num)⟩
  all_goals exact ⟨le_rfl,by norm_num⟩

theorem finiteCutProfile_intervals (B M N : ℕ) (u v w : ℕ) (huv : u ≤ v) (hvw : v ≤ w)
    (he : finiteCutProfile B M N u = finiteCutProfile B M N w) :
    finiteCutProfile B M N v = finiteCutProfile B M N u := by
  funext e
  have he' := congrFun he e
  dsimp only [finiteCutProfile] at he' ⊢
  have hlo : candidateQuotient e.val*(u+(e.val.1.1.val+1)) ≤
      candidateQuotient e.val*(v+(e.val.1.1.val+1)) := Nat.mul_le_mul_left _ (Nat.add_le_add_right huv _)
  have hhi : candidateQuotient e.val*(v+(e.val.1.1.val+1)) ≤
      candidateQuotient e.val*(w+(e.val.1.1.val+1)) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hvw _)
  by_cases hu : candidateQuotient e.val*(u+(e.val.1.1.val+1)) < candidateLow e.val*(N+1)
  · have hw : candidateQuotient e.val*(w+(e.val.1.1.val+1)) < candidateLow e.val*(N+1) := by
      have hh : decide (candidateQuotient e.val*(w+(e.val.1.1.val+1)) < candidateLow e.val*(N+1)) = true := by
        simpa only [hu,decide_true] using he'.symm
      exact of_decide_eq_true hh
    simp only [hu,hhi.trans_lt hw,decide_true]
  · have hv : ¬ candidateQuotient e.val*(v+(e.val.1.1.val+1)) < candidateLow e.val*(N+1) :=
      fun h => hu (hlo.trans_lt h)
    simp only [hu,hv,decide_false]

theorem profileCandidateCutoff_finite {B T M N u : ℕ} {e : BlockCandidateIndex M}
    (he : e ∈ primeCandidatePool B M) :
    profileCandidateCutoff B T M (finiteCutProfile B M N u) e = finiteCandidateCutoff B T N u e := by
  simp [profileCandidateCutoff,he,finiteCutProfile,finiteCandidateCutoff]

theorem actualCandidateCutError_congr {B L T H M u : ℕ} {τ C : ℝ}
    {χ ψ : BlockCandidateIndex M → ℝ}
    (hχ : ∀ e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))), χ e = ψ e) :
    actualCandidateCutError B L T H M τ C χ u = actualCandidateCutError B L T H M τ C ψ u := by
  have hroot (e : blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))) (R : Finset ℕ) :
      candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) χ e.val R =
      candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) ψ e.val R := by
    unfold candidateRootWeight
    rw [hχ e.val e.property]
  have hactual : actualCandidateKernel B L T H M τ C χ u =
      actualCandidateKernel B L T H M τ C ψ u := by
    rw [actualCandidateKernel_explicit,actualCandidateKernel_explicit]
    funext i k
    unfold candidateMatrix
    apply sum_congr rfl
    intro e _
    dsimp only
    rw [hroot]
  have hlatent : latentCandidateKernel B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))) χ =
      latentCandidateKernel B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) ψ := by
    funext i k
    unfold latentCandidateKernel candidateMatrix
    apply sum_congr rfl
    intro e _
    have hw : candidateMeanWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) χ e.val =
        candidateMeanWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) ψ e.val := by
      unfold candidateMeanWeight finiteExpectation
      apply sum_congr rfl
      intro R _
      dsimp only
      rw [hroot]
    dsimp only
    rw [hw]
  unfold actualCandidateCutError
  rw [hactual,hlatent]

theorem actualCandidateCutError_finiteProfile (B L T H M N u : ℕ) (τ C : ℝ) :
    actualCandidateCutError B L T H M τ C
      (profileCandidateCutoff B T M (finiteCutProfile B M N u)) u =
    actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u := by
  apply actualCandidateCutError_congr
  intro e he
  exact profileCandidateCutoff_finite (blockCandidates_subset_primePool (fun _ => filter_subset _ _) he)

end JointDickman

end OAI
