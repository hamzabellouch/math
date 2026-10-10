import OAI.NumberTheory.JointDickman.Amplification.CandidateFiniteCutoff
import OAI.NumberTheory.JointDickman.Amplification.CandidatePairSum

namespace OAI

/-! # The original finite graph and its arithmetic candidate matrix -/

namespace JointDickman
open Finset Classical

theorem candidateMatrix_forward {M : ℕ} (I : Finset (BlockCandidateIndex M))
    (hI : ∀ e ∈ I, e.1.1 < e.1.2) (w : BlockCandidateIndex M → ℝ)
    (i k : Fin M) (hik : i < k) :
    candidateMatrix (fun e : I => e.val.1.1) (fun e : I => e.val.1.2)
      (fun e => w e.val) i k = ∑ e ∈ I, if e.1 = (i,k) then w e else 0 := by
  unfold candidateMatrix
  change (∑ e : I, (fun e : BlockCandidateIndex M =>
    ((if i = e.1.1 then if k = e.1.2 then w e else 0 else 0)+
      (if i = e.1.2 then if k = e.1.1 then w e else 0 else 0))) e.val) = _
  trans ∑ e ∈ I, ((if i = e.1.1 then if k = e.1.2 then w e else 0 else 0)+
    (if i = e.1.2 then if k = e.1.1 then w e else 0 else 0))
  · exact sum_coe_sort I (fun e : BlockCandidateIndex M =>
      ((if i = e.1.1 then if k = e.1.2 then w e else 0 else 0)+
        (if i = e.1.2 then if k = e.1.1 then w e else 0 else 0)))
  · apply sum_congr rfl
    intro e he
    have hord := hI e he
    have hback : ¬ (i = e.1.2 ∧ k = e.1.1) := by
      rintro ⟨hi,hk⟩
      rw [← hi,← hk] at hord
      exact (not_lt_of_ge hik.le) hord
    have hpair : e.1 = (i,k) ↔ i = e.1.1 ∧ k = e.1.2 := by
      simp only [Prod.ext_iff]
      exact and_congr eq_comm eq_comm
    by_cases hi : i = e.1.1 <;> by_cases hk : k = e.1.2 <;>
      by_cases hi' : i = e.1.2 <;> by_cases hk' : k = e.1.1 <;>
      simp_all only [ite_true,ite_false,add_zero,not_true_eq_false,and_self,
        and_false,false_and,not_false_eq_true]

theorem actualCandidateKernel_pair {B L T H M u : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (hik : i < k) :
    actualCandidateKernel B L T H M τ C χ u i k =
      ∑ e ∈ blockCandidates B L T H M τ C
        (fun l => coefficientPrimeSet B (u+(l.val+1))),
        if e.1 = (i,k) then candidateRootWeight B L τ C
          (fun l => coefficientPrimeSet B (u+(l.val+1))) χ e
          (coefficientPrimeSet B (candidateArithmeticQuotient u e)) else 0 := by
  rw [actualCandidateKernel_explicit]
  exact candidateMatrix_forward
    (blockCandidates B L T H M τ C (fun l => coefficientPrimeSet B (u+(l.val+1))))
    (fun e he => (mem_blockCandidates.mp he).2.1)
    (fun e => candidateRootWeight B L τ C (fun l => coefficientPrimeSet B (u+(l.val+1)))
      χ e (coefficientPrimeSet B (candidateArithmeticQuotient u e))) i k hik

theorem rawArithmeticGraphKernel_finiteCandidate {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    {i k : Fin M} (hik : i < k) (hH : H < k.val-i.val)
    (hsq : ¬ BlockSquareHit B M u) :
    rawArithmeticGraphKernel B L τ C T N ((k.val-i.val : ℕ) : ℤ)
      (u+(i.val+1))/(B : ℝ) =
      actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u i k := by
  rw [rawArithmeticGraphKernel_candidate_sum hB hT hTP hik hH hsq,
    actualCandidateKernel_pair _ i k hik]
  apply sum_congr rfl
  intro e he
  by_cases hp : e.1 = (i,k)
  · have hi : e.1.1 = i := congrArg Prod.fst hp
    simp only [hp,true_and,ite_true]
    have hedge := candidateGraphTriple_edge_iff hTP he (N := N)
    rw [hi] at hedge
    simp only [hedge]
    by_cases hc : candidateQuotient e*(u+(e.1.1.val+1)) < candidateLow e*(N+1)
    · have hci : candidateQuotient e*(u+(i.val+1)) < candidateLow e*(N+1) := by
        simpa only [hi] using hc
      simp only [hci,ite_true]
      unfold arithmeticCandidateWeight candidateRootWeight finiteCandidateCutoff
      simp only [hc,ite_true]
      rfl
    · have hci : ¬ candidateQuotient e*(u+(i.val+1)) < candidateLow e*(N+1) := by
        simpa only [hi] using hc
      simp only [hci,ite_false]
      unfold candidateRootWeight finiteCandidateCutoff
      simp only [hc,ite_false,mul_zero]
  · simp only [hp,false_and,ite_false]

end JointDickman

end OAI
