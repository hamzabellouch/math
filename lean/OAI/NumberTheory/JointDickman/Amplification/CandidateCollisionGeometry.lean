import OAI.NumberTheory.JointDickman.Arithmetic.CandidateExceptionalPrimes
import OAI.NumberTheory.JointDickman.Arithmetic.RequiredPrimeProduct

namespace OAI

/-! # A repeated rational root forces a prescribed third endpoint coefficient -/

namespace JointDickman
open Finset

theorem equal_candidate_roots_denominator {B L T H M : ℕ} {τ C : ℝ}
    {e f : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e)
    (hf : BlockCandidateAdmissible B L T H τ C f)
    (hr : blockCandidateRoot e = blockCandidateRoot f) :
    candidateQuotient e = candidateQuotient f ∧
      (candidateLow f : ℤ) = candidateLow e+
        ((f.1.1.val : ℤ)-e.1.1.val)*candidateQuotient e := by
  have hh := shiftedCandidateRoot_injective he.2.2.2.1 hf.2.2.2.1
    he.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.1 hr
  refine ⟨hh.1,?_⟩
  convert hh.2 using 1; ring

theorem equal_candidate_roots_values {B L T H M : ℕ} {τ C : ℝ}
    {e f : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e)
    (hf : BlockCandidateAdmissible B L T H τ C f)
    (hr : blockCandidateRoot e = blockCandidateRoot f) :
    candidateSiteValue e f.1.1 = candidateLow f ∧
      candidateSiteValue e f.1.2 = candidateHigh f := by
  obtain ⟨hc,hl⟩ := equal_candidate_roots_denominator he hf hr
  refine ⟨hl.symm,?_⟩
  have hrel := hf.2.2.2.2.1
  have horder : f.1.1.val ≤ f.1.2.val := le_of_lt hf.1
  have hcast : (candidateHigh f : ℤ) = candidateLow f+
      ((f.1.2.val : ℤ)-f.1.1.val)*candidateQuotient f := by
    exact_mod_cast hrel
  dsimp [candidateSiteValue]
  rw [hcast,← hc,hl]
  ring

theorem distinct_ordered_pairs_third {M : ℕ} {e f : BlockCandidateIndex M}
    (he : e.1.1 < e.1.2) (hf : f.1.1 < f.1.2) (hp : e.1 ≠ f.1) :
    (f.1.1 ≠ e.1.1 ∧ f.1.1 ≠ e.1.2) ∨ (f.1.2 ≠ e.1.1 ∧ f.1.2 ≠ e.1.2) := by
  by_contra hn
  push Not at hn
  have hvals : e.1.1 = f.1.1 ∧ e.1.2 = f.1.2 := by
    rcases eq_or_ne f.1.1 e.1.1 with hl | hl
    · refine ⟨hl.symm,?_⟩
      by_contra hr
      have hx := hn.2 (by intro hx; rw [hl,hx] at hf; exact lt_irrefl _ hf)
      exact hr hx.symm
    · have hl' := hn.1 hl
      have hr : f.1.2 ≠ e.1.2 := by intro hr; rw [hl',hr] at hf; exact lt_irrefl _ hf
      have hx := hn.2 (by intro hx; rw [hl',hx] at hf; exact lt_asymm he hf)
      exact False.elim (hr hx)
  exact hp (Prod.ext hvals.1 hvals.2)

/-- Any duplicate root at another pair makes a large, prescribed integer
available at an endpoint outside the first pair. -/
theorem coincident_candidate_has_third_coefficient {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} {e f : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C S)
    (hf : f ∈ blockCandidates B L T H M τ C S)
    (hp : e.1 ≠ f.1) (hr : blockCandidateRoot e = blockCandidateRoot f) :
    ∃ s : Fin M, s ≠ e.1.1 ∧ s ≠ e.1.2 ∧
      PrimeProductAvailable (candidateSiteValue e s).natAbs (S s) ∧
      T*candidateQuotient e ≤ (candidateSiteValue e s).natAbs := by
  obtain ⟨hes,hea⟩ := mem_blockCandidates.mp he
  obtain ⟨hfs,hfa⟩ := mem_blockCandidates.mp hf
  have hval := equal_candidate_roots_values hea hfa hr
  have hc := (equal_candidate_roots_denominator hea hfa hr).1
  rcases distinct_ordered_pairs_third hea.1 hfa.1 hp with hs | hs
  · refine ⟨f.1.1,hs.1,hs.2,?_,?_⟩
    · rw [hval.1,Int.natAbs_natCast]
      exact ⟨f.2.1,(mem_endpointSplits.mp hfs.1).1,rfl⟩
    · rw [hval.1,Int.natAbs_natCast,hc]
      exact hfa.2.2.2.2.2.2.2.2.2.2.2.2.1
  · refine ⟨f.1.2,hs.1,hs.2,?_,?_⟩
    · rw [hval.2,Int.natAbs_natCast]
      exact ⟨f.2.2,(mem_endpointSplits.mp hfs.2).1,rfl⟩
    · rw [hval.2,Int.natAbs_natCast,hc]
      exact hfa.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end JointDickman

end OAI
