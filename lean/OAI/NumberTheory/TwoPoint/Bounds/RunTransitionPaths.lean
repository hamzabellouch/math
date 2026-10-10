import OAI.NumberTheory.TwoPoint.Bounds.QuotientRunPaths

namespace OAI

/-! Greedy transitions of an actual constant-run sequence give quotient paths. -/

namespace TwoPointCorrelations

open Finset

variable {K α ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

/-- Scan the remaining positions, recording precisely the starts of new runs. -/
def scanRunTransitions (runLabel : ℕ → ι) : ℕ → ℕ → ι → List (ℕ × ι)
  | _, 0, _ => []
  | n, len + 1, previous =>
      if runLabel n = previous then scanRunTransitions runLabel (n + 1) len previous
      else (n, runLabel n) :: scanRunTransitions runLabel (n + 1) len (runLabel n)

/-- Local constant-run geometry suffices for the actual greedy transition list;
no path, run boundaries, or scalar sums are supplied as encoding data. -/
theorem scanRunTransitions_data (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K) (runLabel : ℕ → ι)
    (start finish : ℕ)
    (hlabel : ∀ t ∈ Ico start finish, label t = regularLabel (runLabel t))
    (hline : ∀ t ∈ Ico start finish,
      ∃ c : K, D.mkQ (formalDeparture label coefficient t) = anchor (runLabel t) +
        c • D.mkQ (Pi.basisFun K α (regularLabel (runLabel t))))
    (hnonzero : ∀ a b i, start ≤ a → a < b → b ≤ finish →
      (∀ t ∈ Ico a b, label t = regularLabel i) → (∑ t ∈ Ico a b, coefficient t) ≠ 0)
    (a n len : ℕ) (i : ι) (hsa : start ≤ a) (han : a < n) (hend : n + len ≤ finish)
    (hcurrent : runLabel a = i)
    (hconst : ∀ t ∈ Ico a n, label t = regularLabel i) :
    QuotientRunData D anchor regularLabel label coefficient a i
      (scanRunTransitions runLabel n len i) := by
  induction len generalizing a n i with
  | zero => trivial
  | succ len ih =>
      have hn : n ∈ Ico start finish := mem_Ico.mpr ⟨by omega, by omega⟩
      by_cases heq : runLabel n = i
      · rw [scanRunTransitions, ite_eq_left heq]
        apply ih a (n + 1) i hsa (by omega) (by omega) hcurrent
        intro t ht
        rcases mem_Ico.mp ht with ⟨hat, htn⟩
        by_cases htn' : t < n
        · exact hconst t (mem_Ico.mpr ⟨hat, htn'⟩)
        · have hteq : t = n := by omega
          subst t
          simpa only [heq] using hlabel n hn
      · rw [scanRunTransitions, ite_eq_right heq]
        refine ⟨han.le, hconst, hnonzero a n i hsa han (by omega) hconst,
          Ne.symm heq, hline n hn, ?_⟩
        apply ih n (n + 1) (runLabel n) (by omega) (by omega) (by omega) rfl
        intro t ht
        have hteq : t = n := by have := mem_Ico.mp ht; omega
        subst t
        exact hlabel n hn

/-- Begin immediately after the first position of a nonempty regular segment. -/
theorem regular_segment_run_data (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α)
    (label : ℕ → α) (coefficient : ℕ → K) (runLabel : ℕ → ι)
    (start len : ℕ) (hlen : 0 < len)
    (hlabel : ∀ t ∈ Ico start (start + len), label t = regularLabel (runLabel t))
    (hline : ∀ t ∈ Ico start (start + len),
      ∃ c : K, D.mkQ (formalDeparture label coefficient t) = anchor (runLabel t) +
        c • D.mkQ (Pi.basisFun K α (regularLabel (runLabel t))))
    (hnonzero : ∀ a b i, start ≤ a → a < b → b ≤ start + len →
      (∀ t ∈ Ico a b, label t = regularLabel i) → (∑ t ∈ Ico a b, coefficient t) ≠ 0) :
    QuotientRunData D anchor regularLabel label coefficient start (runLabel start)
      (scanRunTransitions runLabel (start + 1) (len - 1) (runLabel start)) := by
  apply scanRunTransitions_data D anchor regularLabel label coefficient runLabel start
    (start + len) hlabel hline hnonzero start (start + 1) (len - 1) (runLabel start)
    le_rfl (by omega) (by omega) rfl
  intro t ht
  have hteq : t = start := by have := mem_Ico.mp ht; omega
  subst t
  exact hlabel start (mem_Ico.mpr ⟨le_rfl, by omega⟩)

end TwoPointCorrelations

end OAI
