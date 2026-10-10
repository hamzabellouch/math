import OAI.NumberTheory.Ostmann.Construction.WordTransferFourier
import OAI.NumberTheory.Ostmann.Arithmetic.CommonHistoryPeriod

namespace OAI

/-! # A common residue period derived from the actual branching frequencies -/

namespace Ostmann

open scoped Classical

/-- Only internal frequencies enter the denominators of reconstructed words. -/
def internalFrequencyList : (n : ℕ) → FrequencyTree ℤ n → List ℤ
  | 0, _ => []
  | n + 1, t => t.1 :: (internalFrequencyList n t.2.1 ++ internalFrequencyList n t.2.2)

theorem internalFrequencyList_length (n : ℕ) (t : FrequencyTree ℤ n) :
    (internalFrequencyList n t).length = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [internalFrequencyList, List.length_cons, List.length_append, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem internalFrequencyList_nonzero (n : ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) : ∀ s ∈ internalFrequencyList n t, s ≠ 0 := by
  induction n with
  | zero => simp [internalFrequencyList]
  | succ n ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hn.1
    · rcases List.mem_append.mp hs with hs | hs
      · exact ih _ hn.2.1 _ hs
      · exact ih _ hn.2.2 _ hs

theorem WordTransferTemplate.branching_frequencies_dvd {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (M : ℤ)
    (hfreq : ∀ s ∈ internalFrequencyList n t, s ∣ M)
    (env : σ → HistoryFormula σ)
    (henv : ∀ i s, s ∈ (env i).frequencies → s ∣ M) :
    (∀ z ∈ (template.branching t hn).formulaLeaves env, ∀ s ∈ z.2.frequencies, s ∣ M) ∧
    (∀ F ∈ (template.branching t hn).pivotFormulas env, ∀ s ∈ F.frequencies, s ∣ M) := by
  induction template generalizing env with
  | leaf word =>
    constructor
    · intro z hz
      simp only [branching, BranchingWordHistory.formulaLeaves, List.mem_singleton] at hz
      subst z
      apply HistoryFormula.frequencies_listProduct_dvd
      intro F hF
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
      exact henv i
    · intro F hF
      simp only [branching, BranchingWordHistory.pivotFormulas, List.not_mem_nil] at hF
  | @node n d l r hl hr =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
    have hs : step.s ∣ M := hfreq _ (List.mem_cons_self ..)
    have hhead := HistoryFormula.frequencies_bind_dvd step.formula env M
      (step.formula_frequencies_dvd M hs) henv
    have hu : ∀ i s, s ∈ (BranchingWordHistory.updatedFormulas step env i).frequencies → s ∣ M := by
      intro i s hi
      by_cases he : i = step.target
      · subst i
        exact hhead s (by simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hi)
      · exact henv i s (by simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne he] using hi)
    obtain ⟨hll, hlp⟩ := hl t.2.1 hn.2.1
      (fun s hs => hfreq s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))) _ hu
    obtain ⟨hrl, hrp⟩ := hr t.2.2 hn.2.2
      (fun s hs => hfreq s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))) _ hu
    constructor
    · intro z hz
      change z ∈ (l.branching t.2.1 hn.2.1).formulaLeaves (BranchingWordHistory.updatedFormulas step env) ++
        ((r.branching t.2.2 hn.2.2).formulaLeaves (BranchingWordHistory.updatedFormulas step env)).map
          BranchingWordHistory.flipSigned at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hll z hz
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        exact hrl w hw
    · intro F hF
      change F ∈ step.formula.bind env ::
        ((l.branching t.2.1 hn.2.1).pivotFormulas (BranchingWordHistory.updatedFormulas step env) ++
          (r.branching t.2.2 hn.2.2).pivotFormulas (BranchingWordHistory.updatedFormulas step env)) at hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hhead
      · rcases List.mem_append.mp hF with hF | hF
        · exact hlp F hF
        · exact hrp F hF

/-- This is the actual small-frequency modulus, not a new periodicity assumption. -/
theorem WordTransferTemplate.branching_denominator_period {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) (s : ℤ)
    (hs : s ∣ (historyFrequencyBase (internalFrequencyList n t) : ℤ)) :
    (∀ z ∈ (template.branching t hn).formulaLeaves .prime,
      z.2.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ)) ∧
    (∀ F ∈ (template.branching t hn).pivotFormulas .prime,
      F.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ)) := by
  have hfreq := template.branching_frequencies_dvd t hn
    (historyFrequencyBase (internalFrequencyList n t) : ℤ)
    (fun s hs => frequency_dvd_historyFrequencyBase _ s hs) .prime
    (by intro i s hs; simp only [HistoryFormula.frequencies, List.not_mem_nil] at hs)
  have hcost := template.branching_formula_cost t hn B 1 hB (by omega) hwords .prime (fun _ => le_rfl)
  have hperiod (F : HistoryFormula σ) (hf : ∀ d ∈ F.frequencies,
      d ∣ (historyFrequencyBase (internalFrequencyList n t) : ℤ))
      (hc : F.cost ≤ B ^ (n + 1)) :
      F.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) := by
    simp only [historyFrequencyPeriod, Nat.cast_pow]
    exact (F.denominator_test_period _ s hf hs).trans
      (pow_dvd_pow _ (Nat.add_le_add_right (F.frequency_count_le_cost.trans hc) 1))
  constructor
  · intro z hz
    exact hperiod z.2 (hfreq.1 z hz) (by simpa only [Nat.one_mul] using hcost.1 z hz)
  · intro F hF
    exact hperiod F (hfreq.2 F hF) (by simpa only [Nat.one_mul] using hcost.2 F hF)

end Ostmann

end OAI
