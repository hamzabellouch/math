import OAI.NumberTheory.Ostmann.Construction.WordTransferFullPeriod

namespace OAI

/-! # Indexed arrays of the actual branching guards and Fourier leaves -/

namespace Ostmann.WordTransferTemplate

open scoped Classical

variable {σ : Type*} {n : ℕ}

noncomputable def guardAt (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n - 1)) : WordTransferGuard σ :=
  (template.guards t hn .prime)[i.val]'(by rw [template.guards_length]; exact i.isLt)

noncomputable def leafAt (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n)) : WeightedWordLeaf σ :=
  (template.weightedLeaves t hn .prime)[i.val]'(by rw [template.weightedLeaves_length]; exact i.isLt)

theorem guardAt_mem (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n - 1)) :
    template.guardAt t hn i ∈ template.guards t hn .prime := List.getElem_mem _

theorem leafAt_mem (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n)) :
    template.leafAt t hn i ∈ template.weightedLeaves t hn .prime := List.getElem_mem _

theorem guardAt_valid_iff (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (x : σ → ℕ) :
    (∀ i, (template.guardAt t hn i).ValidAt (fun j => (x j : ℤ))) ↔
      ValidTransferHistory (wordTransferSystem σ) n (template.state x) t := by
  rw [← template.guards_iff t hn .prime (fun j => (x j : ℤ)) x
    (by intro i; simp only [HistoryFormula.value_prime, Int.cast_natCast])]
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hib : i < 2 ^ n - 1 := by rwa [template.guards_length] at hi
    exact h ⟨i, hib⟩
  · intro h i
    exact h _ (template.guardAt_mem t hn i)

theorem guardAt_cost (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B)
    (i : Fin (2 ^ n - 1)) :
    max (template.guardAt t hn i).pivot.cost (template.guardAt t hn i).rightProduct.cost ≤ B ^ (n + 1) :=
  template.guards_cost t hn B hB hwords _ (template.guardAt_mem t hn i)

theorem leafAt_cost (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B)
    (i : Fin (2 ^ n)) : (template.leafAt t hn i).formula.cost ≤ B ^ (n + 1) :=
  template.weightedLeaves_cost t hn B hB hwords _ (template.leafAt_mem t hn i)

theorem guardAt_denominators_ne_zero (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) :
    ∀ i, wordGuardDenominators (template.guardAt t hn) i ≠ 0 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [wordGuardDenominators, Fin.append_left] using
      (template.guardAt t hn j).pivot.cleared.denominator_ne_zero
  · simpa only [wordGuardDenominators, Fin.append_right] using
      (template.guardAt t hn j).rightProduct.cleared.denominator_ne_zero

theorem guardAt_full_period (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) :
    ∀ i, wordGuardDenominators (template.guardAt t hn) i *
      (wordGuardModuli (template.guardAt t hn) i : ℤ) ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [wordGuardDenominators, wordGuardModuli, Fin.append_left] using
      (template.guards_full_period t hn B hB hwords _ (template.guardAt_mem t hn j)).1
  · simpa only [wordGuardDenominators, wordGuardModuli, Fin.append_right] using
      (template.guards_full_period t hn B hB hwords _ (template.guardAt_mem t hn j)).2

end Ostmann.WordTransferTemplate

end OAI
