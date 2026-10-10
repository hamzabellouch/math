import OAI.NumberTheory.Ostmann.Construction.WordUnitReplay

namespace OAI

/-! # A common period for the inherited frequency-unit conditions -/

namespace Ostmann

open scoped Classical

theorem WordRangeDecoration.formulas_frequencies_dvd {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (M : ℤ)
    (hfreq : ∀ s ∈ internalFrequencyList n t, s ∣ M)
    (env : σ → HistoryFormula σ) (henv : ∀ i s, s ∈ (env i).frequencies → s ∣ M) :
    ∀ r ∈ D.formulas template t ht env, ∀ s ∈ r.formula.frequencies, s ∣ M := by
  induction template generalizing env with
  | leaf word =>
    cases D with
    | leaf ranges =>
      intro r hr
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr
      apply HistoryFormula.frequencies_listProduct_dvd
      intro F hF
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
      exact henv i
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
      have hs : step.s ∣ M := hfreq _ (List.mem_cons_self ..)
      have hhead := HistoryFormula.frequencies_bind_dvd step.formula env M
        (step.formula_frequencies_dvd M hs) henv
      have hu : ∀ i s, s ∈ (BranchingWordHistory.updatedFormulas step env i).frequencies → s ∣ M := by
        intro i s hi
        by_cases he : i = step.target
        · subst i
          exact hhead s (by simpa only [BranchingWordHistory.updatedFormulas, Function.update_self] using hi)
        · exact henv i s (by simpa only [BranchingWordHistory.updatedFormulas, Function.update_of_ne he] using hi)
      have hL := ihL L t.2.1 ht.2.1
        (fun s hs => hfreq s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))) _ hu
      have hR := ihR R t.2.2 ht.2.2
        (fun s hs => hfreq s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))) _ hu
      intro q hq
      change q ∈ ranges.map (fun q => q.toHistory env) ++ _ at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hq
        apply HistoryFormula.frequencies_listProduct_dvd
        intro F hF
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
        exact henv i
      · rcases List.mem_append.mp hq with hq | hq
        · exact hL q hq
        · exact hR q hq

theorem WordRangeDecoration.formulas_denominator_period {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hD : D.WordsBounded B) :
    ∀ r ∈ D.formulas template t ht .prime, r.formula.cleared.denominator ∣
      (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) := by
  have hfreq := D.formulas_frequencies_dvd template t ht
    (historyFrequencyBase (internalFrequencyList n t) : ℤ)
    (fun s hs => frequency_dvd_historyFrequencyBase _ s hs) .prime
    (by intro i s hs; simp only [HistoryFormula.frequencies, List.not_mem_nil] at hs)
  intro r hr
  have hc : r.formula.cost ≤ B ^ (n + 1) := by
    simpa only [Nat.one_mul] using D.formulas_cost template t ht .prime B 1 hB le_rfl
      hwords hD (fun _ => le_rfl) r hr
  have hd := r.formula.denominator_test_period
    (historyFrequencyBase (internalFrequencyList n t) : ℤ) 1 (hfreq r hr) (one_dvd _)
  simp only [mul_one] at hd
  simp only [historyFrequencyPeriod, Nat.cast_pow]
  exact hd.trans (pow_dvd_pow _ (Nat.add_le_add_right (r.formula.frequency_count_le_cost.trans hc) 1))

theorem WordRangeDecoration.unitGuards_modulus {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ D.unitGuards template t ht env, ∃ s ∈ allFrequencyList n t, g.modulus = s.natAbs := by
  induction template generalizing env with
  | leaf word =>
    cases D with
    | leaf ranges =>
      intro g hg
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg
      exact ⟨t, List.mem_singleton_self _, rfl⟩
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      intro g hg
      change g ∈ ranges.map (fun q => q.toUnitGuard env t.1) ++ _ at hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg
        exact ⟨t.1, List.mem_cons_self .., rfl⟩
      · rcases List.mem_append.mp hg with hg | hg
        · obtain ⟨s, hs, he⟩ := ihL L _ _ _ g hg
          exact ⟨s, List.mem_cons_of_mem _ (List.mem_append_left _ hs), he⟩
        · obtain ⟨s, hs, he⟩ := ihR R _ _ _ g hg
          exact ⟨s, List.mem_cons_of_mem _ (List.mem_append_right _ hs), he⟩

/-- The extra inherited unit gates use the same explicit modulus as the
node integrality gates; no new periodicity input is assumed. -/
theorem WordRangeDecoration.unitGuards_period {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hD : D.WordsBounded B) :
    ∀ g ∈ D.unitGuards template t ht .prime,
      g.formula.cleared.denominator * (g.modulus : ℤ) ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro g hg
  have hF : g.formula ∈ (D.formulas template t ht .prime).map HistoryRange.formula := by
    rw [← D.unitGuards_formulas]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  obtain ⟨r, hr, he⟩ := List.mem_map.mp hF
  have hd := D.formulas_denominator_period template t ht B hB hwords hD r hr
  rw [he] at hd
  obtain ⟨s, hs, he⟩ := D.unitGuards_modulus template t ht .prime g hg
  have hm : (g.modulus : ℤ) ∣ (historyFrequencyBase (allFrequencyList n t) : ℤ) := by
    rw [he]
    exact Int.natCast_dvd_natCast.mpr (Int.dvd_natCast.mp (frequency_dvd_historyFrequencyBase _ s hs))
  simpa only [wordTransferFullPeriod, Nat.cast_mul] using mul_dvd_mul hd hm

end Ostmann

end OAI
