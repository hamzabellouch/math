import OAI.NumberTheory.Ostmann.Construction.WordTransferGuardPolynomial

namespace OAI

/-! # Formula costs and frequency denominators of all actual node guards -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.bind_listProduct {σ τ : Type*} (fs : List (HistoryFormula σ))
    (env : σ → HistoryFormula τ) :
    (HistoryFormula.listProduct fs).bind env = HistoryFormula.listProduct (fs.map (fun F => F.bind env)) := by
  induction fs with
  | nil => rfl
  | cons F fs ih => simp only [listProduct, bind, List.map_cons, ih]

theorem wordTransferGuard_pivot {σ : Type*} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) (env : σ → HistoryFormula σ) :
    (wordTransferGuard d s v w hs env).pivot =
      .solve (HistoryFormula.listProduct (d.left.map env))
        (HistoryFormula.listProduct (d.right.map env)) v w s hs := by
  simp only [wordTransferGuard, HistoryPivotStep.formula, wordTransferStep, HistoryFormula.bind,
    HistoryFormula.bind_listProduct, List.map_map, Function.comp_def]

theorem WordTransferTemplate.guards_right_le_pivot {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ∀ g ∈ template.guards t hn env,
      g.rightProduct.cost ≤ g.pivot.cost ∧
      ∀ s ∈ g.rightProduct.frequencies, s ∈ g.pivot.frequencies := by
  induction template generalizing env with
  | leaf word => simp [guards]
  | @node n d l r hl hr =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [wordTransferGuard_pivot]
      constructor
      · change (HistoryFormula.listProduct (d.right.map env)).cost ≤
          (HistoryFormula.listProduct (d.left.map env)).cost +
            (HistoryFormula.listProduct (d.right.map env)).cost + 2
        omega
      · intro s hs
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hs)
    · rcases List.mem_append.mp hg with hg | hg
      · exact hl _ _ _ _ hg
      · exact hr _ _ _ _ hg

theorem WordTransferTemplate.guards_cost {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) :
    ∀ g ∈ template.guards t hn .prime,
      max g.pivot.cost g.rightProduct.cost ≤ B ^ (n + 1) := by
  intro g hg
  have hp : g.pivot ∈ (template.branching t hn).pivotFormulas .prime := by
    rw [← template.guards_pivots]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have hc : g.pivot.cost ≤ B ^ (n + 1) := by
    simpa only [Nat.one_mul] using
      (template.branching_formula_cost t hn B 1 hB (by omega) hwords .prime (fun _ => le_rfl)).2 _ hp
  exact max_le hc ((template.guards_right_le_pivot t hn .prime g hg).1.trans hc)

theorem WordTransferTemplate.guards_denominator_period {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (B : ℕ) (hB : 1 ≤ B)
    (hwords : template.WordsBounded B) (s : ℤ)
    (hs : s ∣ (historyFrequencyBase (internalFrequencyList n t) : ℤ)) :
    ∀ g ∈ template.guards t hn .prime,
      g.pivot.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) ∧
      g.rightProduct.cleared.denominator * s ∣
        (historyFrequencyPeriod (internalFrequencyList n t) (B ^ (n + 1) + 1) : ℤ) := by
  intro g hg
  have hp : g.pivot ∈ (template.branching t hn).pivotFormulas .prime := by
    rw [← template.guards_pivots]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  constructor
  · exact (template.branching_denominator_period t hn B hB hwords s hs).2 _ hp
  · have hfreq := (template.branching_frequencies_dvd t hn
      (historyFrequencyBase (internalFrequencyList n t) : ℤ)
      (fun a ha => frequency_dvd_historyFrequencyBase _ a ha) .prime
      (by intro i a ha; simp only [HistoryFormula.frequencies, List.not_mem_nil] at ha)).2 _ hp
    have hright := (template.guards_right_le_pivot t hn .prime g hg).2
    have hc := (le_max_right g.pivot.cost g.rightProduct.cost).trans
      (template.guards_cost t hn B hB hwords g hg)
    simp only [historyFrequencyPeriod, Nat.cast_pow]
    exact (g.rightProduct.denominator_test_period _ s
      (fun a ha => hfreq a (hright a ha)) hs).trans
        (pow_dvd_pow _ (Nat.add_le_add_right (g.rightProduct.frequency_count_le_cost.trans hc) 1))

end Ostmann

end OAI
