import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructionIntegrality

namespace OAI

/-! # A common small-frequency period for the constructed reconstruction tests -/

namespace Ostmann

open scoped Classical

namespace HistoryFormula

variable {σ τ : Type*}

theorem frequencies_bind_dvd (F : HistoryFormula σ) (env : σ → HistoryFormula τ) (M : ℤ)
    (hF : ∀ d ∈ F.frequencies, d ∣ M)
    (henv : ∀ i d, d ∈ (env i).frequencies → d ∣ M) :
    ∀ d ∈ (F.bind env).frequencies, d ∣ M := by
  induction F with
  | prime i => exact henv i
  | external z => simp only [bind, frequencies, List.not_mem_nil, false_implies, implies_true]
  | product l r hl hr =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hl (fun a ha => hF a (List.mem_append_left _ ha)) d hd
    · exact hr (fun a ha => hF a (List.mem_append_right _ ha)) d hd
  | solve l r v w s hs hl hr =>
    intro d hd
    rcases List.mem_cons.mp hd with hds | hd
    · subst d; exact hF s (by simp [frequencies])
    · rcases List.mem_append.mp hd with hd | hd
      · exact hl (fun a ha => hF a (by simp only [frequencies, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl ha))) d hd
      · exact hr (fun a ha => hF a (by simp only [frequencies, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr ha))) d hd

theorem frequencies_listProduct_dvd (fs : List (HistoryFormula σ)) (M : ℤ)
    (h : ∀ F ∈ fs, ∀ d ∈ F.frequencies, d ∣ M) :
    ∀ d ∈ (listProduct fs).frequencies, d ∣ M := by
  induction fs with
  | nil => simp only [listProduct, frequencies, List.not_mem_nil, false_implies, implies_true]
  | cons F fs ih =>
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h F (by simp) d hd
    · exact ih (fun G hG => h G (by simp [hG])) d hd

theorem replay_frequencies_dvd (steps : List (σ × HistoryFormula σ))
    (env : σ → HistoryFormula σ) (M : ℤ)
    (hsteps : ∀ step ∈ steps, ∀ d ∈ step.2.frequencies, d ∣ M)
    (henv : ∀ i d, d ∈ (env i).frequencies → d ∣ M) (i : σ) :
    ∀ d ∈ (replayFormulas steps env i).frequencies, d ∣ M := by
  induction steps generalizing env with
  | nil => exact henv i
  | cons step rest ih =>
    apply ih _ (fun s hs => hsteps s (by simp [hs]))
    intro j d hd
    by_cases hj : j = step.1
    · subst j
      simp only [Function.update_self] at hd
      exact frequencies_bind_dvd step.2 env M (hsteps step (by simp)) henv d hd
    · simp only [Function.update_of_ne hj] at hd
      exact henv j d hd

end HistoryFormula

theorem HistoryPivotStep.formula_frequencies_dvd {σ : Type*}
    (step : HistoryPivotStep σ) (M : ℤ) (hs : step.s ∣ M) :
    ∀ d ∈ step.formula.frequencies, d ∣ M := by
  intro d hd
  have hprime (l : List σ) : ∀ a ∈ (HistoryFormula.listProduct (l.map .prime)).frequencies, a ∣ M := by
    apply HistoryFormula.frequencies_listProduct_dvd
    intro F hF
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
    simp only [HistoryFormula.frequencies, List.not_mem_nil, false_implies, implies_true]
  rcases List.mem_cons.mp hd with he | hd
  · subst d; exact hs
  · rcases List.mem_append.mp hd with hd | hd
    · exact hprime step.left d hd
    · exact hprime step.right d hd

theorem integerReconstructionFormulas_frequencies_dvd {σ : Type*}
    (steps : List (HistoryPivotStep σ)) (M : ℤ)
    (hsteps : ∀ step ∈ steps, step.s ∣ M) (i : σ) :
    ∀ d ∈ (integerReconstructionFormulas steps i).frequencies, d ∣ M := by
  apply HistoryFormula.replay_frequencies_dvd
  · intro step hstep
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hstep
    exact a.formula_frequencies_dvd M (hsteps a ha)
  · intro _ d hd
    simp only [HistoryFormula.frequencies, List.not_mem_nil] at hd

theorem integerReconstructionFormulas_period {σ : Type*}
    (steps : List (HistoryPivotStep σ)) (M s : ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hsteps : ∀ step ∈ steps, step.s ∣ M)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C)
    (hs : s ∣ M) (i : σ) :
    (integerReconstructionFormulas steps i).cleared.denominator * s ∣ M ^ (C ^ steps.length + 1) := by
  have hc : (integerReconstructionFormulas steps i).cost ≤ C ^ steps.length := by
    have hb := HistoryFormula.reconstructedFormulas_cost
      (steps.map fun step => (step.target, step.formula)) C hC
      (by
        intro step hstep
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hstep
        simpa only [a.formula_cost] using hsize a ha) i
    simpa only [integerReconstructionFormulas, List.length_map] using hb
  have hf := (integerReconstructionFormulas steps i).frequency_count_le_cost
  apply ((integerReconstructionFormulas steps i).denominator_test_period M s
    (integerReconstructionFormulas_frequencies_dvd steps M hsteps i) hs).trans
  exact pow_dvd_pow M (Nat.add_le_add_right (hf.trans hc) 1)

end Ostmann

end OAI
