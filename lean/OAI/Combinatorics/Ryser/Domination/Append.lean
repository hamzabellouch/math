import OAI.Combinatorics.Ryser.Domination.TraceDefinitions

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [instDecidableEqV : DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

theorem append_exists (t : DominationTrace G pool J root k) (v : V) (Y : Finset V)
    (hne : Y.Nonempty)
    (hdis : ∀ a, a < k → Disjoint Y (t.y a))
    (hreal : ∃ U, IsTransversalOn G pool J U ∧
      (∀ a, a < k → neighborsIn G (t.x a) U = t.y a) ∧ neighborsIn G v U = Y)
    (hmin : ∀ U, IsTransversalOn G pool J U →
      (∀ a, a < k → neighborsIn G (t.x a) U = t.y a) →
      Y.card ≤ (neighborsIn G v U).card)
    (horigin : pool v = root ∨ ∃ b, b < k ∧ ∃ w ∈ t.y b, pool v = pool w) :
    Nonempty (DominationTrace G pool J root (k + 1)) := let _ := instDecidableEqV; by
  classical
  let X : ℕ → V := fun a => if a = k then v else t.x a
  let Z : ℕ → Finset V := fun a => if a = k then Y else t.y a
  have hXnew : X k = v := by simp [X]
  have hZnew : Z k = Y := by simp [Z]
  have hXold (a : ℕ) (ha : a < k) : X a = t.x a := by
    simp only [X, ite_eq_right (Nat.ne_of_lt ha)]
  have hZold (a : ℕ) (ha : a < k) : Z a = t.y a := by
    simp only [Z, ite_eq_right (Nat.ne_of_lt ha)]
  refine ⟨⟨X, Z, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro a ha
    by_cases hak : a = k
    · subst a
      rw [hZnew]
      exact hne
    · have ha' : a < k := by omega
      rw [hZold a ha']
      exact t.nonempty a ha'
  · intro a ha b hb hab
    by_cases hak : a = k
    · subst a
      have hb' : b < k := by omega
      rw [hZnew, hZold b hb']
      exact hdis b hb'
    · have ha' : a < k := by omega
      by_cases hbk : b = k
      · subst b
        rw [hZold a ha', hZnew]
        exact (hdis a ha').symm
      · have hb' : b < k := by omega
        rw [hZold a ha', hZold b hb']
        exact t.disjoint a ha' b hb' hab
  · obtain ⟨U, hU, hprev, hnew⟩ := hreal
    refine ⟨U, hU, ?_⟩
    intro a ha
    by_cases hak : a = k
    · subst a
      rw [hXnew, hZnew]
      exact hnew
    · have ha' : a < k := by omega
      rw [hXold a ha', hZold a ha']
      exact hprev a ha'
  · intro a ha U hU hearlier
    by_cases hak : a = k
    · subst a
      rw [hXnew, hZnew]
      apply hmin U hU
      intro b hb
      have heq := hearlier b hb
      rw [hXold b hb, hZold b hb] at heq
      exact heq
    · have ha' : a < k := by omega
      rw [hXold a ha', hZold a ha']
      apply t.minimal a ha' U hU
      intro b hb
      have hbk : b < k := lt_trans hb ha'
      have heq := hearlier b hb
      rw [hXold b hbk, hZold b hbk] at heq
      exact heq
  · intro a ha
    by_cases hak : a = k
    · subst a
      rw [hXnew]
      rcases horigin with hr | ⟨b, hb, w, hw, hp⟩
      · exact Or.inl hr
      · apply Or.inr
        refine ⟨b, hb, w, ?_, hp⟩
        rw [hZold b hb]
        exact hw
    · have ha' : a < k := by omega
      rw [hXold a ha']
      rcases t.origin a ha' with hr | ⟨b, hb, w, hw, hp⟩
      · exact Or.inl hr
      · apply Or.inr
        refine ⟨b, hb, w, ?_, hp⟩
        rw [hZold b (lt_trans hb ha')]
        exact hw

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
