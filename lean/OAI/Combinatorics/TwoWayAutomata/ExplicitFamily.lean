import OAI.Combinatorics.TwoWayAutomata.DeterministicBound

namespace OAI

namespace TwoWayComplementation

/-- An explicit liveness witness and its complementation lower bound. -/
theorem explicit_complementation_family (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      A.language = sourceLanguage (Fin (n - 2)) ∧
      (∀ (Q : Type*) [Fintype Q],
        ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ)) := by
  obtain ⟨A, hA⟩ := sourceLanguage_state_bound (Fin (n - 2))
  have hsize : Fintype.card (Fin (n - 2)) + 2 = n := by simp; omega
  let A' := A.reindex (finCongr hsize)
  have hAlang : A'.language = sourceLanguage (Fin (n - 2)) := by
    rw [TwoNFA.reindex_language, hA]
  refine ⟨A', hAlang, ?_⟩
  intro Q _ B hB
  let B' := B.reindex (Fintype.equivFin Q)
  obtain ⟨τ, l, r, a, b, hzero, hmul, hrecognition⟩ := B'.diagram_representation
  have hbound := diagram_recognition_lower_bound (n - 2) (Fintype.card Q + 1)
    (by omega) (by omega) τ hzero hmul l r a b (by
      intro w
      rw [← hrecognition w, TwoNFA.reindex_language, hB, hAlang]
      rfl)
  have hnat : 2 ^ ((n - 4) / 127) ≤ 2 * (Fintype.card Q + 1) := by
    simpa only [lossBound, Nat.sub_sub, Nat.reduceAdd] using hbound
  have hreal : (2 : ℝ) ^ ((n - 4) / 127) ≤ 2 * ((Fintype.card Q : ℝ) + 1) := by
    exact_mod_cast hnat
  linarith

/-- Both lower bounds hold for the same n-state liveness witness. -/
theorem explicit_family_main (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      A.language = sourceLanguage (Fin (n - 2)) ∧
      (∀ (Q : Type*) [Fintype Q],
        ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ)) ∧
      (131 ≤ n → ∀ (Q : Type*) [Fintype Q],
        ∀ D : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        D.Deterministic → D.language = A.language →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) ≤ (Fintype.card Q : ℝ)) := by
  obtain ⟨A, hA, hcomp⟩ := explicit_complementation_family n hn
  refine ⟨A, hA, hcomp, ?_⟩
  intro hn Q _ D hdet hD
  exact deterministic_liveness_lower_bound n hn Q D hdet (hD.trans hA)

end TwoWayComplementation

end OAI
