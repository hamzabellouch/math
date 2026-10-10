import OAI.Combinatorics.TwoWayAutomata.ExplicitFamily

namespace OAI

namespace TwoWayComplementation

/-- No alphabet-uniform polynomial state bound determinizes all 2NFAs. -/
theorem no_polynomial_determinization :
    ¬ ∃ p : Polynomial ℝ, ∀ n k : ℕ, ∀ A : TwoNFA (Fin k) (Fin n),
      ∃ s : ℕ, ∃ D : TwoNFA (Fin k) (Fin s),
        D.Deterministic ∧ D.language = A.language ∧
          (s : ℝ) ≤ p.eval (n : ℝ) := by
  classical
  rintro ⟨p, hp⟩
  let q : Polynomial ℝ := p.comp (Polynomial.C 127 * Polynomial.X + Polynomial.C 131)
  apply polynomial_not_bound_two_pow q
  intro t
  let n := 127 * t + 131
  obtain ⟨A, _hA, _hcomp, hdet⟩ := explicit_family_main.{0, 0} n (by dsimp [n]; omega)
  let Sigma := SetRel (Fin (n - 2)) (Fin (n - 2))
  let e : Sigma ≃ Fin (Fintype.card Sigma) := Fintype.equivFin Sigma
  obtain ⟨s, D, hDdet, hD, hs⟩ := hp n (Fintype.card Sigma) (A.pullAlphabet e.symm)
  have hrecognizes : (D.pullAlphabet e).language = A.language := by
    ext w
    rw [D.pullAlphabet_language, hD]
    change w.map e ∈ (A.pullAlphabet e.symm).language ↔ w ∈ A.language
    rw [A.pullAlphabet_language]
    simp only [List.map_map, Equiv.symm_comp_self, List.map_id]
  have hbound := hdet (by dsimp [n]; omega) (Fin s) (D.pullAlphabet e)
    (hDdet.pullAlphabet e) hrecognizes
  have hexponent : (n - 4) / 127 = t + 1 := by dsimp [n]; omega
  rw [hexponent, Fintype.card_fin, pow_succ] at hbound
  change (2 : ℝ) ^ t ≤ q.eval (t : ℝ)
  simp only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  have hn : (n : ℝ) = 127 * (t : ℝ) + 131 := by simp [n]
  rw [hn] at hs
  linarith

end TwoWayComplementation

end OAI
