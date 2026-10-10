import OAI.Probability.SATVariance.ReplacementSharpness

namespace OAI

namespace RandomKSAT

theorem sharpness (k : ℕ) (hk : 3 ≤ k) :
    (∀ γ D A : ℝ, γ < (k : ℝ) / ((k-1 : ℕ) : ℝ) → 0 < D → 0 < A →
      ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ k ≤ u ∧ ∃ S : Finset (Assignment u),
        S.Nonempty ∧ A * (u : ℝ) ^ (-((k-1 : ℕ) : ℝ)) ≤ blockKill u (k-1) S 1 ∧
        D * (blockKill u (k-1) S 1) ^ (-γ) < lifetime u k S) ∧
    (∃ u : ℕ → ℕ, ∃ S : ∀ g, Finset (Assignment (u g)),
      (∀ g, 2 ≤ g → k ≤ u g ∧ (S g).Nonempty) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun g => blockKill (u g) (k-1) (S g) 1 - blockKill (u g) k (S g) g)
        (fun g => ((2 : ℝ)^k)⁻¹ * (g : ℝ)^(-((k-1 : ℕ) : ℝ)))) ∧
    (¬ ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop e (fun g => (g : ℝ)^(-((k-1 : ℕ) : ℝ))) ∧
      ∀ u, k ≤ u → ∀ S : Finset (Assignment u), S.Nonempty → ∀ g, 2 ≤ g →
        blockKill u (k-1) S 1 - e g ≤ blockKill u k S g) := by
  exact ⟨lifetime_sharp k hk, replacement_sharp k hk, no_uniform_littleO_error k hk⟩

end RandomKSAT

end OAI
