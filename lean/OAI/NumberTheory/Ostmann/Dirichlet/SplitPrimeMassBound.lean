import OAI.NumberTheory.Ostmann.Dirichlet.SplitPrimeSeries

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

theorem exists_splitPrimeMass_lower_with_errors :
    ∃ K B : ℝ, 0 < K ∧ 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), chi ≠ 1 → chi.IsQuadratic →
      ∀ (M : ℕ), q ∣ M → ∀ Q sigma : ℝ,
        0 ≤ Q → 1 < sigma → sigma ≤ 2 →
          ((sigma - 1)⁻¹ - K * modulusHeight q 0 - B) / 2 -
            (∑' n, removedPrimeSeriesTerm M sigma n) -
            (∑' n, tailPrimeSeriesTerm Q sigma n) ≤ splitPrimeMass chi M Q := by
  obtain ⟨B, hB, hord⟩ := exists_ordinaryPrimeSeries_lower
  obtain ⟨K, hK, hchar⟩ := exists_realPrimeSeries_lower
  have hE : 0 ≤ Erdos970.Mertens.E₁ := tsum_nonneg Erdos970.Mertens.E₁.summand_nonneg
  refine ⟨K, B + Erdos970.Mertens.E₁, hK, by positivity, ?_⟩
  intro q _ chi hchi hquad M hqM Q sigma hQ hs hs2
  have ho := hord sigma hs hs2
  have hc := hchar q chi hchi sigma hs hs2
  have hsplit := prime_split_tsum_le chi hquad hqM hQ hs
  linarith

end Ostmann.Dirichlet

end OAI
