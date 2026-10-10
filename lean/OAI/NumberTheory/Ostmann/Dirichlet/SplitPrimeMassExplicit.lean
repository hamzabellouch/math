import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesTailBound
import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesTailRemoved
import OAI.NumberTheory.Ostmann.Dirichlet.SplitPrimeMassBound

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

lemma tailPrimeSeriesTerm_eq (Q sigma : ℝ) :
    tailPrimeSeriesTerm Q sigma = ordinaryPrimeTailTerm sigma Q := by
  funext n
  by_cases hp : n.Prime <;> by_cases hQ : Q < (n : ℝ) <;>
    simp [tailPrimeSeriesTerm, ordinaryPrimeTailTerm, ordinaryPrimeSeriesTerm, hp, hQ]

theorem exists_splitPrimeMass_explicit_lower :
    ∃ K B : ℝ, 0 < K ∧ 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), chi ≠ 1 → chi.IsQuadratic →
      ∀ (M : ℕ), 1 ≤ M → q ∣ M → ∀ Q sigma R : ℝ,
        0 < Q → 1 < sigma → sigma ≤ 2 → 1 ≤ R →
          ((sigma - 1)⁻¹ - K * modulusHeight q 0 - B) / 2 -
            (Real.log R + (Real.log 4 + 4) + Real.log M / R) -
            (Real.log 4 * sigma / (sigma - 1) * Q ^ (1 - sigma)) ≤ splitPrimeMass chi M Q := by
  obtain ⟨K, B, hK, hB, hbound⟩ := exists_splitPrimeMass_lower_with_errors
  refine ⟨K, B, hK, hB, ?_⟩
  intro q _ chi hchi hquad M hM hqM Q sigma R hQ hs hs2 hR
  have h := hbound q chi hchi hquad M hqM Q sigma hQ.le hs hs2
  have hr := tsum_removedPrimeSeries_le M hM hs.le hR
  have ht := ordinaryPrimeTail_le hs hQ
  change (∑' n, removedPrimeSeriesTerm M sigma n) ≤ _ at hr
  change (∑' n, ordinaryPrimeTailTerm sigma Q n) ≤ _ at ht
  rw [← tailPrimeSeriesTerm_eq Q sigma] at ht
  linarith

end Ostmann.Dirichlet

end OAI
