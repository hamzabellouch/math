import OAI.NumberTheory.Ostmann.Construction.RetainedCharacterPrimeBound
import OAI.NumberTheory.Ostmann.QuadraticSieve.JacobiPrimeSeries

namespace OAI

/-! # The retained prime lower bound for actual signed squarefree kernels -/

namespace Ostmann

open scoped BigOperators Classical

/-- The primitive character is constructed from d. The only remaining
analytic hypotheses are the cited published zero inputs; the Page-retention
condition says precisely which already-selected exception is allowed. -/
theorem retained_signed_kernel_prime_lower (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      ∀ d : ℤ, Squarefree d.natAbs → 2 < d.natAbs →
        ∃ (χ : PrimitiveRealCharacter) (N : ℕ),
          1 < N ∧ N ∣ χ.modulus ∧ χ.modulus ≤ 8 * N ∧
          (d.natAbs = N ∨ d.natAbs = 2 * N) ∧
          χ.modulus ≤ 4 * d.natAbs ∧ d.natAbs ≤ 2 * χ.modulus ∧
          ∀ (Q : ℕ) (R s : ℝ), 2 ≤ Q → 4 * d.natAbs ≤ Q → 0 ≤ R →
            2 * (A + H.errorConstant) ≤ Real.log (4 * (Q : ℝ)) →
            1 < s → s ≤ 1 + 1 / Real.log (4 * (Q : ℝ)) →
            (∀ e : PrimitiveRealZero, selectedPageZero P Q = some e →
              samePrimitiveRealCharacter e χ → (e.modulus : ℝ) ≤ R) →
            Summable (jacobiPrimeTerm d s) ∧
            -2 * zeroComparisonConstant P * Real.log (4 * (Q : ℝ)) -
              K * R ^ ε - H.errorConstant - A - 2 ≤ ∑' n, jacobiPrimeTerm d s n := by
  obtain ⟨A, K, hA, hK, hbound⟩ := retained_character_prime_lower P H hSiegel ε hε
  obtain ⟨C, hC, hseries⟩ := exists_realPrimeSeries_error
  refine ⟨A, K, hA, hK, ?_⟩
  intro d hsf hd
  obtain ⟨χ, N, hN, hNq, hqN, hdN, hqd, hdq, hv⟩ :=
    exists_signed_kernel_character d hsf hd
  refine ⟨χ, N, hN, hNq, hqN, hdN, hqd, hdq, ?_⟩
  intro Q R s hQ hdQ hR hsize hs hss hretain
  have hχ := hbound χ Q R s hQ (hqd.trans hdQ) hR hsize hs hss hretain
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hc := jacobiPrimeSeries_comparison d χ s (by linarith) hv
    (hseries χ.modulus χ.character s hs).1
  refine ⟨hc.1, ?_⟩
  have hdiff := (abs_le.mp hc.2).1
  linarith

end Ostmann

end OAI
