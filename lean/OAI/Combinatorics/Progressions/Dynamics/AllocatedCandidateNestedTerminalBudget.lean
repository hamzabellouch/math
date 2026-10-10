import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateTerminalNextWork

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedCandidateNestedTerminal_polynomial_budget
    (s m Cprimitive : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ) {x : ℝ},
        C ≤ A → s + 1 ≤ innerDepth → 0 ≤ x →
        let seed := candidateNestedForwardSeed A constants innerDepth outer x
        P.eval₂ (Nat.castRingHom ℝ)
          (allocatedCandidateTerminalFullInput s m Cprimitive seed
            (preparedFiniteForwardWork A constants s seed)
            (preparedFiniteForwardCumulative A constants s seed)) ≤
          candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_allocatedCandidateTerminalFullInput_polynomial_next_work s m Cprimitive P
  refine ⟨C, hC, ?_⟩
  intro A constants innerDepth outer x hCA hdepth hx seed
  have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  exact (hbound A constants hCA hseed).trans
    (candidateNestedForwardWork_le_next_seed A constants innerDepth outer (s + 1) hx hdepth)

theorem exists_allocatedCandidateNestedTerminal_budget
    (s m Cprimitive : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ) {x : ℝ},
        C ≤ A → s + 1 ≤ innerDepth → 0 ≤ x →
        let seed := candidateNestedForwardSeed A constants innerDepth outer x
        allocatedCandidateTerminalFullInput s m Cprimitive seed
          (preparedFiniteForwardWork A constants s seed)
          (preparedFiniteForwardCumulative A constants s seed) ≤
          candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  simpa only [Polynomial.eval₂_X] using
    exists_allocatedCandidateNestedTerminal_polynomial_budget s m Cprimitive Polynomial.X

end Erdos3.VectorPolynomial

end

end OAI
