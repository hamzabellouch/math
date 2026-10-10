import OAI.NumberTheory.Ostmann.Construction.MatchedGraphQuotient

namespace OAI

/-! # Full phase quotients have the transported graph difference -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem directedPrimePhase_split {I : Type*} [Fintype I]
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (p : I → ℕ) (hp : ∀ i, p i ≠ 0) (t : ∀ p : ℕ, ZMod p)
    (ν : I → ℕ → ℂ) (b : I → I → ℤ) (v : ℤ) :
    let : ∀ i, NeZero (p i) := fun i => ⟨hp i⟩
    directedPrimePhase p (fun i => χ i (p i)) (fun i => t (p i))
      (fun i => ν i (p i)) b v =
      primeTupleAdditivePhase p hp t v * finiteEdgeWeight (dirichletGraphEdge χ b) ν p := by
  dsimp only
  simp only [directedPrimePhase, primeTupleAdditivePhase, finiteEdgeWeight,
    dirichletGraphEdge, mul_assoc, Finset.prod_mul_distrib]

/-- The matching transports the first graph to the second set of slots.
The translating centers are indexed by actual primes, as in the construction. -/
theorem matched_directed_phase_quotient {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (χ : J → ∀ p : ℕ, DirichletCharacter ℂ p)
    (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (t : ∀ p : ℕ, ZMod p)
    (ν : I → ℕ → ℂ) (ω : J → ℕ → ℂ)
    (b : I → I → ℤ) (c : J → J → ℤ) (v : ℤ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hb : ∀ i, b i i = 0) (hcdiag : ∀ i, c i i = 0) :
    let : ∀ j, NeZero (p j) := fun j => ⟨hp j⟩
    let : ∀ i, NeZero (p (e i)) := fun i => ⟨hp (e i)⟩
    directedPrimePhase (fun i => p (e i)) (fun i => χ (e i) (p (e i)))
        (fun i => t (p (e i))) (fun i => ν i (p (e i))) b v *
      conj (directedPrimePhase p (fun j => χ j (p j)) (fun j => t (p j))
        (fun j => ω j (p j)) c v) =
      finiteEdgeWeight (dirichletGraphEdge χ (graphDifference (transportGraph e b) c))
        (fun j x => ν (e.symm j) x * conj (ω j x)) p := by
  dsimp only
  rw [directedPrimePhase_split (fun i => χ (e i)) (fun i => p (e i))
      (fun i => hp (e i)) t ν b v,
    directedPrimePhase_split χ p hp t ω c v,
    permuted_additive_phase_cancel e p hp t v,
    matched_graph_quotient e χ b c ν ω p hc hb hcdiag]

end Ostmann

end OAI
