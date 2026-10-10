import OAI.NumberTheory.Ostmann.Construction.RetainedInvariantCharacter
import OAI.NumberTheory.Ostmann.Construction.DirectedPhaseReindex

namespace OAI

/-! # Exact cancellation at a shared root frequency on all prime coordinates -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem directedPrimePhase_invariant_pair {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, p i ≠ 0) (e : Equiv.Perm I)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ i, χ (e i) = χ i)
    (center : ∀ p : ℕ, ZMod p) (ν ω : I → ℕ → ℂ)
    (b c : I → I → ℤ) (v : ℤ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hb : ∀ i, b i i = 0) (hcdiag : ∀ i, c i i = 0) :
    let : ∀ i, NeZero (p i) := fun i => ⟨hp i⟩
    let : ∀ i, NeZero (p (e i)) := fun i => ⟨hp (e i)⟩
    directedPrimePhase p (fun i => χ i (p i)) (fun i => center (p i))
        (fun i => ν i (p i)) b v *
      conj (directedPrimePhase (fun i => p (e i)) (fun i => χ i (p (e i)))
        (fun i => center (p (e i))) (fun i => ω i (p (e i))) c v) =
      finiteEdgeWeight (dirichletGraphEdge χ (graphDifference b (transportGraph e c)))
        (fun i q => ν i q * conj (ω (e.symm i) q)) p := by
  let : ∀ i, NeZero (p i) := fun i => ⟨hp i⟩
  let : ∀ i, NeZero (p (e i)) := fun i => ⟨hp (e i)⟩
  dsimp only
  rw [directedPrimePhase_split χ p hp center ν b v,
    directedPrimePhase_split χ (fun i => p (e i)) (fun i => hp (e i)) center ω c v]
  rw [primeTupleAdditivePhase_equiv e p hp]
  have hunit : primeTupleAdditivePhase p hp center v *
      conj (primeTupleAdditivePhase p hp center v) = 1 := by
    rw [Complex.mul_conj', primeTupleAdditivePhase_norm]
    norm_num
  rw [map_mul]
  calc
    _ = finiteEdgeWeight (dirichletGraphEdge χ b) ν p *
        conj (finiteEdgeWeight (dirichletGraphEdge χ c) ω (fun i => p (e i))) := by
      calc
        _ = (primeTupleAdditivePhase p hp center v * conj (primeTupleAdditivePhase p hp center v)) *
            (finiteEdgeWeight (dirichletGraphEdge χ b) ν p *
              conj (finiteEdgeWeight (dirichletGraphEdge χ c) ω (fun i => p (e i)))) := by ring
        _ = _ := by rw [hunit, one_mul]
    _ = _ := by
      have he := finiteEdgeWeight_invariant_transport e χ hχ c ω p
      dsimp only [Function.comp_def] at he
      rw [he]
      exact dirichlet_graph_quotient χ b (transportGraph e c) ν (fun i => ω (e.symm i)) p hc hb
        (fun i => hcdiag (e.symm i))

end Ostmann

end OAI
