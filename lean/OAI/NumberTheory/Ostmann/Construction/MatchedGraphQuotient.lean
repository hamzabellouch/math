import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletGraphFactor
import OAI.NumberTheory.Ostmann.Characters.PermutedAdditiveCancellation

namespace OAI

/-! # The graph quotient under an actual matching of the prime variables -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

def graphDifference {I : Type*} (b c : I → I → ℤ) (i j : I) : ℤ := b i j - c i j

theorem finiteEdgeWeight_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (E : J → J → ℕ → ℕ → ℂ) (ν : J → ℕ → ℂ) (p : J → ℕ) :
    finiteEdgeWeight (fun i j => E (e i) (e j)) (fun i => ν (e i)) (fun i => p (e i)) =
      finiteEdgeWeight E ν p := by
  unfold finiteEdgeWeight
  calc
    _ = ∏ i, ν (e i) (p (e i)) * ∏ j, E (e i) j (p (e i)) (p j) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [e.prod_comp (fun j => E (e i) j (p (e i)) (p j))]
    _ = _ := e.prod_comp (fun i => ν i (p i) * ∏ j, E i j (p i) (p j))

theorem dirichlet_graph_quotient {I : Type*} [Fintype I]
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b c : I → I → ℤ) (ν ω : I → ℕ → ℂ) (p : I → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hb : ∀ i, b i i = 0) (hcdiag : ∀ i, c i i = 0) :
    finiteEdgeWeight (dirichletGraphEdge χ b) ν p *
        conj (finiteEdgeWeight (dirichletGraphEdge χ c) ω p) =
      finiteEdgeWeight (dirichletGraphEdge χ (graphDifference b c))
        (fun i x => ν i x * conj (ω i x)) p := by
  unfold finiteEdgeWeight
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_mul, map_prod]
  rw [show (ν i (p i) * ∏ j, dirichletGraphEdge χ b i j (p i) (p j)) *
      (conj (ω i (p i)) * ∏ j, conj (dirichletGraphEdge χ c i j (p i) (p j))) =
      (ν i (p i) * conj (ω i (p i))) *
        ((∏ j, dirichletGraphEdge χ b i j (p i) (p j)) *
          ∏ j, conj (dirichletGraphEdge χ c i j (p i) (p j))) by ring]
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp only [dirichletGraphEdge, graphDifference, hb, hcdiag, sub_self,
      zpow_zero, map_one, mul_one]
  · have hu : IsUnit (p j : ZMod (p i)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hc hij).symm
    have hn : χ i (p i) (p j : ZMod (p i)) ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr hu
    simp only [dirichletGraphEdge, graphDifference, conjugate_character_power]
    rw [← zpow_add₀ hn, sub_eq_add_neg]

theorem graphQuotientUnary_norm {I : Type*} (ν ω : I → ℕ → ℂ)
    (hν : ∀ i x, ‖ν i x‖ ≤ 1) (hω : ∀ i x, ‖ω i x‖ ≤ 1) (i : I) (x : ℕ) :
    ‖ν i x * conj (ω i x)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj]
  exact (mul_le_mul (hν i x) (hω i x) (norm_nonneg _) (by norm_num)).trans
    (by norm_num)

def transportGraph {I J : Type*} (e : I ≃ J) (b : I → I → ℤ) (i j : J) : ℤ :=
  b (e.symm i) (e.symm j)

theorem matched_graph_quotient {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (χ : J → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : I → I → ℤ) (c : J → J → ℤ)
    (ν : I → ℕ → ℂ) (ω : J → ℕ → ℂ) (p : J → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hb : ∀ i, b i i = 0) (hcdiag : ∀ i, c i i = 0) :
    finiteEdgeWeight (dirichletGraphEdge (fun i => χ (e i)) b) ν (fun i => p (e i)) *
        conj (finiteEdgeWeight (dirichletGraphEdge χ c) ω p) =
      finiteEdgeWeight (dirichletGraphEdge χ (graphDifference (transportGraph e b) c))
        (fun j x => ν (e.symm j) x * conj (ω j x)) p := by
  have he : finiteEdgeWeight (dirichletGraphEdge (fun i => χ (e i)) b) ν
      (fun i => p (e i)) =
      finiteEdgeWeight (dirichletGraphEdge χ (transportGraph e b))
        (fun j => ν (e.symm j)) p := by
    simpa only [finiteEdgeWeight, dirichletGraphEdge, transportGraph,
      Equiv.symm_apply_apply] using
      finiteEdgeWeight_equiv e (dirichletGraphEdge χ (transportGraph e b))
        (fun j => ν (e.symm j)) p
  rw [he]
  exact dirichlet_graph_quotient χ (transportGraph e b) c _ ω p hc
    (fun i => hb (e.symm i)) hcdiag

end Ostmann

end OAI
