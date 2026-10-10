import OAI.NumberTheory.Ostmann.Arithmetic.OneSidedGraphFactor

namespace OAI

/-! # The genuine character attached to a surviving directed edge -/

namespace Ostmann

open scoped BigOperators

/-- Nonzero powers commute with evaluation also at nonunits. This permits
the same bounded extension convention after large coprimalities are removed. -/
theorem dirichlet_zpow_apply_nonzero {p : ℕ} (χ : DirichletCharacter ℂ p)
    (e : ℤ) (he : e ≠ 0) (x : ZMod p) : (χ ^ e) x = χ x ^ e := by
  cases e with
  | ofNat n =>
    have hn : n ≠ 0 := by intro hn; subst n; exact he rfl
    change (χ ^ (n : ℤ)) x = χ x ^ (n : ℤ)
    simp only [zpow_natCast]
    exact χ.pow_apply' hn x
  | negSucc n =>
    simp only [zpow_negSucc, MulChar.inv_apply_eq_inv',
      χ.pow_apply' (Nat.succ_ne_zero n)]

noncomputable def dirichletGraphEdge {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (b : I → I → ℤ)
    (i j : I) (x y : ℕ) : ℂ := χ i x (y : ZMod x) ^ b i j

theorem dirichletGraphEdge_norm {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (b : I → I → ℤ)
    (i j : I) (x y : ℕ) : ‖dirichletGraphEdge χ b i j x y‖ ≤ 1 :=
  character_zpow_norm_le_one (χ i x) _ _

/-- A zero reverse edge leaves exactly one short-modulus character of the
long prime. All other factors depend on at most one of the two variables. -/
theorem dirichlet_one_sided_graph_factorization {J : Type*} [Fintype J]
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hν : ∀ i x, ‖ν i x‖ ≤ 1)
    (hself : b (.inl true) (.inl true) = 0 ∧ b (.inl false) (.inl false) = 0)
    (hreverse : b (.inl false) (.inl true) = 0)
    (hforward : b (.inl true) (.inl false) ≠ 0) :
    ∃ U V : ℕ → ℂ, (∀ p, ‖U p‖ ≤ 1) ∧ (∀ q, ‖V q‖ ≤ 1) ∧
      ∀ q p, finiteEdgeWeight (dirichletGraphEdge χ b) ν (twoVertexLabels fixed q p) =
        U p * V q * (χ (.inl true) q ^ b (.inl true) (.inl false)) (p : ZMod q) := by
  refine ⟨longGraphFactor (dirichletGraphEdge χ b) ν fixed,
    shortGraphFactor (dirichletGraphEdge χ b) ν fixed,
    longGraphFactor_norm _ ν fixed (dirichletGraphEdge_norm χ b) hν,
    shortGraphFactor_norm _ ν fixed (dirichletGraphEdge_norm χ b) hν, ?_⟩
  intro q p
  rw [one_sided_graph_factorization _ ν fixed q p
    (by simp only [dirichletGraphEdge, hself.1, hself.2, zpow_zero, and_self])
    (by simp only [dirichletGraphEdge, hreverse, zpow_zero])]
  rw [dirichlet_zpow_apply_nonzero _ _ hforward]
  rfl

end Ostmann

end OAI
