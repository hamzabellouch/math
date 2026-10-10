import OAI.NumberTheory.Ostmann.Construction.DirectedPrimePhase

namespace OAI

/-! # Separating a one-sided graph edge from the bounded unary factors -/

namespace Ostmann

open scoped BigOperators

def twoVertexLabels {J : Type*} (fixed : J → ℕ) (q p : ℕ) : Bool ⊕ J → ℕ
  | .inl true => q
  | .inl false => p
  | .inr j => fixed j

noncomputable def finiteEdgeWeight {I : Type*} [Fintype I]
    (E : I → I → ℕ → ℕ → ℂ) (ν : I → ℕ → ℂ) (v : I → ℕ) : ℂ :=
  ∏ i, ν i (v i) * ∏ j, E i j (v i) (v j)

noncomputable def fixedGraphFactor {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ) : ℂ :=
  ∏ i, ν (.inr i) (fixed i) * ∏ j, E (.inr i) (.inr j) (fixed i) (fixed j)

noncomputable def longGraphFactor {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ) (p : ℕ) : ℂ :=
  ν (.inl false) p * (∏ j, E (.inl false) (.inr j) p (fixed j)) *
    ∏ i, E (.inr i) (.inl false) (fixed i) p

noncomputable def shortGraphFactor {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ) (q : ℕ) : ℂ :=
  ν (.inl true) q * (∏ j, E (.inl true) (.inr j) q (fixed j)) *
    (∏ i, E (.inr i) (.inl true) (fixed i) q) * fixedGraphFactor E ν fixed

theorem one_sided_graph_factorization {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ) (q p : ℕ)
    (hself : E (.inl true) (.inl true) q q = 1 ∧ E (.inl false) (.inl false) p p = 1)
    (hreverse : E (.inl false) (.inl true) p q = 1) :
    finiteEdgeWeight E ν (twoVertexLabels fixed q p) =
      longGraphFactor E ν fixed p * shortGraphFactor E ν fixed q * E (.inl true) (.inl false) q p := by
  simp only [finiteEdgeWeight, Fintype.prod_sum_type, Fintype.prod_bool, twoVertexLabels,
    hself.1, hself.2, hreverse, one_mul, mul_one]
  simp only [longGraphFactor, shortGraphFactor, fixedGraphFactor]
  simp only [Finset.prod_mul_distrib]
  ring

private theorem norm_mul_le_one' (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul hx hy (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

private theorem norm_prod_le_one' {I : Type*} [Fintype I] (f : I → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) : ‖∏ i, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hf i)

theorem fixedGraphFactor_norm {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hE : ∀ i j x y, ‖E i j x y‖ ≤ 1) (hν : ∀ i x, ‖ν i x‖ ≤ 1) :
    ‖fixedGraphFactor E ν fixed‖ ≤ 1 := by
  apply norm_prod_le_one'
  intro i
  exact norm_mul_le_one' _ _ (hν _ _) (norm_prod_le_one' _ (fun j => hE _ _ _ _))

theorem longGraphFactor_norm {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hE : ∀ i j x y, ‖E i j x y‖ ≤ 1) (hν : ∀ i x, ‖ν i x‖ ≤ 1) (p : ℕ) :
    ‖longGraphFactor E ν fixed p‖ ≤ 1 := by
  apply norm_mul_le_one'
  · exact norm_mul_le_one' _ _ (hν _ _) (norm_prod_le_one' _ (fun j => hE _ _ _ _))
  · exact norm_prod_le_one' _ (fun i => hE _ _ _ _)

theorem shortGraphFactor_norm {J : Type*} [Fintype J]
    (E : (Bool ⊕ J) → (Bool ⊕ J) → ℕ → ℕ → ℂ)
    (ν : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hE : ∀ i j x y, ‖E i j x y‖ ≤ 1) (hν : ∀ i x, ‖ν i x‖ ≤ 1) (q : ℕ) :
    ‖shortGraphFactor E ν fixed q‖ ≤ 1 := by
  apply norm_mul_le_one'
  · apply norm_mul_le_one'
    · exact norm_mul_le_one' _ _ (hν _ _) (norm_prod_le_one' _ (fun j => hE _ _ _ _))
    · exact norm_prod_le_one' _ (fun i => hE _ _ _ _)
  · exact fixedGraphFactor_norm E ν fixed hE hν

end Ostmann

end OAI
