import OAI.NumberTheory.Ostmann.Construction.FixedPivotFullPair

namespace OAI

/-! # Embedding the retained graph while the pivot has only a constant coordinate -/

namespace Ostmann

open scoped BigOperators Classical

def fixedPivotGraph {V : Type*} (g : V → V → ℤ) : Option V → Option V → ℤ
  | some i, some j => g i j
  | _, _ => 0

noncomputable def fixedPivotCharacters {V : Type*}
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) : Option V → ∀ p : ℕ, DirichletCharacter ℂ p
  | none, _ => 1
  | some i, p => χ i p

def fixedPivotUnary {V : Type*} (ν : V → ℕ → ℂ) : Option V → ℕ → ℂ
  | none, _ => 1
  | some i, p => ν i p

theorem fixedPivotUnary_norm {V : Type*} (ν : V → ℕ → ℂ)
    (hν : ∀ i p, ‖ν i p‖ ≤ 1) (i : Option V) (p : ℕ) :
    ‖fixedPivotUnary ν i p‖ ≤ 1 := by
  cases i
  · simp only [fixedPivotUnary, norm_one, le_refl]
  · exact hν _ _

theorem fixedPivotGraph_phase {V : Type*} [Fintype V]
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (g : V → V → ℤ)
    (ν : V → ℕ → ℂ) (M : ℕ) (p : V → ℕ) :
    finiteEdgeWeight (dirichletGraphEdge (fixedPivotCharacters χ) (fixedPivotGraph g))
      (fixedPivotUnary ν) (fixedPivotPrimeValues M p) =
      finiteEdgeWeight (dirichletGraphEdge χ g) ν p := by
  simp only [finiteEdgeWeight, Fintype.prod_option, fixedPivotUnary, fixedPivotGraph,
    fixedPivotCharacters, dirichletGraphEdge, fixedPivotPrimeValues,
    zpow_zero, one_mul, mul_one, Finset.prod_const_one]
  congr 1

end Ostmann

end OAI
