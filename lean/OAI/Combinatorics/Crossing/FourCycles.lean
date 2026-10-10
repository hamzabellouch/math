import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

noncomputable section
namespace Zarankiewicz
open SimpleGraph
open scoped BigOperators

abbrev completeBipartite (m n : ℕ) := completeBipartiteGraph (Fin m) (Fin n)

def orientedEdgeStep {m n : ℕ} (u v : Fin m ⊕ Fin n) : Fin m × Fin n → ℝ :=
  match u,v with
  | .inl i, .inr p => Pi.single (i,p) 1
  | .inr p, .inl i => -Pi.single (i,p) 1
  | _, _ => 0

def walkEdgeChain {m n : ℕ} {u v : Fin m ⊕ Fin n} :
    (completeBipartite m n).Walk u v → (Fin m × Fin n → ℝ)
  | .nil => 0
  | @Walk.cons _ _ _ w _ _ rest => orientedEdgeStep u w + walkEdgeChain rest

def fourCycleWalk {m n : ℕ} (i i₀ : Fin m) (p p₀ : Fin n) :
    (completeBipartite m n).Walk (.inl i) (.inl i) :=
  .cons (v := .inr p) (by simp [completeBipartite, completeBipartiteGraph])
    (.cons (v := .inl i₀) (by simp [completeBipartite, completeBipartiteGraph])
      (.cons (v := .inr p₀) (by simp [completeBipartite, completeBipartiteGraph])
        (.cons (v := .inl i) (by simp [completeBipartite, completeBipartiteGraph]) .nil)))

theorem fourCycleWalk_isCycle {m n : ℕ} (i i₀ : Fin m) (p p₀ : Fin n)
    (hi : i ≠ i₀) (hp : p ≠ p₀) : (fourCycleWalk i i₀ p p₀).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · apply Walk.IsPath.mk'
    change ([Sum.inr p, Sum.inl i₀, Sum.inr p₀, Sum.inl i] : List (Fin m ⊕ Fin n)).Nodup
    simp [hp, hi.symm]
  · change 3 ≤ (4 : ℕ)
    decide

theorem fourCycleWalk_chain {m n : ℕ} (i i₀ : Fin m) (p p₀ : Fin n) :
    walkEdgeChain (fourCycleWalk i i₀ p p₀) =
      Pi.single (i,p) 1 - Pi.single (i₀,p) 1 + Pi.single (i₀,p₀) 1 - Pi.single (i,p₀) 1 := by
  simp [fourCycleWalk, walkEdgeChain, orientedEdgeStep, sub_eq_add_neg, add_assoc]

end Zarankiewicz

end

end OAI
