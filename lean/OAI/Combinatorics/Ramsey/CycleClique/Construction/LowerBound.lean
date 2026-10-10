import OAI.Combinatorics.Ramsey.CycleClique.Construction.Definitions
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-!
# The disjoint-clique lower bound

The red graph consists of `a` disjoint complete graphs of order `k`.
A red cycle stays within one block, while an independent set uses at most
one vertex from each block. This is the lower-bound construction in the
proof of Theorem 1 of *Cycle--clique Ramsey numbers*.
-/

namespace CycleClique.Construction
/-- Disjoint red cliques: the first coordinate records the block. -/
def blockGraph (a k : ℕ) : SimpleGraph (Fin a × Fin k) where
  Adj x y := x ≠ y ∧ x.1 = y.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] theorem blockGraph_adj {a k : ℕ} {x y : Fin a × Fin k} :
    (blockGraph a k).Adj x y ↔ x ≠ y ∧ x.1 = y.1 := Iff.rfl

private theorem cycleNext_castSucc {r : ℕ} (i : Fin r) :
    cycleNext i.castSucc = i.succ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)

/-- Every red cycle in the disjoint-clique construction lies in a single block. -/
theorem blockGraph_cycle_bound {a k m : ℕ} (hm : 0 < m)
    (h : HasCycle (blockGraph a k) m) : m ≤ k := by
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hfirst : ∀ i : Fin (r + 1), (f i).1 = (f 0).1 := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hi := (he i.castSucc).2
      rw [cycleNext_castSucc] at hi
      exact hi.symm.trans ih
  have hinj : Function.Injective (fun i => (f i).2) := by
    intro i j hij
    apply hf
    exact Prod.ext ((hfirst i).trans (hfirst j).symm) hij
  simpa using Fintype.card_le_of_injective (fun i => (f i).2) hinj

/-- An independent set uses at most one vertex in every block. -/
theorem blockGraph_independent_bound {a k n : ℕ}
    (h : HasIndependent (blockGraph a k) n) : n ≤ a := by
  obtain ⟨f, hf, he⟩ := h
  have hinj : Function.Injective (fun i => (f i).1) := by
    intro i j hij
    by_contra hne
    exact he i j ⟨fun h => hne (hf h), hij⟩
  simpa using Fintype.card_le_of_injective (fun i => (f i).1) hinj

/-- The lower-bound coloring on a linearly labelled set of `k * a` vertices. -/
theorem blockGraph_not_ramsey {a k m n : ℕ} (hkm : k < m) (han : a < n) :
    ¬ RamseyProperty m n (k * a) := by
  let e : Fin (k * a) ≃ Fin a × Fin k :=
    (finCongr (Nat.mul_comm k a)).trans finProdFinEquiv.symm
  let G : SimpleGraph (Fin (k * a)) := (blockGraph a k).comap e
  intro h
  rcases h G with hc | hi
  · have hc' : HasCycle (blockGraph a k) m :=
      hc.map e e.injective (fun h => h)
    have := blockGraph_cycle_bound (by omega) hc'
    omega
  · have hi' : HasIndependent (blockGraph a k) n :=
      hi.map e e.injective (fun h => h)
    have := blockGraph_independent_bound hi'
    omega

/-- The sharp lower bound in the manuscript's main parameter range. -/
theorem cycle_clique_lower_bound {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    ¬ RamseyProperty m n ((m - 1) * (n - 1)) := by
  exact blockGraph_not_ramsey (by omega) (by omega)

end CycleClique.Construction

end OAI
