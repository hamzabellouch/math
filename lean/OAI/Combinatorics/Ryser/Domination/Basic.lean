import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Push

namespace OAI

namespace RyserCoveringCounterexample.Selection

structure Graph (V : Type*) where
  Adj : V → V → Prop
  symm : Std.Symm Adj
  loopless : Std.Irrefl Adj

namespace Graph

protected theorem irrefl {V : Type*} {G : Graph V} {v : V} : ¬ G.Adj v v :=
  G.loopless.irrefl v

theorem Adj.symm {V : Type*} {G : Graph V} {v w : V}
    (h : G.Adj v w) : G.Adj w v :=
  G.symm.symm v w h

end Graph

variable {V ι : Type*} [instDecidableEqV : DecidableEq V] [DecidableEq ι]

def IsTransversalOn (G : Graph V) (pool : V → ι)
    (J : Finset ι) (U : Finset V) : Prop :=
  (∀ x ∈ U, ∀ y ∈ U, ¬ G.Adj x y) ∧
    Set.InjOn pool (U : Set V) ∧ U.image pool = J

noncomputable def neighborsIn (G : Graph V) (x : V) (U : Finset V) : Finset V := by
  classical
  exact U.filter (G.Adj x)

@[simp] theorem mem_neighborsIn {G : Graph V} {x y : V} {U : Finset V} :
    y ∈ neighborsIn G x U ↔ y ∈ U ∧ G.Adj x y := let _ := instDecidableEqV; by
  classical
  simp [neighborsIn]

theorem neighborsIn_subset (G : Graph V) (x : V) (U : Finset V) :
    neighborsIn G x U ⊆ U := by
  intro y hy
  exact (mem_neighborsIn.mp hy).1

theorem neighborsIn_eq_empty_iff {G : Graph V} {x : V} {U : Finset V} :
    neighborsIn G x U = ∅ ↔ ∀ y ∈ U, ¬ G.Adj x y := by
  constructor
  · intro h y hy hxy
    have hm : y ∈ neighborsIn G x U := mem_neighborsIn.mpr ⟨hy, hxy⟩
    simp [h] at hm
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact h y (mem_neighborsIn.mp hy).1 (mem_neighborsIn.mp hy).2

def DominatesOn (G : Graph V) (pool : V → ι)
    (I : Finset ι) (T : Finset V) : Prop :=
  ∀ x, pool x ∈ I → x ∉ T → ∃ y ∈ T, G.Adj x y

def DominationCertificate (G : Graph V) (pool : V → ι) : Prop :=
  ∃ I : Finset ι, ∃ T : Finset V,
    I.Nonempty ∧ (∀ x ∈ T, pool x ∈ I) ∧
    T.card ≤ 2 * (I.card - 1) ∧ DominatesOn G pool I T

end RyserCoveringCounterexample.Selection

end OAI
