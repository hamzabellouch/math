import OAI.Combinatorics.ContingencyTables.Transport.LayeredTableNetwork
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # Executed bounded-table feasibility from the cited flow bound

The test runs the concrete residual algorithm on the literal three-layer
network. It handles zero margins, empty row or column types, and structural
zeros. No bounded-table feasibility oracle is assumed.
-/

namespace ContingencyTables.BoundedTableFeasibility

open LayeredTableNetwork
open scoped BigOperators

def vertices (m n : ℕ) : Vertex m n ≃ Fin (2+(m+n)) :=
  (Equiv.sumCongr finTwoEquiv.symm finSumFinEquiv).trans finSumFinEquiv

variable {m n : ℕ}

def networkCapacity (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    PublishedEdmondsKarp.Capacity (2+(m+n)) :=
  fun u v=>capacity r c b ((vertices m n).symm u) ((vertices m n).symm v)

def pull (f : PublishedEdmondsKarp.Flow (2+(m+n))) : Vertex m n → Vertex m n → ℤ :=
  fun u v=>f (vertices m n u) (vertices m n v)

def push (f : Vertex m n → Vertex m n → ℤ) : PublishedEdmondsKarp.Flow (2+(m+n)) :=
  fun u v=>f ((vertices m n).symm u) ((vertices m n).symm v)

lemma source_ne_sink : vertices m n (source : Vertex m n)≠vertices m n sink := by
  intro h
  have he := (vertices m n).injective h
  cases he

lemma capacity_loop (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (u : Fin (2+(m+n))) : networkCapacity r c b u u=0 :=
  capacity_diagonal r c b _

lemma pull_feasible (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (f : PublishedEdmondsKarp.Flow (2+(m+n)))
    (hf : PublishedEdmondsKarp.Feasible (networkCapacity r c b)
      (vertices m n source) (vertices m n sink) f) : Feasible r c b (pull f) := by
  refine ⟨fun u v=>hf.1 _ _,?_,?_⟩
  · intro u v
    simpa only [pull,networkCapacity,Equiv.symm_apply_apply] using hf.2.1
      (vertices m n u) (vertices m n v)
  · intro u hs ht
    have h := hf.2.2 (vertices m n u)
      (fun he=>hs ((vertices m n).injective he))
      (fun he=>ht ((vertices m n).injective he))
    simpa only [pull,(vertices m n).sum_comp] using h

lemma push_feasible (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (f : Vertex m n → Vertex m n → ℤ) (hf : Feasible r c b f) :
    PublishedEdmondsKarp.Feasible (networkCapacity r c b)
      (vertices m n source) (vertices m n sink) (push f) := by
  refine ⟨fun u v=>hf.1 _ _,fun u v=>hf.2.1 _ _,?_⟩
  intro u hs ht
  have h := hf.2.2 ((vertices m n).symm u)
    (fun he=>hs ((vertices m n).symm_apply_eq.mp he))
    (fun he=>ht ((vertices m n).symm_apply_eq.mp he))
  simpa only [push,(vertices m n).symm.sum_comp] using h

lemma pull_value (f : PublishedEdmondsKarp.Flow (2+(m+n))) :
    value (pull f)=PublishedEdmondsKarp.value (vertices m n source) f := by
  exact (vertices m n).sum_comp (fun v=>f (vertices m n source) v)

lemma push_value (f : Vertex m n → Vertex m n → ℤ) :
    PublishedEdmondsKarp.value (vertices m n source) (push f)=value f := by
  simp only [PublishedEdmondsKarp.value,push,Equiv.symm_apply_apply]
  exact (vertices m n).symm.sum_comp (fun v=>f source v)

def computedFlow (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    Vertex m n → Vertex m n → ℤ :=
  pull (EdmondsKarpAlgorithm.maxFlow (networkCapacity r c b)
    (vertices m n source) (vertices m n sink))

def feasibleTest (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) : Bool :=
  decide ((∑ i,r i)=∑ j,c j ∧ value (computedFlow r c b)=∑ i,(r i:ℤ))

theorem computedFlow_feasible (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    Feasible r c b (computedFlow r c b) :=
  pull_feasible r c b _ (EdmondsKarpAlgorithm.maxFlow_correct hEK
    (networkCapacity r c b) (capacity_loop r c b) _ _ source_ne_sink).1

theorem feasibleTest_correct (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ) :
    feasibleTest r c b=true ↔ ∃ X,HasMargins X r c ∧ ∀ i j,X i j≤b i j := by
  rw [feasibleTest,decide_eq_true_eq]
  constructor
  · rintro ⟨htotal,hvalue⟩
    exact ⟨decode (computedFlow r c b),decode_boundedTable r c b _
      (computedFlow_feasible hEK r c b) hvalue htotal⟩
  · rintro ⟨X,hm,hb⟩
    refine ⟨totals_equal hm,?_⟩
    have hmax := EdmondsKarpAlgorithm.maxFlow_correct hEK
      (networkCapacity r c b) (capacity_loop r c b)
      (vertices m n source) (vertices m n sink) source_ne_sink
    have hle := hmax.2 (push (tableFlow r c X))
      (push_feasible r c b _ (tableFlow_feasible r c b X hm hb))
    rw [push_value,tableFlow_value,←pull_value] at hle
    exact le_antisymm (value_le_total r c b _ (computedFlow_feasible hEK r c b)) hle

end ContingencyTables.BoundedTableFeasibility

end OAI
