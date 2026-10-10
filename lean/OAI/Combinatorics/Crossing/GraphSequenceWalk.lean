import OAI.Combinatorics.Crossing.GraphWalkTrace

namespace OAI

namespace Zarankiewicz

def graphSequenceWalk {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (∀ i, i < k → G.Adj (v i) (v (i+1))) → G.Walk (v 0) (v k)
  | 0, _ => .nil
  | k+1, h => (graphSequenceWalk G v k (fun i hi => h i (by omega))).concat (h k (by omega))

theorem graphSequenceWalk_length {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (h : ∀ i, i < k → G.Adj (v i) (v (i+1))) → (graphSequenceWalk G v k h).length=k
  | 0, _ => rfl
  | k+1, h => by rw [graphSequenceWalk,SimpleGraph.Walk.length_concat,graphSequenceWalk_length]

theorem graphSequenceWalk_getVert {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (h : ∀ i, i < k → G.Adj (v i) (v (i+1))) →
    ∀ i, i ≤ k → (graphSequenceWalk G v k h).getVert i=v i
  | 0, h, i, hi => by
    have he : i=0 := by omega
    subst i
    exact SimpleGraph.Walk.getVert_zero _
  | k+1, h, i, hi => by
    by_cases hik : i ≤ k
    · rw [graphSequenceWalk,SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append',
        graphSequenceWalk_length,ite_eq_left hik]
      exact graphSequenceWalk_getVert G v k _ i hik
    · have he : i=k+1 := by omega
      subst i
      simpa only [graphSequenceWalk_length] using (graphSequenceWalk G v (k+1) h).getVert_length

theorem graphSequenceWalk_isPath {V : Type*} (G : SimpleGraph V) (v : ℕ → V)
    (k : ℕ) (h : ∀ i, i < k → G.Adj (v i) (v (i+1)))
    (hv : Set.InjOn v {i | i ≤ k}) : (graphSequenceWalk G v k h).IsPath := by
  apply (SimpleGraph.Walk.IsPath.getVert_injOn_iff _).mp
  intro i hi j hj he
  rw [graphSequenceWalk_length] at hi hj
  rw [graphSequenceWalk_getVert G v k h i hi,graphSequenceWalk_getVert G v k h j hj] at he
  exact hv hi hj he

end Zarankiewicz

end OAI
