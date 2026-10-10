import OAI.Combinatorics.Crossing.CyclicWalkDarts
import OAI.Combinatorics.Crossing.RectangleAlgebra

namespace OAI

noncomputable section
namespace Zarankiewicz
open SimpleGraph
open scoped BigOperators
variable {m n : ℕ} {u v : BipartiteVertex m n}

theorem walkEdgeChain_sum_steps (p : (completeBipartite m n).Walk u v) :
    walkEdgeChain p=∑ i ∈ Finset.range p.length, orientedEdgeStep (p.getVert i) (p.getVert (i+1)) := by
  induction p with
  | nil => simp [walkEdgeChain]
  | @cons u w v h p ih =>
    rw [walkEdgeChain,ih,Walk.length_cons,Finset.sum_range_succ']
    simp only [Walk.getVert_cons_succ,Walk.getVert_zero]
    abel

theorem walkEdgeChain_sum_cyclic_darts (p : (completeBipartite m n).Walk u u) (hp : 0 < p.length) :
    walkEdgeChain p=∑ i ∈ Finset.range p.length,
      bipartiteDartSign (cyclicWalkDart p hp i) • Pi.single (bipartiteDartEdge (cyclicWalkDart p hp i)) 1 := by
  rw [walkEdgeChain_sum_steps]
  apply Finset.sum_congr rfl
  intro i hi
  have hlt := Finset.mem_range.mp hi
  rw [cyclicWalkDart,cyclicIndex_of_lt _ _ _ hlt]
  exact orientedEdgeStep_dart (walkDart p ⟨i,hlt⟩)

theorem edgePairing_sum_left {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (s : Finset α) (z : α → ι → ℝ) (y : ι → ℝ) :
    edgePairing J (∑ a ∈ s, z a) y=∑ a ∈ s, edgePairing J (z a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [edgePairing]
  | @insert a s ha ih => rw [Finset.sum_insert ha,edgePairing_add_left,ih,Finset.sum_insert ha]

theorem edgePairing_sum_right {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (s : Finset α) (z : ι → ℝ) (y : α → ι → ℝ) :
    edgePairing J z (∑ a ∈ s, y a)=∑ a ∈ s, edgePairing J z (y a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [edgePairing]
  | @insert a s ha ih => rw [Finset.sum_insert ha,edgePairing_add_right,ih,Finset.sum_insert ha]

theorem edgePairing_smul_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (e f : ι) (a b : ℝ) :
    edgePairing J (a • Pi.single e 1) (b • Pi.single f 1)=a*b*J e f := by
  simp [edgePairing,Pi.single_apply,mul_comm,mul_left_comm]

theorem edgePairing_walk_dart_sum (J : Matrix (BipartiteEdge m n) (BipartiteEdge m n) ℝ)
    (p : (completeBipartite m n).Walk u u) (q : (completeBipartite m n).Walk v v)
    (hp : 0 < p.length) (hq : 0 < q.length) :
    edgePairing J (walkEdgeChain p) (walkEdgeChain q)=
      ∑ i ∈ Finset.range p.length, ∑ j ∈ Finset.range q.length,
        bipartiteDartSign (cyclicWalkDart p hp i)*bipartiteDartSign (cyclicWalkDart q hq j)*
          J (bipartiteDartEdge (cyclicWalkDart p hp i)) (bipartiteDartEdge (cyclicWalkDart q hq j)) := by
  rw [walkEdgeChain_sum_cyclic_darts p hp,walkEdgeChain_sum_cyclic_darts q hq,edgePairing_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [edgePairing_sum_right]
  apply Finset.sum_congr rfl
  intro j hj
  exact edgePairing_smul_single _ _ _ _ _

end Zarankiewicz

end

end OAI
