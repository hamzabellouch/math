import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WalkVertices

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma exists_treePath_with_support (w : NumericalLine D h ℓ) (hh : 0<h) {E : Finset (Fin ℓ)}
    (hE : E ⊆ w.line.treeSteps) {u v : ℤ} (q : (edgeGraph w.line hh E).Walk u v)
    (hlen : q.length ≤ L) (hu : u ∈ treeVertices w.line) (hne : u≠v) :
    ∃ P : TreePath w L,P.vertex 0=u ∧ P.vertex (Fin.last P.length)=v ∧ (∀ i,P.edge i ∈ E) ∧ (∀ i,P.vertex i ∈ q.bypass.support) := by
  let p := q.bypass
  have hp : p.IsPath := q.bypass_isPath
  have hpL : p.length ≤ L := q.length_bypass_le_length.trans hlen
  have hp0 : 0<p.length := by
    by_contra hn
    exact hne (Walk.eq_of_length_eq_zero (Nat.eq_zero_of_not_pos hn))
  have hedge : ∀ i : Fin p.length,∃ e ∈ E,
      (p.getVert i.val=w.line.offset e.castSucc ∧ p.getVert (i.val+1)=w.line.offset e.succ) ∨
      (p.getVert (i.val+1)=w.line.offset e.castSucc ∧ p.getVert i.val=w.line.offset e.succ) :=
    fun i => p.adj_getVert_succ i.isLt
  choose edge he hor using hedge
  let vf : Fin (p.length+1) → ℤ := fun i => p.getVert i.val
  let forward : Fin p.length → Bool := fun i => decide (p.getVert i.val=w.line.offset (edge i).castSucc)
  have endpoints (i : Fin p.length) : if forward i then
      vf i.castSucc=w.line.offset (edge i).castSucc ∧ vf i.succ=w.line.offset (edge i).succ
      else vf i.castSucc=w.line.offset (edge i).succ ∧ vf i.succ=w.line.offset (edge i).castSucc := by
    dsimp [forward,vf]
    split_ifs with hi
    · have hi' : p.getVert i.val=w.line.offset (edge i).castSucc := of_decide_eq_true hi
      rcases hor i with hor | hrev
      · exact hor
      · exact (w.line.endpoints_ne hh (edge i) (hi'.symm.trans hrev.2)).elim
    · rcases hor i with hor | hrev
      · exact (hi (decide_eq_true hor.1)).elim
      · exact ⟨hrev.2,hrev.1⟩
  let P : TreePath w L := {
    length := p.length
    length_pos := hp0
    length_le := hpL
    vertex := vf
    distinct := by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij
    vertex_mem := by
      intro i
      have hi := walk_vertices w.line hh p hu _ (p.getVert_mem_support i.val)
      obtain ⟨j,_,hjv⟩ := mem_image.mp hi
      exact ⟨j,hjv.symm⟩
    edge := edge
    tree := fun i => hE (he i)
    forward := forward
    endpoints := endpoints }
  exact ⟨P,by simp [P,vf],by simp [P,vf],he,fun i => p.getVert_mem_support i.val⟩

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
