import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMergeProperties
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMergeEdges

namespace OAI

/-! Canonical merging preserves exactly the unordered endpoint support.
This includes edges whose merged coefficient is zero. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaUnorderedPair_map {α β : Type*} (f : α → β) {a b c d : α}
    (h : s(a,b) = s(c,d)) : s(f a,f b) = s(f c,f d) := by
  rcases Sym2.eq_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [ha,hb]
  · rw [ha,hb]
    exact Sym2.eq_swap

namespace QuantumListMerge
open MediatorListProgram

theorem ordered_endpointPair (e : Bond) :
    s((ordered e).1,(ordered e).2) = s(e.1,e.2.1) := by
  rcases le_total e.1 e.2.1 with h | h
  · simp only [ordered,min_eq_left h,max_eq_right h]
  · simpa only [ordered,min_eq_right h,max_eq_left h] using
      (Sym2.eq_swap : s(e.2.1,e.1) = s(e.1,e.2.1))

theorem value_edge_source (n : ℕ) (xs : List Bond) {e : Bond}
    (he : e ∈ value n xs) :
    ∃ f ∈ xs, s(e.1,e.2.1) = s(f.1,f.2.1) := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  have hm := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨f,hf,hfp⟩ := List.mem_map.mp hm
  refine ⟨f,hf,?_⟩
  rw [← hfp]
  exact ordered_endpointPair f

theorem value_edge_target {n : ℕ} {xs : List Bond}
    (hb : SourceBondLists.bounded n xs) {f : Bond} (hf : f ∈ xs) :
    ∃ e ∈ value n xs, s(e.1,e.2.1) = s(f.1,f.2.1) := by
  have hp : ordered f ∈ support n xs :=
    (mem_support hb _).mpr (List.mem_map.mpr ⟨f,hf,rfl⟩)
  refine ⟨((ordered f).1,(ordered f).2,weight xs (ordered f)),?_,ordered_endpointPair f⟩
  exact List.mem_map.mpr ⟨ordered f,hp,rfl⟩

theorem value_support {n : ℕ} {xs : List Bond}
    (hb : SourceBondLists.bounded n xs) (p : Sym2 ℕ) :
    (∃ e ∈ value n xs, s(e.1,e.2.1) = p) ↔ ∃ e ∈ xs, s(e.1,e.2.1) = p := by
  constructor
  · rintro ⟨e,he,hp⟩
    obtain ⟨f,hf,hef⟩ := value_edge_source n xs he
    exact ⟨f,hf,hef.symm.trans hp⟩
  · rintro ⟨f,hf,hp⟩
    obtain ⟨e,he,hef⟩ := value_edge_target hb hf
    exact ⟨e,he,hef.trans hp⟩

end QuantumListMerge

namespace QMARationalExchangeGraph

theorem orderedPair_endpointPair (G : QMARationalExchangeGraph) (e : G.Edge) :
    s((G.orderedPair e).1,(G.orderedPair e).2) = s(G.left e,G.right e) := by
  rcases le_total (G.left e) (G.right e) with h | h
  · simp only [orderedPair,min_eq_left h,max_eq_right h]
  · simpa only [orderedPair,min_eq_right h,max_eq_left h] using
      (Sym2.eq_swap : s(G.right e,G.left e) = s(G.left e,G.right e))

theorem merge_unordered_source (G : QMARationalExchangeGraph) (e : G.merge.Edge) :
    ∃ f : G.Edge, s(G.merge.left e,G.merge.right e) = s(G.left f,G.right f) := by
  obtain ⟨f,hf⟩ := G.merge_edge_source e
  exact ⟨f,Sym2.eq_iff.mpr hf⟩

theorem merge_unordered_target (G : QMARationalExchangeGraph) (f : G.Edge) :
    ∃ e : G.merge.Edge, s(G.merge.left e,G.merge.right e) = s(G.left f,G.right f) :=
  ⟨G.edgeClass f,G.orderedPair_endpointPair f⟩

theorem merge_support (G : QMARationalExchangeGraph) (p : Sym2 (Fin G.n)) :
    (∃ e : G.merge.Edge, s(G.merge.left e,G.merge.right e) = p) ↔
      ∃ f : G.Edge, s(G.left f,G.right f) = p := by
  constructor
  · rintro ⟨e,hp⟩
    obtain ⟨f,hef⟩ := G.merge_unordered_source e
    exact ⟨f,hef.symm.trans hp⟩
  · rintro ⟨f,hp⟩
    obtain ⟨e,hef⟩ := G.merge_unordered_target f
    exact ⟨e,hef.trans hp⟩

theorem merge_nat_support (G : QMARationalExchangeGraph) (p : Sym2 ℕ) :
    (∃ e : G.merge.Edge, s((G.merge.left e).val,(G.merge.right e).val) = p) ↔
      ∃ f : G.Edge, s((G.left f).val,(G.right f).val) = p := by
  constructor
  · rintro ⟨e,hp⟩
    obtain ⟨f,hef⟩ := G.merge_unordered_source e
    exact ⟨f,(qmaUnorderedPair_map Fin.val hef).symm.trans hp⟩
  · rintro ⟨f,hp⟩
    obtain ⟨e,hef⟩ := G.merge_unordered_target f
    exact ⟨e,(qmaUnorderedPair_map Fin.val hef).trans hp⟩

variable (G H : QMARationalExchangeGraph) (vertex : Fin G.n ≃ Fin H.n)

theorem merge_support_forward
    (forward : ∀ e : G.Edge, ∃ f : H.Edge,
      s(vertex (G.left e),vertex (G.right e)) = s(H.left f,H.right f))
    (e : G.merge.Edge) :
    ∃ f : H.merge.Edge,
      s(vertex (G.merge.left e),vertex (G.merge.right e)) = s(H.merge.left f,H.merge.right f) := by
  obtain ⟨a,ha⟩ := G.merge_unordered_source e
  obtain ⟨b,hb⟩ := forward a
  obtain ⟨f,hf⟩ := H.merge_unordered_target b
  exact ⟨f,(qmaUnorderedPair_map vertex ha).trans (hb.trans hf.symm)⟩

theorem merge_support_backward
    (backward : ∀ f : H.Edge, ∃ e : G.Edge,
      s(vertex (G.left e),vertex (G.right e)) = s(H.left f,H.right f))
    (f : H.merge.Edge) :
    ∃ e : G.merge.Edge,
      s(vertex (G.merge.left e),vertex (G.merge.right e)) = s(H.merge.left f,H.merge.right f) := by
  obtain ⟨b,hb⟩ := H.merge_unordered_source f
  obtain ⟨a,ha⟩ := backward b
  obtain ⟨e,he⟩ := G.merge_unordered_target a
  exact ⟨e,(qmaUnorderedPair_map vertex he).trans (ha.trans hb.symm)⟩

end QMARationalExchangeGraph

namespace QuantumListGraph
open MediatorListProgram

theorem ofBonds_nat_support (n : ℕ) (xs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1)
    (p : Sym2 ℕ) :
    (∃ i : (ofBonds n xs c hb hn).Edge,
      s(((ofBonds n xs c hb hn).left i).val,((ofBonds n xs c hb hn).right i).val) = p) ↔
      ∃ e ∈ xs, s(e.1,e.2.1) = p := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨xs.get i,List.get_mem xs i,hi⟩
  · rintro ⟨e,he,hp⟩
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
    refine ⟨i,?_⟩
    change s((xs.get i).1,(xs.get i).2.1) = p
    rwa [hi]

theorem mergedTape_nat_support (n : ℕ) (xs : List Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1)
    (p : Sym2 ℕ) :
    (∃ i : (ofBonds n (QuantumListMerge.value n xs) c
      (QuantumListMerge.bounded n xs) (QuantumListMerge.noLoops hn)).Edge,
      s(((ofBonds n (QuantumListMerge.value n xs) c
        (QuantumListMerge.bounded n xs) (QuantumListMerge.noLoops hn)).left i).val,
        ((ofBonds n (QuantumListMerge.value n xs) c
          (QuantumListMerge.bounded n xs) (QuantumListMerge.noLoops hn)).right i).val) = p) ↔
      ∃ e : (ofBonds n xs c hb hn).merge.Edge,
        s((((ofBonds n xs c hb hn).merge).left e).val,
          (((ofBonds n xs c hb hn).merge).right e).val) = p := by
  exact (ofBonds_nat_support n (QuantumListMerge.value n xs) c
    (QuantumListMerge.bounded n xs) (QuantumListMerge.noLoops hn) p).trans
    ((QuantumListMerge.value_support hb p).trans
      ((ofBonds_nat_support n xs c hb hn p).symm.trans
        ((ofBonds n xs c hb hn).merge_nat_support p).symm))

end QuantumListGraph
end ContinuumCoulomb

end

end OAI
