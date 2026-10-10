import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Rerooting
open Classical Finset SimpleGraph
noncomputable section
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def ConnectedSet (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ x∈A,∀ y∈A,∃ p : G.Walk x y,∀ z∈p.support,z∈A

structure Gate (G : SimpleGraph V) (root : V) (A : Finset V) where
  vertex : V
  mem : vertex∈A
  path : G.Walk root vertex
  simple : path.IsPath
  first : ∀ z∈A,z∈path.support → z=vertex

lemma gate_exists {root z : V} {A : Finset V} (p : G.Walk root z) (hz : z∈A) :
    Nonempty (Gate G root A) := by
  let q := p.toPath
  obtain ⟨x,hx,hxq,hfirst⟩ := q.val.exists_mem_support_forall_mem_support_imp_eq A
    ⟨z,mem_filter.mpr ⟨hz,q.val.end_mem_support⟩⟩
  exact ⟨⟨x,hx,q.val.takeUntil x hxq,q.property.takeUntil hxq,hfirst⟩⟩

omit [DecidableEq V] in
lemma path_append_of_intersection {x y z : V} {p : G.Walk x y} {q : G.Walk y z}
    (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ u∈p.support,u∈q.support → u=y) : (p.append q).IsPath := by
  have hy : y∉q.support.tail := by
    have hh := hq.support_nodup
    rw [←q.cons_tail_support,List.nodup_cons] at hh
    exact hh.1
  rw [Walk.isPath_def,Walk.support_append,List.nodup_append]
  refine ⟨hp.support_nodup,hq.support_nodup.tail,?_⟩
  intro u hup v hvq huv
  subst v
  have he := hi u hup (List.mem_of_mem_tail hvq)
  exact hy (he ▸ hvq)

omit [DecidableEq V] in
lemma paths_eq (hG : G.IsAcyclic) {x y : V} {p q : G.Walk x y}
    (hp : p.IsPath) (hq : q.IsPath) : p=q :=
  congrArg Subtype.val ((hG.subsingleton_path x y).elim ⟨p,hp⟩ ⟨q,hq⟩)

namespace Gate
variable {root : V} {A : Finset V} (g : Gate G root A)

lemma factor (hG : G.IsAcyclic) (hA : ConnectedSet G A) {z : V} (hz : z∈A)
    (p : G.Walk root z) (hp : p.IsPath) :
    ∃ q : G.Walk g.vertex z,q.IsPath ∧ p=g.path.append q ∧ ∀ x∈q.support,x∈A := by
  obtain ⟨q,hq⟩ := hA g.vertex g.mem z hz
  have hqA : ∀ x∈q.toPath.val.support,x∈A := fun x hx => hq x (q.support_toPath_subset_support hx)
  have hs := path_append_of_intersection g.simple q.toPath.property
    (fun x hx hqx => g.first x (hqA x hqx) hx)
  exact ⟨q.toPath.val,q.toPath.property,paths_eq hG hp hs,hqA⟩

lemma on_path (hG : G.IsAcyclic) (hA : ConnectedSet G A) {z : V} (hz : z∈A)
    (p : G.Walk root z) (hp : p.IsPath) : g.vertex∈p.support := by
  obtain ⟨q,hq,he,hAq⟩ := g.factor hG hA hz p hp
  rw [he]
  exact Walk.support_subset_support_append_left _ _ g.path.end_mem_support

lemma support_subset (hG : G.IsAcyclic) (hA : ConnectedSet G A) {z : V} (hz : z∈A)
    (p : G.Walk root z) (hp : p.IsPath) : g.path.support ⊆ p.support := by
  obtain ⟨q,hq,he,hAq⟩ := g.factor hG hA hz p hp
  rw [he]
  exact Walk.support_subset_support_append_left ..
end Gate

def Ancestor {ι : Type*} (root : V) (v : ι → V) (p : ∀ i,G.Walk root (v i)) (i j : ι) : Prop :=
  v i∈(p j).support ∧ v i≠v j

lemma path_support_prefix (hG : G.IsAcyclic) {root x y : V}
    (p : G.Walk root x) (q : G.Walk root y) (hp : p.IsPath) (hq : q.IsPath)
    (hx : x∈q.support) : p.support ⊆ q.support := by
  have he : p=q.takeUntil x hx := paths_eq hG hp (hq.takeUntil hx)
  rw [he]
  exact q.support_takeUntil_subset_support hx

lemma ancestor_trans {ι : Type*} (hG : G.IsAcyclic) (root : V) (v : ι → V)
    (p : ∀ i,G.Walk root (v i)) (hp : ∀ i,(p i).IsPath) :
    ∀ ⦃first middle last : ι⦄, Ancestor root v p first middle →
      Ancestor root v p middle last → Ancestor root v p first last := by
  intro i j k hij hjk
  refine ⟨path_support_prefix hG (p j) (p k) (hp j) (hp k) hjk.1 hij.1,?_⟩
  intro he
  have hji := path_support_prefix hG (p j) (p k) (hp j) (hp k) hjk.1
  have hprefix : p j=(p k).takeUntil (v j) hjk.1 := paths_eq hG (hp j) ((hp k).takeUntil hjk.1)
  have hnot := Walk.endpoint_notMem_support_takeUntil (hp k) hjk.1 hjk.2.symm
  apply hnot
  rw [←hprefix]
  exact he ▸ hij.1

omit [DecidableEq V] in
lemma ancestor_irrefl {ι : Type*} (root : V) (v : ι → V)
    (p : ∀ i,G.Walk root (v i)) : ∀ index, ¬Ancestor root v p index index :=
  fun _ hi => hi.2 rfl

end
end OrdinaryCorrelations.Rerooting

end

end OAI
