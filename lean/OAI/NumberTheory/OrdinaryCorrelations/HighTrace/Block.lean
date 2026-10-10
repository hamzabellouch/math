import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ForestTraversal
open Classical SimpleGraph
noncomputable section
variable {V : Type*} {G : SimpleGraph V}

abbrev Block (H : SimpleGraph V) := (u : V) × (v : V) × H.Walk u v
namespace Block
abbrev walk {H : SimpleGraph V} (b : Block H) := b.2.2
end Block

def cutCount (H : SimpleGraph V) {u v : V} (p : G.Walk u v) : ℕ :=
  p.edges.countP (fun e => decide (e ∉ H.edgeSet))

lemma cutCount_nil (H : SimpleGraph V) (u : V) : cutCount H (SimpleGraph.Walk.nil : G.Walk u u)=0 := rfl
lemma cutCount_cons (H : SimpleGraph V) {u v z : V} (a : G.Adj u v) (p : G.Walk v z) :
    cutCount H (.cons a p)=cutCount H p+if H.Adj u v then 0 else 1 := by
  simp [cutCount,List.countP_cons]
lemma cutCount_append (H : SimpleGraph V) {u v z : V} (p : G.Walk u v) (q : G.Walk v z) :
    cutCount H (p.append q)=cutCount H p+cutCount H q := by
  simp [cutCount,List.countP_append]

def Covers {H : SimpleGraph V} {u v : V} (p : G.Walk u v) (bs : List (Block H)) : Prop :=
  (∀ z ∈ p.support,∃ b ∈ bs,z ∈ b.walk.support) ∧
  (∀ e ∈ p.edges,e ∈ H.edgeSet → ∃ b ∈ bs,e ∈ b.walk.edges)

theorem cut_cover (H : SimpleGraph V) {u v : V} (p : G.Walk u v) :
    ∃ (z : V) (first : H.Walk u z) (rest : List (Block H)),
      rest.length ≤ cutCount H p ∧
      (∀ b ∈ (⟨u,z,first⟩::rest),b.walk.length ≤ p.length) ∧
      Covers p (⟨u,z,first⟩::rest) := by
  induction p with
  | @nil u =>
    refine ⟨u,.nil,[],by simp [cutCount],?_,?_,?_⟩
    · intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      rfl
    · intro z hz
      have he : z=u := by simpa using hz
      subst z
      exact ⟨⟨u,u,.nil⟩,by simp,by simp⟩
    · simp
  | @cons u v z hadj p ih =>
    obtain ⟨e,first,rest,hlen,hbounds,hvertices,hedges⟩ := ih
    by_cases hh : H.Adj u v
    · let new : H.Walk u e := .cons hh first
      refine ⟨e,new,rest,?_,?_,?_,?_⟩
      · simpa only [cutCount_cons,hh,ite_true,add_zero] using hlen
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · have h := hbounds ⟨v,e,first⟩ (by simp)
          simpa only [Block.walk,new,Walk.length_cons,Nat.succ_le_succ_iff] using h
        · exact (hbounds b (List.mem_cons_of_mem _ hb)).trans (by simp)
      · intro x hx
        rcases List.mem_cons.mp hx with hxu | hx
        · subst x
          exact ⟨⟨u,e,new⟩,by simp,by simp [Block.walk,new]⟩
        · obtain ⟨b,hb,hx⟩ := hvertices x hx
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨⟨u,e,new⟩,by simp,List.mem_cons_of_mem _ hx⟩
          · exact ⟨b,List.mem_cons_of_mem _ hb,hx⟩
      · intro s hs hsg
        rcases List.mem_cons.mp hs with hse | hs
        · subst s
          exact ⟨⟨u,e,new⟩,by simp,by simp [Block.walk,new]⟩
        · obtain ⟨b,hb,hs⟩ := hedges s hs hsg
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨⟨u,e,new⟩,by simp,List.mem_cons_of_mem _ hs⟩
          · exact ⟨b,List.mem_cons_of_mem _ hb,hs⟩
    · refine ⟨u,.nil,⟨v,e,first⟩::rest,?_,?_,?_,?_⟩
      · simp only [List.length_cons,cutCount_cons,hh,ite_false]
        omega
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simp [Block.walk]
        · exact (hbounds b hb).trans (by simp)
      · intro x hx
        rcases List.mem_cons.mp hx with hxu | hx
        · subst x
          exact ⟨⟨u,u,.nil⟩,by simp,by simp⟩
        · obtain ⟨b,hb,hx⟩ := hvertices x hx
          exact ⟨b,List.mem_cons_of_mem _ hb,hx⟩
      · intro s hs hsg
        rcases List.mem_cons.mp hs with hse | hs
        · subst s
          exact (hh (by simpa using hsg)).elim
        · obtain ⟨b,hb,hs⟩ := hedges s hs hsg
          exact ⟨b,List.mem_cons_of_mem _ hb,hs⟩

end
end OrdinaryCorrelations.ForestTraversal

end

end OAI
