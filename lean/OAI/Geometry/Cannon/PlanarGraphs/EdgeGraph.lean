import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonForest
open Set

theorem empty_of_no_leaves {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic)
    (hother : ∀ x y,G.Adj x y → ∃ z,G.Adj x z ∧ z≠y) : G=⊥ := by
  classical
  ext x y
  constructor
  · intro hxy
    let c := G.connectedComponentMk x
    let a : c.supp := ⟨x,rfl⟩
    let b : c.supp := ⟨y,SimpleGraph.ConnectedComponent.sound hxy.reachable.symm⟩
    have hab : a≠b := fun h=>hxy.ne (congrArg Subtype.val h)
    let _ : Nontrivial c.supp := ⟨⟨a,b,hab⟩⟩
    let _ : Fintype c.supp := Fintype.ofFinite c.supp
    obtain ⟨v,hv⟩ := (hG.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
    obtain ⟨w,hw,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    have hval : G.Adj v.val w.val := hw
    obtain ⟨z,hz,hzw⟩ := hother v.val w.val hval
    have hzc : z∈c.supp := c.mem_supp_of_adj_mem_supp v.property hz
    let z' : c.supp := ⟨z,hzc⟩
    have hvz : c.toSimpleGraph.Adj v z' := hz
    exact (hzw (congrArg Subtype.val (hunique _ hvz))).elim
  · exact False.elim
end CannonForest

end
end
section
noncomputable section
namespace CannonGraphGauge
open Set

variable {V E D : Type*} [Fintype E] [Group D]
def edgeGraph (a b : E→V) (hneq:∀i,a i≠b i) (S:Set E) : SimpleGraph V where
  Adj x y := ∃ i∈S,(a i=x ∧ b i=y) ∨ (a i=y ∧ b i=x)
  symm := ⟨by
    rintro x y ⟨i,hi,h|h⟩
    · exact ⟨i,hi,Or.inr h⟩
    · exact ⟨i,hi,Or.inl h⟩⟩
  loopless := ⟨by rintro x ⟨i,hi,h|h⟩ <;> exact hneq i (h.1.trans h.2.symm)⟩

def goodEdges (a b:E→V) (K:E→D) (v:V→D) : Finset E := by
  classical
  exact Finset.univ.filter fun i=>K i*v (a i)=v (b i)
@[simp] lemma mem_goodEdges (a b:E→V) (K:E→D) (v:V→D) (i:E) :
    i∈goodEdges a b K v ↔ K i*v (a i)=v (b i) := by
  classical
  simp [goodEdges]

theorem exists_connected_good (a b:E→V) (hneq:∀i,a i≠b i) (K:E→D)
    (hconn:(edgeGraph a b hneq univ).Preconnected) :
    ∃ v:V→D,(edgeGraph a b hneq (goodEdges a b K v : Set E)).Preconnected := by
  classical
  let S : Finset (Finset E) := Finset.univ.filter fun A=>∃ v:V→D,goodEdges a b K v=A
  have hS : S.Nonempty := ⟨goodEdges a b K (fun _=>1),by simp [S]⟩
  obtain ⟨A,hAS,hmax⟩ := Finset.exists_max_image S Finset.card hS
  obtain ⟨v,rfl⟩ := (Finset.mem_filter.mp hAS).2
  have hmaxv (w:V→D) : (goodEdges a b K w).card≤(goodEdges a b K v).card :=
    hmax _ (by simp [S])
  let H := edgeGraph a b hneq (goodEdges a b K v : Set E)
  have hreach (i:E) : H.Reachable (a i) (b i) := by
    by_contra hn
    let C (x:V) : Prop := H.Reachable (a i) x
    let γ := (K i*v (a i))⁻¹*v (b i)
    let w (x:V) : D := if C x then v x*γ else v x
    have hpres : goodEdges a b K v⊆goodEdges a b K w := by
      intro j hj
      have hadj : H.Adj (a j) (b j) := ⟨j,hj,Or.inl ⟨rfl,rfl⟩⟩
      have hc : C (a j)↔C (b j) :=
        ⟨fun h=>h.trans hadj.reachable,fun h=>h.trans hadj.reachable.symm⟩
      apply (mem_goodEdges ..).mpr
      have he := (mem_goodEdges a b K v j).mp hj
      by_cases ha : C (a j)
      · simp only [w,ite_eq_left ha,ite_eq_left (hc.mp ha),←mul_assoc,he]
      · simp only [w,ite_eq_right ha,ite_eq_right (mt hc.mpr ha),he]
    have hiw : i∈goodEdges a b K w := by
      apply (mem_goodEdges ..).mpr
      have hai : C (a i) := .rfl
      have hbi : ¬C (b i) := hn
      simp [w,hai,hbi,γ,←mul_assoc]
    have hiv : i∉goodEdges a b K v := by
      intro hi
      exact hn (show H.Adj (a i) (b i) from ⟨i,hi,Or.inl ⟨rfl,rfl⟩⟩).reachable
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hpres,fun he=>hiv (he ▸ hiw)⟩)
    exact (not_lt_of_ge (hmaxv w)) hlt
  refine ⟨v,?_⟩
  intro x y
  obtain ⟨p⟩ := hconn x y
  induction p with
  | nil => exact .rfl
  | @cons x y z h p ih =>
    obtain ⟨i,-,h|h⟩ := h
    · exact (h.1 ▸ h.2 ▸ hreach i).trans ih
    · exact (h.2 ▸ h.1 ▸ (hreach i).symm).trans ih

theorem exists_connected_good_restrict (a b:E→V) (hneq:∀i,a i≠b i) (K:E→D)
    (R:Set E) (hconn:(edgeGraph a b hneq R).Preconnected) :
    ∃ v:V→D,(edgeGraph a b hneq (R∩(goodEdges a b K v : Set E))).Preconnected := by
  classical
  let I := {i // i∈R}
  let _ : Fintype I := Fintype.ofFinite I
  let a' : I→V := fun i=>a i.val
  let b' : I→V := fun i=>b i.val
  have hab' : ∀ i:I,a' i≠b' i := fun i=>hneq i.val
  have heq0 : edgeGraph a' b' hab' univ=edgeGraph a b hneq R := by
    ext x y
    constructor
    · rintro ⟨i,-,h⟩; exact ⟨i.val,i.property,h⟩
    · rintro ⟨i,hi,h⟩; exact ⟨⟨i,hi⟩,mem_univ _,h⟩
  obtain ⟨v,hv⟩ := exists_connected_good a' b' hab' (fun i=>K i.val) (heq0 ▸ hconn)
  refine ⟨v,?_⟩
  have heq : edgeGraph a' b' hab' (goodEdges a' b' (fun i=>K i.val) v : Set I)=
      edgeGraph a b hneq (R∩(goodEdges a b K v : Set E)) := by
    ext x y
    constructor
    · rintro ⟨i,hi,h⟩
      exact ⟨i.val,⟨i.property,by simpa [a',b'] using hi⟩,h⟩
    · rintro ⟨i,⟨hi,hg⟩,h⟩
      exact ⟨⟨i,hi⟩,by simpa [a',b'] using hg,h⟩
  rwa [heq] at hv

theorem label_equal_of_other_edges {W Z : Type*} [Finite W] (G:SimpleGraph W)
    (hG:G.IsCycles) {a b:W} (hab:G.Adj a b) (f:W→Z)
    (hother:∀x y,G.Adj x y → s(x,y)≠s(a,b) → f x=f y) : f a=f b := by
  obtain ⟨p⟩ := hG.reachable_deleteEdges hab
  have hw {x y:W} (p:(G.deleteEdges {s(a,b)}).Walk x y) : f x=f y := by
    induction p with
    | nil => rfl
    | @cons x y z h p ih =>
      have hx : G.Adj x y ∧ s(x,y)∉({s(a,b)}:Set (Sym2 W)) := SimpleGraph.deleteEdges_adj.mp h
      exact (hother x y hx.1 (by simpa using hx.2)).trans ih
  exact hw p
end CannonGraphGauge

end
end
end
end

end OAI
