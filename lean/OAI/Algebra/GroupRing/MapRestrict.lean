import Mathlib
import OAI.Algebra.GroupRing.BFSTree

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MapRestrict

section
open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (P : O→Prop)
    (hs : ∀ x,P (σ x)↔P x) (ha : ∀ x,P (α x)↔P x)
local notation "σP" => perm σ P hs
local notation "αP" => perm α P ha
local notation "σN" => perm σ (fun x=>¬P x) (not_invariant σ P hs)
local notation "αN" => perm α (fun x=>¬P x) (not_invariant α P ha)

def componentInclude : Component σP αP→ Component σ α :=
  MapEuler.lift σP αP (fun x=>component σ α x.val)
    (fun x=>component_rotation σ α x.val) (fun x=>component_partner σ α x.val)
omit [Fintype O] in
@[simp] lemma componentInclude_component (x : Subtype P) :
    componentInclude σ α P hs ha (component σP αP x)=component σ α x.val := rfl

def componentRaw (x : O) : Component σP αP ⊕ Component σN αN :=
  if h:P x then .inl (component σP αP ⟨x,h⟩) else .inr (component σN αN ⟨x,h⟩)
omit [Fintype O] in
lemma componentRaw_rotation (x : O) : componentRaw σ α P hs ha (σ x)=componentRaw σ α P hs ha x := by
  by_cases hx : P x
  · rw [componentRaw,dite_eq_left ((hs x).mpr hx),componentRaw,dite_eq_left hx]
    exact congrArg Sum.inl (component_rotation σP αP ⟨x,hx⟩)
  · rw [componentRaw,dite_eq_right (fun h=>hx ((hs x).mp h)),componentRaw,dite_eq_right hx]
    exact congrArg Sum.inr (component_rotation σN αN ⟨x,hx⟩)
omit [Fintype O] in
lemma componentRaw_partner (x : O) : componentRaw σ α P hs ha (α x)=componentRaw σ α P hs ha x := by
  by_cases hx : P x
  · rw [componentRaw,dite_eq_left ((ha x).mpr hx),componentRaw,dite_eq_left hx]
    exact congrArg Sum.inl (component_partner σP αP ⟨x,hx⟩)
  · rw [componentRaw,dite_eq_right (fun h=>hx ((ha x).mp h)),componentRaw,dite_eq_right hx]
    exact congrArg Sum.inr (component_partner σN αN ⟨x,hx⟩)

def componentEquiv : Component σ α≃Component σP αP ⊕ Component σN αN where
  toFun := MapEuler.lift σ α (componentRaw σ α P hs ha)
    (componentRaw_rotation σ α P hs ha) (componentRaw_partner σ α P hs ha)
  invFun := Sum.elim (componentInclude σ α P hs ha)
    (componentInclude σ α (fun x=>¬P x) (not_invariant σ P hs) (not_invariant α P ha))
  left_inv := by
    intro c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
    change (Sum.elim _ _) (componentRaw σ α P hs ha x)=component σ α x
    unfold componentRaw
    split_ifs <;> rfl
  right_inv := by
    intro c
    rcases c with c|c
    · obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
      change componentRaw σ α P hs ha x.val=Sum.inl (component σP αP x)
      rw [componentRaw,dite_eq_left x.property]
    · obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
      change componentRaw σ α P hs ha x.val=Sum.inr (component σN αN x)
      rw [componentRaw,dite_eq_right x.property]

lemma component_card : Nat.card (Component σ α)=Nat.card (Component σP αP)+Nat.card (Component σN αN) := by
  rw [Nat.card_congr (componentEquiv σ α P hs ha),Nat.card_sum]

omit [Fintype O] in
include hs ha in
lemma mul_invariant (x : O) : P ((α*σ) x)↔P x := (ha (σ x)).trans (hs x)
omit [Fintype O] in
lemma perm_mul : perm (α*σ) P (mul_invariant σ α P hs ha)=αP*σP := rfl

/-- Restriction to any invariant union of map components preserves actual
Euler genus zero. The proof uses decomposition and the universal Euler upper
bound on BOTH complementary pieces. -/
theorem genusZero (hi : Function.Involutive α) (hz : GenusZero σ α) : GenusZero σP αP := by
  have hs' := cycle_card σ P hs
  have hf' := cycle_card (α*σ) P (mul_invariant σ α P hs ha)
  have ha' := support_card α P ha
  have hc' := component_card σ α P hs ha
  have hP := MapEuler.upper σP αP (perm_involutive α P ha hi)
  have hN := MapEuler.upper σN αN (perm_involutive α (fun x=>¬P x) (not_invariant α P ha) hi)
  have heN : perm (α*σ) (fun x=>¬P x) (not_invariant (α*σ) P (mul_invariant σ α P hs ha))=αN*σN := rfl
  rw [perm_mul σ α P hs ha,heN] at hf'
  unfold GenusZero at hz ⊢
  simp only [ConedMap.support_card_nat] at ha' hP hN hz ⊢
  omega

end

open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
    (S : Set (Cycle σ))

lemma cycleInclude_injective (f : Equiv.Perm O) (P : O→Prop) (hf : ∀ x,P (f x)↔P x) :
    Function.Injective (cycleInclude f P hf) := (cycleEquiv f P hf).symm.injective.comp Sum.inl_injective

def internalPair : Equiv.Perm O := inducedPair α hi (fun x=>cycle σ x∈S)
omit [Fintype O] in
lemma internalPair_involutive : Function.Involutive (internalPair σ α hi S) :=
  inducedPairFun_involutive α hi _
omit [Fintype O] in
lemma rotation_invariant (x : O) : (cycle σ (σ x)∈S)↔cycle σ x∈S := by rw [cycle_apply]
omit [Fintype O] in
lemma pairing_invariant (x : O) : (cycle σ (internalPair σ α hi S x)∈S)↔cycle σ x∈S := by
  change (cycle σ (if cycle σ x∈S ∧ cycle σ (α x)∈S then α x else x)∈S)↔cycle σ x∈S
  split_ifs with h
  · exact iff_of_true h.2 h.1
  · rfl

def rotation := perm σ (fun x=>cycle σ x∈S) (rotation_invariant σ S)
def pairing := perm (internalPair σ α hi S) (fun x=>cycle σ x∈S) (pairing_invariant σ α hi S)
omit [Fintype O] in
lemma pairing_involutive : Function.Involutive (pairing σ α hi S) :=
  perm_involutive _ _ _ (internalPair_involutive σ α hi S)

def vertexEquiv : Cycle (rotation σ S)≃S where
  toFun c := ⟨cycleInclude σ (fun x=>cycle σ x∈S) (rotation_invariant σ S) c,by
    obtain ⟨x,rfl⟩ := cycle_surjective (rotation σ S) c
    exact x.property⟩
  invFun v := cycle (rotation σ S) ⟨Quotient.out v.val,by rw [MapEuler.home_cycle];exact v.property⟩
  left_inv := by
    intro c
    apply cycleInclude_injective
    exact Quotient.out_eq _
  right_inv := by intro v;exact Subtype.ext (Quotient.out_eq v.val)
@[simp] lemma vertexEquiv_cycle (x : {x : O // cycle σ x∈S}) :
    vertexEquiv σ S (cycle (rotation σ S) x)=⟨cycle σ x.val,x.property⟩ := rfl

/-- The restricted dart system realizes precisely the induced simple graph. -/
def graphIso : graph (rotation σ S) (pairing σ α hi S) (pairing_involutive σ α hi S) ≃g
    (graph σ α hi).induce S where
  toEquiv := vertexEquiv σ S
  map_rel_iff' := by
    intro v w
    constructor
    · intro he
      change (graph σ α hi).Adj (vertexEquiv σ S v).val (vertexEquiv σ S w).val at he
      obtain ⟨hne,x,hx,hy⟩ := he
      have hxS : cycle σ x∈S := hx ▸ (vertexEquiv σ S v).property
      have hyS : cycle σ (α x)∈S := hy ▸ (vertexEquiv σ S w).property
      refine ⟨fun h=>hne (congrArg (fun c=>(vertexEquiv σ S c).val) h),⟨x,hxS⟩,?_,?_⟩
      · apply (vertexEquiv σ S).injective
        exact Subtype.ext hx
      · apply (vertexEquiv σ S).injective
        apply Subtype.ext
        change cycle σ (internalPair σ α hi S x)=(vertexEquiv σ S w).val
        rw [internalPair,inducedPair_apply,ite_eq_left ⟨hxS,hyS⟩]
        exact hy
    · rintro ⟨hne,x,hx,hy⟩
      change (graph σ α hi).Adj (vertexEquiv σ S v).val (vertexEquiv σ S w).val
      have hvw : (vertexEquiv σ S v).val≠(vertexEquiv σ S w).val :=
        fun h=>hne ((vertexEquiv σ S).injective (Subtype.ext h))
      have hx' := congrArg (fun c=>(vertexEquiv σ S c).val) hx
      have hy' := congrArg (fun c=>(vertexEquiv σ S c).val) hy
      change cycle σ x.val=(vertexEquiv σ S v).val at hx'
      change cycle σ (internalPair σ α hi S x.val)=(vertexEquiv σ S w).val at hy'
      have hh : cycle σ (α x.val)∈S := by
        by_contra hn
        rw [internalPair,inducedPair_apply,ite_eq_right (fun h=>hn h.2)] at hy'
        exact hvw (hx'.symm.trans hy')
      rw [internalPair,inducedPair_apply,ite_eq_left ⟨x.property,hh⟩] at hy'
      exact ⟨hvw,x.val,hx',hy'⟩

theorem induced_genusZero (hz : GenusZero σ α) : GenusZero (rotation σ S) (pairing σ α hi S) :=
  genusZero σ (internalPair σ α hi S) (fun x=>cycle σ x∈S) (rotation_invariant σ S)
    (pairing_invariant σ α hi S) (internalPair_involutive σ α hi S)
    (genusZero_inducedPair σ α hi _ hz)

end TorsionFreeZeroDivisors.MapRestrict

namespace TorsionFreeZeroDivisors.MapContract
open scoped Classical
open PermutationCycles MapEuler
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (hi : Function.Involutive α)
    (B : Set (Cycle σ))
local notation "P" => fun x : O=>cycle σ x∈B
local notation "s" => MapRestrict.rotation σ B
local notation "a" => MapRestrict.pairing σ α hi B
local notation "hai" => MapRestrict.pairing_involutive σ α hi B
variable (T : SimpleGraph (Cycle (MapRestrict.rotation σ B)))
  (hT : T≤graph (MapRestrict.rotation σ B) (MapRestrict.pairing σ α hi B) (MapRestrict.pairing_involutive σ α hi B))
local notation "b" => subgraphPair s a hai T hT

def treePair : Equiv.Perm O := Equiv.Perm.ofSubtype (p:=fun x : O=>cycle σ x∈B)
  (subgraphPair (MapRestrict.rotation σ B) (MapRestrict.pairing σ α hi B)
    (MapRestrict.pairing_involutive σ α hi B) T hT)
local notation "β" => treePair σ α hi B T hT
lemma treePair_inside (x : {x : O // P x}) : β x=(b x).val := Equiv.Perm.ofSubtype_apply_coe b x
lemma treePair_outside (x : O) (hx : ¬P x) : β x=x := Equiv.Perm.ofSubtype_apply_of_not_mem b hx
lemma treePair_invariant (x : O) : P (β x)↔P x := Equiv.Perm.ofSubtype_apply_mem_iff_mem b x
lemma treePair_involutive : Function.Involutive β := by
  intro x
  by_cases hx : P x
  · have h := congrArg Subtype.val (subgraphPair_involutive s a hai T hT ⟨x,hx⟩)
    change β (β (⟨x,hx⟩ : {x : O // P x}))=x
    rw [treePair_inside,treePair_inside]
    exact h
  · rw [treePair_outside σ α hi B T hT x hx,treePair_outside σ α hi B T hT x hx]
lemma treePair_subpairing (x : O) : β x=x ∨ β x=α x := by
  by_cases hx : P x
  · have he := subgraphPair_subpairing s a hai T hT ⟨x,hx⟩
    rcases he with he|he
    · exact Or.inl ((treePair_inside σ α hi B T hT ⟨x,hx⟩).trans (congrArg Subtype.val he))
    · have h := (treePair_inside σ α hi B T hT ⟨x,hx⟩).trans (congrArg Subtype.val he)
      change β x=MapRestrict.internalPair σ α hi B x at h
      rw [MapRestrict.internalPair,inducedPair_apply] at h
      split_ifs at h
      · exact Or.inr h
      · exact Or.inl h
  · exact Or.inl (treePair_outside σ α hi B T hT x hx)

def rotation : Equiv.Perm O := β*σ
def pairing : Equiv.Perm O := α*β
local notation "ρ" => rotation σ α hi B T hT
local notation "γ" => pairing σ α hi B T hT
lemma pairing_involutive : Function.Involutive γ :=
  complement_involutive α β hi (treePair_involutive σ α hi B T hT) (treePair_subpairing σ α hi B T hT)

theorem genusZero (hz : GenusZero σ α) : GenusZero ρ γ := by
  have h := (genusZero_dual (α*σ) γ (pairing_involutive σ α hi B T hT)).mp
    (genusZero_complement_dual σ α β hi (treePair_involutive σ α hi B T hT)
      (treePair_subpairing σ α hi B T hT) hz)
  rw [show γ*(α*σ)=ρ from complement_face σ α β hi (treePair_involutive σ α hi B T hT)
    (treePair_subpairing σ α hi B T hT)] at h
  exact h

lemma rotation_invariant (x : O) : P (ρ x)↔P x := by
  change P (β (σ x))↔P x
  simpa only [cycle_apply] using treePair_invariant σ α hi B T hT (σ x)
lemma rotation_inside : MapRestrict.perm ρ P (rotation_invariant σ α hi B T hT)=b*s := by
  ext x
  exact treePair_inside σ α hi B T hT (s x)

variable (hz : GenusZero σ α) (ht : T.IsTree)
include hz ht in
lemma inside_cycle_eq {x y : O} (hx : P x) (hy : P y) : cycle ρ x=cycle ρ y := by
  have hn := tree_contour_card s a hai T hT (MapRestrict.induced_genusZero σ α hi B hz) ht
  have hs : Subsingleton (Cycle (b*s)) := (Nat.card_eq_one_iff_unique.mp hn).1
  have h := Subsingleton.elim (cycle (b*s) ⟨x,hx⟩) (cycle (b*s) ⟨y,hy⟩)
  rw [←rotation_inside σ α hi B T hT] at h
  exact congrArg (MapRestrict.cycleInclude ρ P (rotation_invariant σ α hi B T hT)) h

include hz ht in
lemma quotient_invariant (x : O) : cycle ρ (σ x)=cycle ρ x := by
  by_cases hx : P x
  · exact inside_cycle_eq σ α hi B T hT hz ht (by simpa only [cycle_apply] using hx) hx
  · have h : ρ x=σ x := treePair_outside σ α hi B T hT (σ x) (by simpa only [cycle_apply] using hx)
    rw [←h,cycle_apply]

def quotient : Cycle σ→Cycle ρ :=
  PermutationCycles.lift σ (fun x=>cycle ρ x) (quotient_invariant σ α hi B T hT hz ht)
local notation "q" => quotient σ α hi B T hT hz ht
@[simp] lemma quotient_cycle (x : O) : q (cycle σ x)=cycle ρ x := rfl
lemma quotient_surjective : Function.Surjective q := by
  intro v
  obtain ⟨x,rfl⟩ := cycle_surjective ρ v
  exact ⟨cycle σ x,rfl⟩

def labelRaw (x : O) : Option (Cycle σ) := if P x then none else some (cycle σ x)
lemma labelRaw_invariant (x : O) : labelRaw σ B (ρ x)=labelRaw σ B x := by
  by_cases hx : P x
  · rw [labelRaw,ite_eq_left ((rotation_invariant σ α hi B T hT x).mpr hx),labelRaw,ite_eq_left hx]
  · have he : ρ x=σ x := treePair_outside σ α hi B T hT (σ x) (by simpa only [cycle_apply] using hx)
    simp only [he,labelRaw,cycle_apply]
def label : Cycle ρ→Option (Cycle σ) :=
  PermutationCycles.lift ρ (labelRaw σ B) (labelRaw_invariant σ α hi B T hT)
lemma label_quotient (v : Cycle σ) : label σ α hi B T hT (q v)=if v∈B then none else some v := by
  obtain ⟨x,rfl⟩ := cycle_surjective σ v
  rfl

lemma quotient_eq_iff (v w : Cycle σ) : q v=q w ↔ v=w ∨ (v∈B ∧ w∈B) := by
  constructor
  · intro h
    have he := congrArg (label σ α hi B T hT) h
    rw [label_quotient,label_quotient] at he
    by_cases hv : v∈B <;> by_cases hw : w∈B <;> simp only [hv,hw,ite_true,ite_false] at he
    · exact Or.inr ⟨hv,hw⟩
    · contradiction
    · contradiction
    · exact Or.inl (Option.some.inj he)
  · rintro (rfl|⟨hv,hw⟩)
    · rfl
    · obtain ⟨x,rfl⟩ := cycle_surjective σ v
      obtain ⟨y,rfl⟩ := cycle_surjective σ w
      exact inside_cycle_eq σ α hi B T hT hz ht hv hw

include hz ht in
lemma cycle_treePair (x : O) : cycle ρ (β x)=cycle ρ x := by
  by_cases hx : P x
  · exact inside_cycle_eq σ α hi B T hT hz ht ((treePair_invariant σ α hi B T hT x).mpr hx) hx
  · rw [treePair_outside σ α hi B T hT x hx]

/-- Every original edge either contracts to a vertex or is an actual edge. -/
lemma quotient_adj {v w : Cycle σ} (he : (graph σ α hi).Adj v w) :
    q v=q w ∨ (graph ρ γ (pairing_involutive σ α hi B T hT)).Adj (q v) (q w) := by
  by_cases h : q v=q w
  · exact Or.inl h
  · obtain ⟨_,x,rfl,rfl⟩ := he
    refine Or.inr ⟨h,β x,cycle_treePair σ α hi B T hT hz ht x,?_⟩
    change cycle ρ (α (β (β x)))=cycle ρ (α x)
    rw [treePair_involutive σ α hi B T hT x]

/-- No new nonloop adjacency is introduced by the literal contraction. -/
lemma adj_lift {v w : Cycle ρ} (he : (graph ρ γ (pairing_involutive σ α hi B T hT)).Adj v w) :
    ∃ x y,(graph σ α hi).Adj x y ∧ q x=v ∧ q y=w := by
  obtain ⟨hne,x,rfl,rfl⟩ := he
  have hb : β x=x := by
    rcases treePair_subpairing σ α hi B T hT x with h|h
    · exact h
    · have hf : γ x=x := (congrArg α h).trans (hi x)
      exact (hne (congrArg (cycle ρ) hf).symm).elim
  have he : γ x=α x := congrArg α hb
  refine ⟨cycle σ x,cycle σ (α x),⟨?_,x,rfl,rfl⟩,rfl,?_⟩
  · intro h
    exact hne ((congrArg q h).trans (congrArg (cycle ρ) he.symm))
  · exact congrArg (cycle ρ) he.symm

end TorsionFreeZeroDivisors.MapContract

namespace TorsionFreeZeroDivisors.GraphBall
open scoped Classical
open SimpleGraph
variable {V : Type} (G : SimpleGraph V) (hc : G.Connected) (root : V) (N : ℕ)
def vertices : Set V := {v | G.dist v root≤N}
def rootVertex : vertices G root N := ⟨root,by simp [vertices]⟩

include hc
lemma exists_walk (v : vertices G root N) :
    ∃ p : (G.induce (vertices G root N)).Walk v (rootVertex G root N), p.length=G.dist v.val root := by
  generalize hn : G.dist v.val root=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v.val=root
    · have he : v=rootVertex G root N := Subtype.ext hv
      subst v
      exact ⟨Walk.nil,by simpa only [Walk.length_nil,rootVertex,dist_self] using hn⟩
    · let u := BFSTree.parent G hc root v.val
      have hd : G.dist u root+1=G.dist v.val root := BFSTree.parent_dist G hc root v.val hv
      have hu : u∈vertices G root N := by have hh := v.property;change G.dist v.val root≤N at hh;exact by dsimp [vertices];omega
      obtain ⟨p,hp⟩ := ih (G.dist u root) (by omega) ⟨u,hu⟩ rfl
      have he : (G.induce (vertices G root N)).Adj v ⟨u,hu⟩ := BFSTree.parent_adj G hc root v.val hv
      refine ⟨p.cons he,?_⟩
      rw [Walk.length_cons,hp,hd,hn]

lemma connected : (G.induce (vertices G root N)).Connected := by
  apply (connected_iff_exists_forall_reachable (G.induce (vertices G root N))).mpr
  refine ⟨rootVertex G root N,fun v=>?_⟩
  obtain ⟨p,_⟩ := exists_walk G hc root N v
  exact p.reverse.reachable

lemma dist_root (v : vertices G root N) :
    (G.induce (vertices G root N)).dist v (rootVertex G root N)=G.dist v.val root := by
  apply Nat.le_antisymm
  · obtain ⟨p,hp⟩ := exists_walk G hc root N v
    rw [←hp]
    exact (G.induce (vertices G root N)).dist_le p
  · obtain ⟨p,hp⟩ := (connected G hc root N).exists_walk_length_eq_dist v (rootVertex G root N)
    let f : G.induce (vertices G root N) →g G := ⟨Subtype.val,fun h=>h⟩
    have h := G.dist_le (p.map f)
    change G.dist v.val root≤(p.map f).length at h
    simpa only [Walk.length_map,hp] using h

end TorsionFreeZeroDivisors.GraphBall

end

end OAI
