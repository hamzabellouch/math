import Mathlib
import OAI.Algebra.GroupRing.FullPairing

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MapEuler

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

lemma component_card_one_of_connected (hc : (graph σ α ha).Connected) :
    Nat.card (Component σ α)=1 := by
  rw [graphComponent_card σ α ha]
  have : Nonempty (Cycle σ) := hc.nonempty
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨hc.preconnected.subsingleton_connectedComponent,inferInstance⟩

omit [Fintype O] in
lemma connected_of_component_card_one (hc : Nat.card (Component σ α)=1) :
    (graph σ α ha).Connected := by
  obtain ⟨hs,hn⟩ := Nat.card_eq_one_iff_unique.mp hc
  have : Subsingleton (Component σ α) := hs
  obtain ⟨c⟩ := hn
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective c
  have : Nonempty (Cycle σ) := ⟨cycle σ x⟩
  refine ⟨?_⟩
  intro v w
  obtain ⟨y,rfl⟩ := cycle_surjective σ v
  obtain ⟨z,rfl⟩ := cycle_surjective σ w
  exact reachable_of_component σ α ha (Subsingleton.elim _ _)

/-- Literal connectedness can be read from the map's component quotient. -/
lemma connected_iff_component_card_one :
    (graph σ α ha).Connected ↔ Nat.card (Component σ α)=1 :=
  ⟨component_card_one_of_connected σ α ha,connected_of_component_card_one σ α ha⟩

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α β : Equiv.Perm O)
    (ha : Function.Involutive α) (hb : Function.Involutive β)
    (hsub : ∀ x,β x=x ∨ β x=α x)

include ha hb hsub in
lemma subpairing_commute : Commute α β := by
  show α*β=β*α
  ext x
  change α (β x)=β (α x)
  rcases hsub x with hx|hx
  · rcases hsub (α x) with hy|hy
    · rw [hx,hy]
    · rw [ha x] at hy
      have he : α x=x := β.injective (hy.trans hx.symm)
      rw [hx,he,hx]
  · have hy : β (α x)=x := by rw [←hx,hb x]
    rw [hx,ha x,hy]

include ha hb hsub in
lemma complement_involutive : Function.Involutive (α*β) := by
  have he : ∀ x, β (α x)=α (β x) := fun x=>
    (congrArg (fun f : Equiv.Perm O => f x) (subpairing_commute α β ha hb hsub).eq).symm
  intro x
  change α (β (α (β x)))=x
  rw [he,hb x,ha x]

include ha hsub in
lemma complement_subpairing : ∀ x,(α*β) x=x ∨ (α*β) x=α x := by
  intro x
  change α (β x)=x ∨ α (β x)=α x
  rcases hsub x with hx|hx
  · exact Or.inr (congrArg α hx)
  · exact Or.inl ((congrArg α hx).trans (ha x))

include ha hb hsub in
lemma complement_face : (α*β)*(α*σ)=β*σ := by
  ext x
  change α (β (α (σ x)))=β (σ x)
  have he : β (α (σ x))=α (β (σ x)) :=
    (congrArg (fun f : Equiv.Perm O => f (σ x)) (subpairing_commute α β ha hb hsub).eq).symm
  rw [he,ha]

variable [Fintype O]
include hsub in
lemma subpairing_support_subset : β.support⊆α.support := by
  intro x hx
  rw [Equiv.Perm.mem_support] at hx ⊢
  rcases hsub x with hh|hh
  · exact (hx hh).elim
  · rwa [←hh]

include ha hsub in
lemma complement_support : (α*β).support=α.support\β.support := by
  ext x
  simp only [Equiv.Perm.mem_support,Finset.mem_sdiff]
  change α (β x)≠x ↔ α x≠x ∧ ¬β x≠x
  rcases hsub x with hh|hh
  · simp only [hh,ne_eq,not_true_eq_false,not_false_eq_true,and_true]
  · simp only [hh,ha x,ne_eq,not_true_eq_false,not_not,false_iff]
    exact fun h=>h.1 h.2

include ha hsub in
lemma complement_support_card : (α*β).support.card+β.support.card=α.support.card := by
  rw [complement_support α β ha hsub,Finset.card_sdiff_of_subset (subpairing_support_subset α β hsub)]
  exact Nat.sub_add_cancel (Finset.card_le_card (subpairing_support_subset α β hsub))

include ha hb hsub in
/-- Deleting a chosen set of primal edges is actual complementary-pair deletion
in the dual map, not an assumed planar-minor interface. -/
theorem genusZero_complement_dual (hz : GenusZero σ α) : GenusZero (α*σ) (α*β) :=
  genusZero_subpairing (α*σ) α (α*β) ha (complement_involutive α β ha hb hsub)
    (complement_subpairing α β ha hsub) ((genusZero_dual σ α ha).mp hz)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)

lemma subgraphPair_subpairing : ∀ x,subgraphPair σ α ha T hT x=x ∨
    subgraphPair σ α ha T hT x=α x := by
  intro x
  rw [subgraphPair_apply]
  split_ifs <;> simp only [true_or,or_true]

lemma subgraphPair_support_tree (ht : T.IsTree) :
    (subgraphPair σ α ha T hT).support.card+2=2*Nat.card (Cycle σ) := by
  rw [subgraphPair_support_card]
  have hc := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
  omega

/-- The literal contour permutation of a chosen spanning tree has one cycle. -/
theorem tree_contour_card (hz : GenusZero σ α) (ht : T.IsTree) :
    Nat.card (Cycle (subgraphPair σ α ha T hT*σ))=1 := by
  have hc : (graph σ (subgraphPair σ α ha T hT) (subgraphPair_involutive σ α ha T hT)).Connected := by
    rw [subgraphPair_graph]
    exact ht.connected
  have hcomp := component_card_one_of_connected σ _ (subgraphPair_involutive σ α ha T hT) hc
  have hgen := genusZero_subgraphPair σ α ha T hT hz
  change 2*Nat.card (Cycle σ)+2*Nat.card (Cycle (subgraphPair σ α ha T hT*σ))=
    (subgraphPair σ α ha T hT).support.card+4*Nat.card (Component σ (subgraphPair σ α ha T hT)) at hgen
  have hsup := subgraphPair_support_tree σ α ha T hT ht
  omega

/-- The complementary edge matching in the original dual rotation has exactly
one fewer edge than dual vertices. -/
lemma cotree_support (hz : GenusZero σ α) (ht : T.IsTree) :
    (α*subgraphPair σ α ha T hT).support.card+2=2*Nat.card (Cycle (α*σ)) := by
  have hconn : (graph σ α ha).Connected := ht.connected.mono hT
  have hc := component_card_one_of_connected σ α ha hconn
  have hp := subgraphPair_support_tree σ α ha T hT ht
  have hs := complement_support_card α _ ha (subgraphPair_subpairing σ α ha T hT)
  change 2*Nat.card (Cycle σ)+2*Nat.card (Cycle (α*σ))=α.support.card+4*Nat.card (Component σ α) at hz
  omega

/-- Tree--cotree duality proved from actual permutations and Euler equality.
Loops and parallel edges in the original map are allowed. No embedding or
planar-duality axiom is used. -/
theorem spanning_cotree_isTree (hz : GenusZero σ α) (ht : T.IsTree) :
    (graph (α*σ) (α*subgraphPair σ α ha T hT)
      (complement_involutive α _ ha (subgraphPair_involutive σ α ha T hT)
        (subgraphPair_subpairing σ α ha T hT))).IsTree := by
  let β := subgraphPair σ α ha T hT
  have hb := subgraphPair_involutive σ α ha T hT
  have hsub := subgraphPair_subpairing σ α ha T hT
  have hface := complement_face σ α β ha hb hsub
  have hgen := genusZero_complement_dual σ α β ha hb hsub hz
  have htface := tree_contour_card σ α ha T hT hz ht
  have hs := cotree_support σ α ha T hT hz ht
  change 2*Nat.card (Cycle (α*σ))+2*Nat.card (Cycle ((α*β)*(α*σ)))=
    (α*β).support.card+4*Nat.card (Component (α*σ) (α*β)) at hgen
  rw [hface] at hgen
  have hcomp : Nat.card (Component (α*σ) (α*β))=1 := by
    dsimp only [β] at hgen ⊢
    omega
  exact graph_isTree_of_support (α*σ) (α*β) (complement_involutive α β ha hb hsub)
    (connected_of_component_card_one _ _ _ hcomp) hs

end

section
open scoped Classical
open PermutationCycles
variable {O V : Type} [Fintype O]

omit [Fintype O] in
lemma sameCycle_of_card_one (θ : Equiv.Perm O) (hθ : Nat.card (Cycle θ)=1) (x y : O) :
    θ.SameCycle x y := by
  have : Subsingleton (Cycle θ) := (Nat.card_eq_one_iff_unique.mp hθ).1
  exact (cycle_eq θ).mp (Subsingleton.elim _ _)

/-- In a cyclic contour with at most one exit from S, the labels of all members
of S are connected using only steps internal to S. This finite orbit argument
replaces a geometric assertion that tree-subtree corners form an interval. -/
theorem contour_interval_reachable (θ : Equiv.Perm O)
    (hθ : ∀ x y,θ.SameCycle x y) (S : Set O) (p : O)
    (hout : ∀ x∈S,θ x∉S → x=p) (H : SimpleGraph V) (label : O → V)
    (hstep : ∀ x∈S,θ x∈S → H.Reachable (label x) (label (θ x)))
    (x : O) (hx : x∈S) : H.Reachable (label p) (label x) := by
  by_contra hn
  have invariant (y : O) (hy : y∈S) (hn : ¬H.Reachable (label p) (label y)) :
      θ y∈S ∧ ¬H.Reachable (label p) (label (θ y)) := by
    have hy' : θ y∈S := by
      by_contra h
      have he := hout y hy h
      subst y
      exact hn (SimpleGraph.Reachable.refl _)
    refine ⟨hy',fun h=>hn (h.trans (hstep y hy hy').symm)⟩
  have hp (n : ℕ) : (θ^n) x∈S ∧ ¬H.Reachable (label p) (label ((θ^n) x)) := by
    induction n with
    | zero => exact ⟨hx,hn⟩
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      exact invariant _ ih.1 ih.2
  obtain ⟨n,he⟩ := (hθ x p).exists_nat_pow_eq
  have hh := (hp n).2
  rw [he] at hh
  exact hh (SimpleGraph.Reachable.refl _)

end

open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)

omit [Fintype O] in
lemma pairFinset_adj (e : T.edgeSet) {x : O} (hx : x∈pairFinset σ α ha T hT e) :
    T.Adj (cycle σ x) (cycle σ (α x)) := by
  change s(cycle σ x,cycle σ (α x))∈T.edgeSet
  rw [pairFinset_edge σ α ha T hT e hx]
  exact e.property

omit [Fintype O] in
lemma pairFinset_cycle_injective (e : T.edgeSet) {x y : O}
    (hx : x∈pairFinset σ α ha T hT e) (hy : y∈pairFinset σ α ha T hT e)
    (h : cycle σ x=cycle σ y) : x=y := by
  have hadj := pairFinset_adj σ α ha T hT e hx
  simp only [pairFinset,Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · rfl
  · exact (hadj.ne h).elim
  · rw [ha] at hadj
    exact (hadj.ne h).elim
  · rfl

lemma subgraphPair_nonfixed_mem {x : O} (hx : subgraphPair σ α ha T hT x≠x) :
    x∈pickedDarts σ α ha T hT := by
  have h := Equiv.Perm.mem_support.mpr hx
  rwa [subgraphPair_support] at h

lemma subgraphPair_nonfixed_apply {x : O} (hx : subgraphPair σ α ha T hT x≠x) :
    subgraphPair σ α ha T hT x=α x := by
  rw [subgraphPair_apply,ite_eq_left (subgraphPair_nonfixed_mem σ α ha T hT hx)]

lemma subgraphPair_adj {x : O} (hx : subgraphPair σ α ha T hT x≠x) :
    T.Adj (cycle σ x) (cycle σ (subgraphPair σ α ha T hT x)) := by
  obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp
    (subgraphPair_nonfixed_mem σ α ha T hT hx)
  rw [subgraphPair_nonfixed_apply σ α ha T hT hx]
  exact pairFinset_adj σ α ha T hT e he

/-- A realized simple subgraph has exactly one dart per directed adjacency. -/
theorem subgraphPair_dart_unique {x y : O}
    (hx : subgraphPair σ α ha T hT x≠x) (hy : subgraphPair σ α ha T hT y≠y)
    (h₁ : cycle σ x=cycle σ y)
    (h₂ : cycle σ (subgraphPair σ α ha T hT x)=cycle σ (subgraphPair σ α ha T hT y)) : x=y := by
  obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp
    (subgraphPair_nonfixed_mem σ α ha T hT hx)
  obtain ⟨f,hf⟩ := (mem_pickedDarts σ α ha T hT y).mp
    (subgraphPair_nonfixed_mem σ α ha T hT hy)
  rw [subgraphPair_nonfixed_apply σ α ha T hT hx,
    subgraphPair_nonfixed_apply σ α ha T hT hy] at h₂
  have hef : e=f := Subtype.ext (by
    rw [←pairFinset_edge σ α ha T hT e he,←pairFinset_edge σ α ha T hT f hf,h₁,h₂])
  subst f
  exact pairFinset_cycle_injective σ α ha T hT e he hf h₁

end TorsionFreeZeroDivisors.MapEuler

/-! The weighted centroid needed by planar dual-tree separator constructions.
This is an actual theorem for finite Mathlib trees, not a separator assumption. -/
namespace TorsionFreeZeroDivisors.TreeCentroid
open scoped Classical BigOperators
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} (h : G.IsTree)

def path (x y : V) : G.Walk x y := (h.connected.exists_path_of_dist x y).choose
lemma path_isPath (x y : V) : ((path h) x y).IsPath :=
  (h.connected.exists_path_of_dist x y).choose_spec.1
lemma path_length (x y : V) : ((path h) x y).length=G.dist x y :=
  (h.connected.exists_path_of_dist x y).choose_spec.2
lemma eq_path {x y : V} {p : G.Walk x y} (hp : p.IsPath) : p=(path h) x y :=
  Subtype.mk.inj (h.isAcyclic.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨_,(path_isPath h) x y⟩)
include h in
lemma path_dist {x y : V} {p : G.Walk x y} (hp : p.IsPath) : p.length=G.dist x y := by
  rw [(eq_path h) hp,(path_length h)]

def next (x y : V) : V := ((path h) x y).snd
lemma next_adj {x y : V} (hne : x≠y) : G.Adj x ((next h) x y) :=
  Walk.adj_snd (Walk.not_nil_of_ne hne)
lemma next_ne {x y : V} (hne : x≠y) : (next h) x y≠x := ((next_adj h) hne).ne'

lemma next_concat {c x y : V} {p : G.Walk c x} (hne : c≠x) (e : G.Adj x y) :
    (p.concat e).snd=p.snd := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons _ _ => simp only [Walk.concat_eq_append,Walk.cons_append,Walk.snd_cons]

lemma next_adjacent {c x y : V} (hx : c≠x) (hy : c≠y) (e : G.Adj x y) :
    (next h) c x=(next h) c y := by
  by_cases hm : x∈((path h) c y).support
  · have hh := h.isAcyclic.path_concat ((path_isPath h) c x) ((path_isPath h) c y) e hm
    unfold next
    rw [hh,next_concat hx]
  · have hm' := h.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      ((path_isPath h) c x) ((path_isPath h) c y) e hm
    have hh := h.isAcyclic.path_concat ((path_isPath h) c y) ((path_isPath h) c x) e.symm hm'
    unfold next
    rw [hh,next_concat hy]

lemma next_walk {c x y : V} (p : G.Walk x y) (hc : c∉p.support) :
    next h c x=next h c y := by
  induction p with
  | nil => rfl
  | @cons x z y e p ih =>
    simp only [Walk.support_cons,List.mem_cons,not_or] at hc
    have hz : c≠z := fun he=>hc.2 (he ▸ p.start_mem_support)
    exact (next_adjacent h hc.1 hz e).trans (ih hc.2)

lemma dist_next {c z : V} (hz : c≠z) : G.dist c z=G.dist ((next h) c z) z+1 := by
  have hl := (path_dist h) ((path_isPath h) c z).tail
  rw [Walk.length_tail,(path_length h)] at hl
  change G.dist c z-1=G.dist (next h c z) z at hl
  have hd : 0<G.dist c z := Nat.pos_of_ne_zero (fun he=>hz (h.connected.dist_eq_zero_iff.mp he))
  omega
lemma dist_not_next {c n z : V} (e : G.Adj c n) (hn : (next h) c z≠n) :
    G.dist n z=G.dist c z+1 := by
  have hmem : n∉((path h) c z).support := by
    intro hm
    exact hn (h.isAcyclic.eq_snd_of_adj_start ((path_isPath h) c z) e hm).symm
  have hp := ((path_isPath h) c z).cons (h := e.symm) hmem
  have hl := (path_dist h) hp
  simpa only [Walk.length_cons,(path_length h)] using hl.symm

variable [Fintype V]

def branch (c n : V) : Finset V := Finset.univ.filter (fun z=>z≠c ∧ (next h) c z=n)
lemma mem_branch {c n z : V} : z∈(branch h) c n ↔ z≠c ∧ (next h) c z=n := by
  simp only [branch,Finset.mem_filter,Finset.mem_univ,true_and]
lemma branch_adj {c n z : V} (hz : z∈(branch h) c n) : G.Adj c n := by
  obtain ⟨hz,hn⟩ := (mem_branch h).mp hz
  simpa only [hn] using (next_adj h) hz.symm
lemma branch_closed {c n x y : V} (hx : x∈(branch h) c n) (hy : y≠c) (e : G.Adj x y) :
    y∈(branch h) c n := by
  obtain ⟨hx,hn⟩ := (mem_branch h).mp hx
  exact (mem_branch h).mpr ⟨hy,((next_adjacent h) hx.symm hy.symm e).symm.trans hn⟩
lemma branch_disjoint {c n m : V} (hnm : n≠m) : Disjoint ((branch h) c n) ((branch h) c m) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact hnm (((mem_branch h).mp hz).2.symm.trans ((mem_branch h).mp hz').2)

lemma distance_step {c n z : V} (e : G.Adj c n) :
    G.dist n z + (if z∈(branch h) c n then 2 else 0)=G.dist c z+1 := by
  by_cases hb : z∈(branch h) c n
  · rw [ite_eq_left hb]
    obtain ⟨hz,hn⟩ := (mem_branch h).mp hb
    have hd := (dist_next h) hz.symm
    rw [hn] at hd
    omega
  · rw [ite_eq_right hb,Nat.add_zero]
    by_cases hz : z=c
    · subst z
      rw [SimpleGraph.dist_self,dist_eq_one_iff_adj.mpr e.symm]
    · apply (dist_not_next h) e
      intro hn
      exact hb ((mem_branch h).mpr ⟨hz,hn⟩)

def potential (w : V → ℕ) (c : V) : ℕ := ∑ z,w z*G.dist c z
lemma potential_step (w : V → ℕ) {c n : V} (e : G.Adj c n) :
    (potential (G:=G)) w n+2*(∑ z∈(branch h) c n,w z)=(potential (G:=G)) w c+∑ z,w z := by
  have hi (z : V) : w z*G.dist n z+(if z∈(branch h) c n then 2*w z else 0)=
      w z*G.dist c z+w z := by
    have hh := congrArg (fun t : ℕ=>w z*t) (distance_step h (z:=z) e)
    split_ifs at hh ⊢ <;> nlinarith only [hh]
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun z _=>hi z)
  simp only [Finset.sum_add_distrib] at hs
  have hif : (∑ z,if z∈(branch h) c n then 2*w z else 0)=2*(∑ z∈(branch h) c n,w z) := by
    rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.mul_sum]
  rw [hif] at hs
  exact hs

/-- A finite tree has a weighted centroid: every branch after its deletion
has at most half of the total nonnegative integral weight. Zero weights allowed. -/
theorem exists_centroid (w : V → ℕ) :
    ∃ c : V,∀ n : V,2*(∑ z∈(branch h) c n,w z)≤∑ z,w z := by
  have : Nonempty V := h.connected.nonempty
  obtain ⟨c,_,hc⟩ := Finset.univ.exists_min_image ((potential (G:=G)) w) Finset.univ_nonempty
  refine ⟨c,fun n=>?_⟩
  by_cases he : G.Adj c n
  · have hh := (potential_step h) w he
    have hm := hc n (Finset.mem_univ n)
    omega
  · have hempty : (branch h) c n=∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun z hz=>he ((branch_adj h) hz))
    simp only [hempty,Finset.sum_empty,Nat.mul_zero,Nat.zero_le]

end TorsionFreeZeroDivisors.TreeCentroid

end

end OAI
