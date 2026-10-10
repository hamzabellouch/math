import Mathlib
import OAI.Algebra.GroupRing.ConcreteGroup

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SampleGraph.FullPairing
open scoped Classical
open BlockAlignment ComparedBlocks GirthAsymptotics ActualPatternEvent TypedGraphs
variable {rep : ℕ} {r : Match rep} {x : VA rep} {y : VB rep}
  {s : PathSystem rep r x y} (a : FullPairing s) (cap : ℕ) (hc : 0<cap)
  (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
/-- Transfer the SAME separator sets/parts/cost to the actual short-closed
paths. In particular no extra charge for the appended tails is introduced. -/
def closed_split (d : DecidableEq (ClosedWords.Piece s cap)) (S : Finset (ClosedWords.Piece s cap))
    (P : @RecursiveSeparator.Split (ClosedWords.Piece s cap) d
      (PairingClusters.Rel (fun z : Position (BalancedRotation.len s.paths cap hc)=>z.1)
        (a.α cap hc)) S) :
    @RecursiveSeparator.Split (ClosedWords.Piece s cap) d
      (PairingClusters.Rel (fun z : Position (fun t=>((a.closed cap hc hL hd).paths t).length)=>z.1)
        (a.closed cap hc hL hd).comparisons.pairing.partner) S :=
  @RecursiveSeparator.Split.of_off_diagonal (ClosedWords.Piece s cap) d _ _ _
      (fun _ _ h=>(a.closed_rel cap hc hL hd h).symm) P

end TorsionFreeZeroDivisors.SampleGraph.FullPairing
namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks
variable {rep : ℕ} {r : ActualPatternEvent.Match rep} {x : VA rep} {y : VB rep} {z w : VA rep⊕VB rep}
  {O : Type} [Fintype O]
  (a : FinitePicture.Data (O:=O) (graph rep r) (label rep) Types.inverse z w)
  (hzw : z≠w) (hr : a.Reduced) (hz : z=Sum.inl x ∨ z=Sum.inr y)
  (cap : ℕ) (hc : 0<cap)
/-- The actual segmented words of a reduced lifted disk picture have genus
zero, with their literal segment-boundary rotation and full letter pairing.
This does not assert the missing sharp planar separator theorem. -/
lemma segmented_genusZero :
    MapEuler.GenusZero
      (BoundaryRotation.perm (BalancedRotation.len (system a hzw hr hz).paths cap hc))
      ((pairing a hzw hr hz).α cap hc) :=
  BalancedGenus.genusZero (system a hzw hr hz).paths cap hc
    (pairing a hzw hr hz).perm (pairing a hzw hr hz).involutive
    (pairing_genusZero a hzw hr hz)

end TorsionFreeZeroDivisors.SampleGraph.Picture
namespace TorsionFreeZeroDivisors.MapEuler

section
open scoped Classical
open PermutationCycles PairingFactors
variable {O : Type} [Fintype O]

/-- Any submatching of a literal genus-zero map is still genus zero; dangling
half-edges are retained as fixed points. No embedding predicate is assumed. -/
theorem genusZero_subpairing (σ α β : Equiv.Perm O)
    (ha : Function.Involutive α) (_hb : Function.Involutive β)
    (hsub : ∀ x, β x = x ∨ β x = α x) (hz : GenusZero σ α) :
    GenusZero σ β := by
  classical
  generalize hn : α.support.card = n at *
  induction n using Nat.strong_induction_on generalizing α with
  | h n ih =>
    by_cases he : α = β
    · simpa only [he] using hz
    · obtain ⟨p,hp⟩ : ∃ p, α p ≠ β p := by
        by_contra h
        push Not at h
        exact he (Equiv.ext h)
      have hbp : β p = p := (hsub p).resolve_right (Ne.symm hp)
      have hap : α p ≠ p := by simpa only [hbp] using hp
      have hbq : β (α p) = α p := by
        rcases hsub (α p) with hh|hh
        · exact hh
        · rw [ha] at hh
          exact (hap (β.injective (hh.trans hbp.symm))).elim
      have hs : ∀ x, β x = x ∨ β x = strip α p x := by
        intro x
        by_cases hxp : x = p
        · exact Or.inl (hxp ▸ hbp)
        by_cases hxq : x = α p
        · exact Or.inl (hxq ▸ hbq)
        rcases hsub x with hh|hh
        · exact Or.inl hh
        · exact Or.inr (hh.trans (strip_away α ha p x hxp hxq).symm)
      have hc := strip_card α ha p hap
      exact ih (strip α p).support.card (by omega) (strip α p)
        (strip_involutive α ha p) hs (genusZero_strip σ α ha hz p hap) rfl

/-- Keep a pair precisely when both its actual endpoint darts satisfy P. -/
def inducedPairFun (α : Equiv.Perm O) (P : O → Prop) (x : O) : O :=
  if P x ∧ P (α x) then α x else x

omit [Fintype O] in
lemma inducedPairFun_involutive (α : Equiv.Perm O) (ha : Function.Involutive α)
    (P : O → Prop) : Function.Involutive (inducedPairFun α P) := by
  intro x
  by_cases h : P x ∧ P (α x)
  · have h' : P (α x) ∧ P (α (α x)) := ⟨h.2,by rw [ha x]; exact h.1⟩
    simp only [inducedPairFun, ite_eq_left h, ite_eq_left h']
    exact ha x
  · simp only [inducedPairFun, ite_eq_right h]

def inducedPair (α : Equiv.Perm O) (ha : Function.Involutive α) (P : O → Prop) :
    Equiv.Perm O where
  toFun := inducedPairFun α P
  invFun := inducedPairFun α P
  left_inv := inducedPairFun_involutive α ha P
  right_inv := inducedPairFun_involutive α ha P

omit [Fintype O] in
lemma inducedPair_apply (α : Equiv.Perm O) (ha : Function.Involutive α)
    (P : O → Prop) (x : O) :
    inducedPair α ha P x = if P x ∧ P (α x) then α x else x := rfl

/-- The rotation of every vertex is unchanged; only crossing/outside pairs
are removed. This handles loops, parallel edges, and disconnected graphs. -/
theorem genusZero_inducedPair (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (P : O → Prop) (hz : GenusZero σ α) : GenusZero σ (inducedPair α ha P) := by
  apply genusZero_subpairing σ α _ ha (inducedPairFun_involutive α ha P) _ hz
  intro x
  rw [inducedPair_apply]
  split_ifs <;> simp

/-- The underlying simple graph of the actual permutation map. Ignoring loops
and parallel copies does not discard any adjacency between distinct vertices. -/
def graph (σ α : Equiv.Perm O) (ha : Function.Involutive α) : SimpleGraph (Cycle σ) where
  Adj v w := v ≠ w ∧ ∃ x, cycle σ x = v ∧ cycle σ (α x) = w
  symm := ⟨by
    intro v w ⟨hne,x,hx,hy⟩
    exact ⟨hne.symm,α x,hy,by rw [ha x]; exact hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype O] in
lemma graph_adj (σ α : Equiv.Perm O) (ha : Function.Involutive α) (v w : Cycle σ) :
    (graph σ α ha).Adj v w ↔ v ≠ w ∧ ∃ x, cycle σ x = v ∧ cycle σ (α x) = w := Iff.rfl

omit [Fintype O] in
/-- The graph after matching deletion is exactly the induced relation on the
chosen vertices, with the other vertices isolated. This is literal equality of
adjacencies, not an assumption of inherited planarity. -/
theorem graph_inducedPair (σ α : Equiv.Perm O) (ha : Function.Involutive α)
    (S : Set (Cycle σ)) (v w : Cycle σ) :
    (graph σ (inducedPair α ha (fun x=>cycle σ x∈S))
      (inducedPairFun_involutive α ha _)).Adj v w ↔
    (graph σ α ha).Adj v w ∧ v ∈ S ∧ w ∈ S := by
  classical
  simp only [graph_adj]
  constructor
  · rintro ⟨hne,x,hx,hy⟩
    change cycle σ (if cycle σ x ∈ S ∧ cycle σ (α x) ∈ S then α x else x) = w at hy
    by_cases h : cycle σ x ∈ S ∧ cycle σ (α x) ∈ S
    · rw [ite_eq_left h] at hy
      exact ⟨⟨hne,x,hx,hy⟩,hx ▸ h.1,hy ▸ h.2⟩
    · rw [ite_eq_right h] at hy
      exact (hne (hx.symm.trans hy)).elim
  · rintro ⟨⟨hne,x,hx,hy⟩,hv,hw⟩
    refine ⟨hne,x,hx,?_⟩
    change cycle σ (if cycle σ x ∈ S ∧ cycle σ (α x) ∈ S then α x else x) = w
    rw [ite_eq_left (show cycle σ x ∈ S ∧ cycle σ (α x) ∈ S by simpa only [hx,hy] using And.intro hv hw)]
    exact hy

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (ha : Function.Involutive α)

lemma component_rot (x : O) : component σ α (σ x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl)))
lemma component_pair (x : O) : component σ α (α x)=component σ α x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl)))

include ha in
lemma reachable_pair (x : O) :
    (graph σ α ha).Reachable (cycle σ x) (cycle σ (α x)) := by
  by_cases h : cycle σ x=cycle σ (α x)
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h,x,rfl,rfl⟩

include ha in
lemma reachable_of_component {x y : O}
    (h : component σ α x=component σ α y) :
    (graph σ α ha).Reachable (cycle σ x) (cycle σ y) := by
  have hh : Relation.EqvGen (Edge σ α) x y := Quotient.exact h
  clear h
  induction hh with
  | rel x y h =>
    rcases h with h|h
    · rw [←h,cycle_apply]
    · rw [←h]
      exact reachable_pair σ α ha x
  | refl => exact SimpleGraph.Reachable.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

variable [Fintype O]
def vertexComponent : Cycle σ → Component σ α :=
  PermutationCycles.lift σ (component σ α) (component_rot σ α)

@[simp] lemma vertexComponent_cycle (x : O) :
    vertexComponent σ α (cycle σ x)=component σ α x := rfl

lemma vertexComponent_adj {v w : Cycle σ} (h : (graph σ α ha).Adj v w) :
    vertexComponent σ α v=vertexComponent σ α w := by
  obtain ⟨_,x,rfl,rfl⟩ := h
  exact (component_pair σ α x).symm

include ha in
lemma vertexComponent_reachable {v w : Cycle σ} (h : (graph σ α ha).Reachable v w) :
    vertexComponent σ α v=vertexComponent σ α w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (vertexComponent_adj σ α ha h).trans ih

/-- Equality of actual map components is exactly graph reachability, including
unpaired darts, loops and parallel edges. No graph planarity predicate intervenes. -/
theorem component_eq_iff_reachable (x y : O) :
    component σ α x=component σ α y ↔
      (graph σ α ha).Reachable (cycle σ x) (cycle σ y) :=
  ⟨reachable_of_component σ α ha,vertexComponent_reachable σ α ha⟩

/-- The map and the underlying simple graph have literally the same components. -/
def graphComponentEquiv : Component σ α ≃ (graph σ α ha).ConnectedComponent where
  toFun := Quotient.lift (fun x=>(graph σ α ha).connectedComponentMk (cycle σ x))
    (fun x y h=>SimpleGraph.ConnectedComponent.sound
      (reachable_of_component σ α ha (Quotient.sound h)))
  invFun := Quot.lift (vertexComponent σ α) (fun _ _ h=>vertexComponent_reachable σ α ha h)
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with | h x => rfl
  right_inv := by
    intro c
    induction c using Quot.inductionOn with
    | h v =>
      obtain ⟨x,rfl⟩ := cycle_surjective σ v
      rfl

lemma graphComponent_card : Nat.card (Component σ α)=Nat.card (graph σ α ha).ConnectedComponent :=
  Nat.card_congr (graphComponentEquiv σ α ha)

end

section
open scoped Classical
open PermutationCycles
variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

/-- Pick an actual occurrence realizing each directed edge; this is injective
because both endpoint vertices of an occurrence are fixed. -/
def realizeDart (d : (graph σ α ha).Dart) : O := d.adj.2.choose
omit [Fintype O] in
lemma realizeDart_fst (d : (graph σ α ha).Dart) :
    cycle σ (realizeDart σ α ha d)=d.fst := d.adj.2.choose_spec.1
omit [Fintype O] in
lemma realizeDart_snd (d : (graph σ α ha).Dart) :
    cycle σ (α (realizeDart σ α ha d))=d.snd := d.adj.2.choose_spec.2
lemma realizeDart_mem (d : (graph σ α ha).Dart) : realizeDart σ α ha d∈α.support := by
  apply Equiv.Perm.mem_support.mpr
  intro he
  apply d.fst_ne_snd
  rw [←realizeDart_fst σ α ha d,←realizeDart_snd σ α ha d,he]
omit [Fintype O] in
lemma realizeDart_injective : Function.Injective (realizeDart σ α ha) := by
  intro d e h
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rw [←realizeDart_fst σ α ha d,←realizeDart_fst σ α ha e,h]
  · rw [←realizeDart_snd σ α ha d,←realizeDart_snd σ α ha e,h]

/-- Removing loops and parallel copies lowers the true paired-edge count. -/
theorem twice_graph_edges_le_support :
    2*Nat.card (graph σ α ha).edgeSet≤α.support.card := by
  let f : (graph σ α ha).Dart → {x // x∈α.support} :=
    fun d=>⟨realizeDart σ α ha d,realizeDart_mem σ α ha d⟩
  have hi : Function.Injective f := fun _ _ h=>
    realizeDart_injective σ α ha (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe,SimpleGraph.dart_card_eq_twice_card_edges,
    SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] at hc
  exact hc

/-- A connected map with the minimal possible true edge count is a tree,
even though the ambient definition permits loops and parallel edges. -/
theorem graph_isTree_of_support (hc : (graph σ α ha).Connected)
    (he : α.support.card+2=2*Nat.card (Cycle σ)) : (graph σ α ha).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc,?_⟩
  have h₁ := twice_graph_edges_le_support σ α ha
  have h₂ := hc.card_vert_le_card_edgeSet_add_one
  omega

end

open scoped Classical BigOperators
open PermutationCycles
variable {O : Type} (σ α : Equiv.Perm O) (ha : Function.Involutive α)

lemma edge_has_realizer (e : (graph σ α ha).edgeSet) :
    ∃ x : O, α x≠x ∧ s(cycle σ x,cycle σ (α x))=e.val := by
  obtain ⟨e,he⟩ := e
  induction e using Sym2.inductionOn with
  | _ v w =>
    obtain ⟨hne,x,hx,hy⟩ := he
    refine ⟨x,?_,?_⟩
    rotate_left
    · change s(cycle σ x,cycle σ (α x))=s(v,w)
      rw [hx,hy]
    intro h
    exact hne (hx.symm.trans ((congrArg (cycle σ) h).symm.trans hy))

def edgeRep (e : (graph σ α ha).edgeSet) : O := (edge_has_realizer σ α ha e).choose
lemma edgeRep_ne (e : (graph σ α ha).edgeSet) : α (edgeRep σ α ha e)≠edgeRep σ α ha e :=
  (edge_has_realizer σ α ha e).choose_spec.1
lemma edgeRep_edge (e : (graph σ α ha).edgeSet) :
    s(cycle σ (edgeRep σ α ha e),cycle σ (α (edgeRep σ α ha e)))=e.val :=
  (edge_has_realizer σ α ha e).choose_spec.2

variable (T : SimpleGraph (Cycle σ)) (hT : T≤graph σ α ha)
def edgeOfSubgraph (e : T.edgeSet) : (graph σ α ha).edgeSet :=
  ⟨e.val,SimpleGraph.edgeSet_mono hT e.property⟩
def pairFinset (e : T.edgeSet) : Finset O :=
  {edgeRep σ α ha (edgeOfSubgraph σ α ha T hT e),
    α (edgeRep σ α ha (edgeOfSubgraph σ α ha T hT e))}

lemma pairFinset_card (e : T.edgeSet) : (pairFinset σ α ha T hT e).card=2 := by
  simp [pairFinset,Ne.symm (edgeRep_ne σ α ha _)]
lemma pairFinset_nonfixed (e : T.edgeSet) {x : O} (hx : x∈pairFinset σ α ha T hT e) : α x≠x := by
  simp only [pairFinset,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl
  · exact edgeRep_ne σ α ha _
  · rw [ha]
    exact Ne.symm (edgeRep_ne σ α ha _)
lemma pairFinset_pair (e : T.edgeSet) {x : O} (hx : x∈pairFinset σ α ha T hT e) :
    α x∈pairFinset σ α ha T hT e := by
  simp only [pairFinset,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  rcases hx with rfl|rfl
  · exact Or.inr rfl
  · exact Or.inl (ha _)
lemma pairFinset_edge (e : T.edgeSet) {x : O} (hx : x∈pairFinset σ α ha T hT e) :
    s(cycle σ x,cycle σ (α x))=e.val := by
  simp only [pairFinset,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl
  · exact edgeRep_edge σ α ha _
  · rw [ha,Sym2.eq_swap]
    exact edgeRep_edge σ α ha _

lemma pairFinset_disjoint {e f : T.edgeSet} (hef : e≠f) :
    Disjoint (pairFinset σ α ha T hT e) (pairFinset σ α ha T hT f) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hef (Subtype.ext ((pairFinset_edge σ α ha T hT e hx).symm.trans
    (pairFinset_edge σ α ha T hT f hy)))

variable [Fintype O]
def pickedDarts : Finset O := Finset.univ.biUnion (pairFinset σ α ha T hT)
lemma mem_pickedDarts (x : O) :
    x∈pickedDarts σ α ha T hT ↔ ∃ e : T.edgeSet,x∈pairFinset σ α ha T hT e := by
  simp only [pickedDarts,Finset.mem_biUnion,Finset.mem_univ,true_and]
lemma pickedDarts_nonfixed {x : O} (hx : x∈pickedDarts σ α ha T hT) : α x≠x := by
  obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp hx
  exact pairFinset_nonfixed σ α ha T hT e he
lemma pickedDarts_pair {x : O} (hx : x∈pickedDarts σ α ha T hT) : α x∈pickedDarts σ α ha T hT := by
  obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp hx
  exact (mem_pickedDarts σ α ha T hT (α x)).mpr ⟨e,pairFinset_pair σ α ha T hT e he⟩
lemma pickedDarts_card : (pickedDarts σ α ha T hT).card=2*Nat.card T.edgeSet := by
  rw [pickedDarts,Finset.card_biUnion]
  · simp only [pairFinset_card,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
    omega
  · intro e _ f _ hef
    exact pairFinset_disjoint σ α ha T hT hef

/-- A chosen simple subgraph is realized by exactly one original paired edge
per simple edge, with the original vertex rotations unchanged. -/
def subgraphPair : Equiv.Perm O := inducedPair α ha (fun x=>x∈pickedDarts σ α ha T hT)
lemma subgraphPair_involutive : Function.Involutive (subgraphPair σ α ha T hT) :=
  inducedPairFun_involutive α ha _
lemma subgraphPair_apply (x : O) : subgraphPair σ α ha T hT x=
    if x∈pickedDarts σ α ha T hT then α x else x := by
  rw [subgraphPair,inducedPair_apply]
  by_cases hx : x∈pickedDarts σ α ha T hT
  · rw [ite_eq_left hx,ite_eq_left ⟨hx,pickedDarts_pair σ α ha T hT hx⟩]
  · rw [ite_eq_right hx,ite_eq_right (fun h=>hx h.1)]
lemma subgraphPair_support : (subgraphPair σ α ha T hT).support=pickedDarts σ α ha T hT := by
  ext x
  rw [Equiv.Perm.mem_support,subgraphPair_apply]
  by_cases hx : x∈pickedDarts σ α ha T hT
  · rw [ite_eq_left hx]
    exact iff_of_true (pickedDarts_nonfixed σ α ha T hT hx) hx
  · rw [ite_eq_right hx]
    simp only [ne_eq,not_true_eq_false,false_iff]
    exact hx
lemma subgraphPair_support_card : (subgraphPair σ α ha T hT).support.card=2*Nat.card T.edgeSet := by
  rw [subgraphPair_support,pickedDarts_card]

lemma subgraphPair_graph :
    graph σ (subgraphPair σ α ha T hT) (subgraphPair_involutive σ α ha T hT)=T := by
  ext v w
  constructor
  · rintro ⟨hne,x,hx,hy⟩
    rw [subgraphPair_apply] at hy
    by_cases hp : x∈pickedDarts σ α ha T hT
    · rw [ite_eq_left hp] at hy
      obtain ⟨e,he⟩ := (mem_pickedDarts σ α ha T hT x).mp hp
      have hedge := pairFinset_edge σ α ha T hT e he
      rw [hx,hy] at hedge
      exact (T.mem_edgeSet).mp (hedge.symm ▸ e.property)
    · rw [ite_eq_right hp] at hy
      exact (hne (hx.symm.trans hy)).elim
  · intro h
    let e : T.edgeSet := ⟨s(v,w),h⟩
    let p := edgeRep σ α ha (edgeOfSubgraph σ α ha T hT e)
    have hmem : p∈pickedDarts σ α ha T hT :=
      (mem_pickedDarts σ α ha T hT p).mpr ⟨e,Finset.mem_insert_self _ _⟩
    have he : s(cycle σ p,cycle σ (α p))=s(v,w) := edgeRep_edge σ α ha _
    rcases Sym2.eq_iff.mp he with ⟨hv,hw⟩|⟨hw,hv⟩
    · refine ⟨h.ne,p,hv,?_⟩
      rw [subgraphPair_apply,ite_eq_left hmem]
      exact hw
    · refine ⟨h.ne,α p,hv,?_⟩
      rw [subgraphPair_apply,ite_eq_left (pickedDarts_pair σ α ha T hT hmem),ha]
      exact hw

lemma genusZero_subgraphPair (hz : GenusZero σ α) :
    GenusZero σ (subgraphPair σ α ha T hT) := genusZero_inducedPair σ α ha _ hz

end TorsionFreeZeroDivisors.MapEuler

end

end OAI
