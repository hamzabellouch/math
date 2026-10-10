import Mathlib
import OAI.Combinatorics.ThinTrees.Encoding.BinaryReduction

namespace OAI

/-! Canonical expansion. -/

section

namespace AlgorithmicThinTrees.BinaryInput
open StrongThinTree Finset

def copies (x : BinaryInput) : List x.Edge :=
  (List.ofFn fun i : Fin x.p => List.ofFn fun j : Fin (x.multiplicity i) =>
    (⟨i,j⟩ : x.Edge)).flatten

lemma mem_copies (x : BinaryInput) (e : x.Edge) : e ∈ x.copies := by
  rcases e with ⟨i,j⟩
  apply List.mem_flatten.mpr
  exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩

lemma copies_nodup (x : BinaryInput) : x.copies.Nodup := by
  rw [copies, List.nodup_flatten]
  constructor
  · intro l hl
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    exact List.nodup_ofFn.mpr (fun j k h => by cases h; rfl)
  · apply List.pairwise_iff_get.mpr
    intro i j hij
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    apply List.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha⟩ := List.mem_ofFn.mp he
    obtain ⟨b,hb⟩ := List.mem_ofFn.mp hf
    have heq := congrArg Sigma.fst (ha.trans hb.symm)
    exact (ne_of_lt hij) (Fin.ext (by simpa using congrArg Fin.val heq))

lemma copies_length (x : BinaryInput) : x.copies.length = Fintype.card x.Edge := by
  classical
  have hu : x.copies.toFinset = univ := by ext e; simp [mem_copies]
  rw [← List.toFinset_card_of_nodup (x.copies_nodup),hu,card_univ]

noncomputable def copiesEquiv (x : BinaryInput) : Fin x.copies.length ≃ x.Edge :=
  Equiv.ofBijective x.copies.get ⟨x.copies_nodup.injective_get,
    fun e => List.mem_iff_get.mp (x.mem_copies e)⟩

@[simp] lemma copiesEquiv_apply (x : BinaryInput) (e : Fin x.copies.length) :
    x.copiesEquiv e = x.copies.get e := rfl

def expanded (x : BinaryInput) : MultiGraph x.n x.copies.length where
  left e := x.left (x.copies.get e).1
  right e := x.right (x.copies.get e).1
  loopless e := ne_of_lt (x.ordered (x.copies.get e).1)

noncomputable def labelEquiv (x : BinaryInput) :
    Fin x.copies.length ≃ Fin (Fintype.card x.Edge) := x.copiesEquiv.trans x.edgeEquiv

@[simp] lemma labelEquiv_left (x : BinaryInput) (e : Fin x.copies.length) :
    x.graph.left (x.labelEquiv e) = x.expanded.left e := by
  simp [graph,labelEquiv,expanded]
@[simp] lemma labelEquiv_right (x : BinaryInput) (e : Fin x.copies.length) :
    x.graph.right (x.labelEquiv e) = x.expanded.right e := by
  simp [graph,labelEquiv,expanded]

lemma expanded_cut (x : BinaryInput) (S : Finset (Fin x.n)) :
    (x.expanded.cut univ S).card = (x.graph.cut univ S).card := by
  classical
  have hm : univ.image x.labelEquiv = univ := Finset.image_univ_of_surjective x.labelEquiv.surjective
  have h := x.expanded.cut_image x.graph x.labelEquiv x.labelEquiv_left x.labelEquiv_right univ S
  rw [hm] at h
  rw [h,card_image_of_injective _ x.labelEquiv.injective]

lemma expanded_edgeConnected (x : BinaryInput) {k : ℕ}
    (h : x.graph.EdgeConnected k) : x.expanded.EdgeConnected k := by
  intro S hS hS'
  rw [x.expanded_cut]
  exact h S hS hS'

lemma expanded_thinTree (x : BinaryInput) {C : ℝ} {k : ℕ}
    {T : Finset (Fin x.copies.length)} (hT : ThinTree C k x.expanded T) :
    ThinTree C k x.graph (T.image x.labelEquiv) := by
  refine ⟨x.expanded.spanningTree_image x.graph x.labelEquiv x.labelEquiv_left
    x.labelEquiv_right hT.1, ?_⟩
  intro S hS hS'
  rw [x.expanded.cut_image x.graph x.labelEquiv x.labelEquiv_left x.labelEquiv_right,
    card_image_of_injective _ x.labelEquiv.injective]
  simpa only [x.expanded_cut] using hT.2 S hS hS'

def originalCopy (x : BinaryInput) (e : Fin x.reduced.copies.length) : x.Edge :=
  x.liftCopy (x.reduced.copies.get e)

noncomputable def originalLabel (x : BinaryInput) (e : Fin x.reduced.copies.length) :
    Fin (Fintype.card x.Edge) := x.edgeEquiv (x.originalCopy e)

lemma originalLabel_eq (x : BinaryInput) :
    x.originalLabel = x.liftLabel ∘ x.reduced.labelEquiv := by
  funext e
  simp [originalLabel,originalCopy,liftLabel,labelEquiv]

lemma expanded_lift_thinTree (x : BinaryInput) (hn : 0 < x.n) (hk : 0 < x.k)
    {C : ℝ} (hC : 0 ≤ C) {T : Finset (Fin x.reduced.copies.length)}
    (hT : ThinTree C (x.n^2) x.reduced.expanded T) :
    ThinTree (2*C) x.k x.graph (T.image x.originalLabel) := by
  have h := x.lift_thinTree hn hk hC (x.reduced.expanded_thinTree hT)
  simpa only [Finset.image_image,←originalLabel_eq] using h

lemma originalCopy_injOn (x : BinaryInput) (hn : 0 < x.n)
    {T : Finset (Fin x.reduced.copies.length)} (hT : x.reduced.expanded.SpanningTree T) :
    Set.InjOn x.originalCopy T := by
  classical
  have hl (e) : x.graph.left (x.originalLabel e) = x.reduced.expanded.left e := by
    simp [originalLabel,originalCopy,graph,liftCopy,expanded]
  have hr (e) : x.graph.right (x.originalLabel e) = x.reduced.expanded.right e := by
    simp [originalLabel,originalCopy,graph,liftCopy,expanded]
  have ht := x.reduced.expanded.spanningTree_image x.graph x.originalLabel hl hr hT
  have hi : Set.InjOn x.originalLabel T := Finset.card_image_iff.mp (by
    rw [x.graph.spanningTree_card hn ht,x.reduced.expanded.spanningTree_card hn hT])
  intro e he f hf heq
  exact hi he hf (congrArg x.edgeEquiv heq)

lemma copies_map (x : BinaryInput) {α : Type*} (f : Fin x.p → α) :
    x.copies.map (fun e => f e.1) =
      (List.ofFn fun i : Fin x.p => List.replicate (x.multiplicity i) (f i)).flatten := by
  simp only [copies,List.map_flatten,List.map_ofFn,Function.comp_def]
  simp

lemma expanded_lefts (x : BinaryInput) :
    List.ofFn (fun e => (x.expanded.left e).val) =
      (List.ofFn fun i : Fin x.p => List.replicate (x.multiplicity i) (x.left i).val).flatten := by
  rw [←copies_map]
  simpa only [List.map_ofFn,Function.comp_def,expanded] using
    congrArg (List.map (fun e : x.Edge => (x.left e.1).val)) (List.ofFn_get x.copies)
lemma expanded_rights (x : BinaryInput) :
    List.ofFn (fun e => (x.expanded.right e).val) =
      (List.ofFn fun i : Fin x.p => List.replicate (x.multiplicity i) (x.right i).val).flatten := by
  rw [←copies_map]
  simpa only [List.map_ofFn,Function.comp_def,expanded] using
    congrArg (List.map (fun e : x.Edge => (x.right e.1).val)) (List.ofFn_get x.copies)
lemma expanded_records (x : BinaryInput) :
    List.ofFn (fun e : Fin x.copies.length => (x.copies.get e).1.val) =
      (List.ofFn fun i : Fin x.p => List.replicate (x.multiplicity i) i.val).flatten := by
  rw [←copies_map]
  simpa only [List.map_ofFn,Function.comp_def,expanded] using
    congrArg (List.map (fun e : x.Edge => e.1.val)) (List.ofFn_get x.copies)

end AlgorithmicThinTrees.BinaryInput
end

end OAI
