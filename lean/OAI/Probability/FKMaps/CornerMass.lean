import OAI.Probability.FKMaps.NodeOrder
import OAI.Probability.FKMaps.RootedLaw

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma nodeIndex_injective (t : CoreTree) : Function.Injective t.nodeIndex := by
  induction t with
  | leaf => intro v w _; exact @Subsingleton.elim PUnit _ v w
  | branch c ts ih =>
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl b => exact congrArg Sum.inl (Subsingleton.elim _ _)
      | inr w => simp only [nodeIndex] at h;omega
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases w with
      | inl a => simp only [nodeIndex] at h;omega
      | inr w =>
        obtain ⟨j,w⟩ := w
        have hij := le_antisymm (children_order c ts i j v w h.le)
          (children_order c ts j i w v h.ge)
        subst j
        have hvw := ih i (show (ts i).nodeIndex v=(ts i).nodeIndex w by
          simpa only [nodeIndex,Nat.add_left_cancel_iff] using h)
        subst w
        rfl

/-- The literal preorder indexing is an equivalence, including the root. -/
def nodeEquiv (t : CoreTree) : t.Node ≃ Fin t.labels.length :=
  Equiv.ofBijective (fun v => ⟨t.nodeIndex v,t.nodeIndex_bound v⟩)
    ⟨fun _ _ h => t.nodeIndex_injective (congrArg Fin.val h),fun i => by
      obtain ⟨v,hv⟩ := t.nodeIndex_surjective i.isLt
      exact ⟨v,Fin.ext hv⟩⟩

def VertexConstant {A : Type*} (t : CoreTree) (f : t.Dart → A) : Prop :=
  ∀ a b,t.matching.distance a b=0 → f a=f b

lemma child_vertexConstant {A : Type*} (c : Core) (ts : Fin c.val.length → CoreTree)
    (f : (branch c ts).Dart → A) (hf : (branch c ts).VertexConstant f)
    (i : Fin c.val.length) : (ts i).VertexConstant (f ∘ childDart ts i) := by
  intro a b hab
  have hn : ts i≠leaf := by
    intro h
    have hh : Nonempty (ts i).Dart := ⟨a⟩
    rw [h] at hh
    exact not_nonempty_empty hh
  obtain ⟨r,L,_,hL⟩ := root_and_head (ts i) hn
  apply hf
  rw [child_internal_distance c ts i r a b L hL,hab]

lemma child_root_value {A : Type*} (c : Core) (ts : Fin c.val.length → CoreTree)
    (f : (branch c ts).Dart → A) (hf : (branch c ts).VertexConstant f)
    (i : Fin c.val.length) :
    (((ts i).rootDart).map (f ∘ childDart ts i)).getD (f (coreDart ts (nextSlot c i)))=
      f (coreDart ts (nextSlot c i)) := by
  by_cases ht : ts i=leaf
  · have hr : (ts i).rootDart=none := by rw [ht];rfl
    rw [hr]
    rfl
  · obtain ⟨a,L,ha,hL⟩ := root_and_head (ts i) ht
    rw [ha,Option.map_some,Option.getD_some]
    apply hf
    rw [(branch c ts).matching.distance_comm,child_distance_sum c ts i (nextSlot c i) a a L hL]
    simp only [StackMatching.distance,SimpleGraph.edist_self,add_zero]

/-- Exact original degree incidence counting. The extra preorder root has
one additional root atom; no size-biased measure is postulated. -/
theorem sum_poles {A : Type*} [AddCommMonoid A] (t : CoreTree) (f : t.Dart → A)
    (hf : t.VertexConstant f) (r : A) :
    (∑ v : t.Node,((t.pole v).map f).getD r)=
      (t.rootDart.map f).getD r+∑ d : t.Dart,f d := by
  induction t generalizing r with
  | leaf =>
    change Empty → A at f
    change (∑ _v : PUnit,r)=r+∑ d : Empty,f d
    simp only [Fintype.sum_unique,Fintype.sum_empty,add_zero]
  | branch c ts ih =>
    change (Fin c.val.length ⊕ (Σ i : Fin c.val.length,(ts i).Dart)) → A at f
    change (∑ v : PUnit ⊕ (Σ i : Fin c.val.length,(ts i).Node),_)=_
    rw [Fintype.sum_sum_type,Fintype.sum_sigma]
    simp only [Fintype.sum_unique,pole,rootDart]
    have hx (i : Fin c.val.length) :
        (∑ v : (ts i).Node,f (childPole c ts i v))=
          f (coreDart ts (nextSlot c i))+∑ d : (ts i).Dart,f (childDart ts i d) := by
      have hh := ih i (f ∘ childDart ts i) (child_vertexConstant c ts f hf i)
        (f (coreDart ts (nextSlot c i)))
      have hp (v : (ts i).Node) : f (childPole c ts i v)=
          (((ts i).pole v).map (f ∘ childDart ts i)).getD (f (coreDart ts (nextSlot c i))) := by
        unfold childPole
        cases (ts i).pole v <;> rfl
      simp_rw [hp]
      exact hh.trans (congrArg (fun z => z+∑ d : (ts i).Dart,f (childDart ts i d))
        (child_root_value c ts f hf i))
    change f (coreDart ts c.entry)+(∑ i,∑ v,f (childPole c ts i v))=
      f (coreDart ts c.entry)+∑ d : Fin c.val.length ⊕ (Σ i : Fin c.val.length,(ts i).Dart),f d
    simp_rw [hx]
    rw [Finset.sum_add_distrib,Fintype.sum_sum_type,Fintype.sum_sigma]
    congr 1
    congr 1
    exact Equiv.sum_comp (List.finRange c.val.length).formPerm (f ∘ coreDart ts)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators ENNReal
namespace FKCRT.PermutationWedge
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Exact quotient-graph relabelling for arbitrary finite dart carriers. -/
def dartVertexEquiv (f : α ≃ β) {p : Perm α} {q : Perm β}
    (hp : ∀ x,q (f x)=f (p x)) : Vertex p ≃ Vertex q :=
  Quotient.congr f (sameCycle_embedding f f.injective hp)

lemma dartVertexEquiv_apply (f : α ≃ β) {p : Perm α} {q : Perm β}
    (hp : ∀ x,q (f x)=f (p x)) (x : α) :
    dartVertexEquiv f hp (vertex p x)=vertex q (f x) := rfl

def dartGraphIso (f : α ≃ β) {p e : Perm α} {q a : Perm β}
    (hp : ∀ x,q (f x)=f (p x)) (he : ∀ x,a (f x)=f (e x)) :
    dartGraph e p ≃g dartGraph a q where
  toEquiv := dartVertexEquiv f hp
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hn,h⟩
      refine ⟨fun hh => hn (congrArg (dartVertexEquiv f hp) hh),?_⟩
      have go (x y : Vertex p) (d : β)
          (hx : vertex q d=dartVertexEquiv f hp x)
          (hy : vertex q (a d)=dartVertexEquiv f hp y) :
          ∃ z,vertex p z=x ∧ vertex p (e z)=y := by
        refine ⟨f.symm d,(dartVertexEquiv f hp).injective ?_,(dartVertexEquiv f hp).injective ?_⟩
        · simpa only [dartVertexEquiv_apply,Equiv.apply_symm_apply] using hx
        · rw [dartVertexEquiv_apply,← he,Equiv.apply_symm_apply]
          exact hy
      rcases h with ⟨d,hx,hy⟩|⟨d,hy,hx⟩
      · exact Or.inl (go x y d hx hy)
      · exact Or.inr (go y x d hy hx)
    · rintro ⟨hn,h⟩
      refine ⟨fun hh => hn ((dartVertexEquiv f hp).injective hh),?_⟩
      have go (x y : Vertex p) (d : α) (hx : vertex p d=x) (hy : vertex p (e d)=y) :
          ∃ z,vertex q z=dartVertexEquiv f hp x ∧ vertex q (a z)=dartVertexEquiv f hp y := by
        refine ⟨f d,congrArg (dartVertexEquiv f hp) hx,?_⟩
        rw [he]
        exact congrArg (dartVertexEquiv f hp) hy
      rcases h with ⟨d,hx,hy⟩|⟨d,hy,hx⟩
      · exact Or.inl (go x y d hx hy)
      · exact Or.inr (go y x d hy hx)

end FKCRT.PermutationWedge
namespace FKCRT
open Inventory MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma dartGraph_eq_spanning {n : ℕ} (a s : Perm (Dart n)) :
    dartGraph a s=spanningGraph a s Set.univ := by
  ext x y
  change (x≠y ∧ ((∃ d,orbit s d=x ∧ orbit s (a d)=y) ∨
    (∃ d,orbit s d=y ∧ orbit s (a d)=x))) ↔ _
  simp only [spanningGraph,SimpleGraph.fromRel_adj,Set.mem_univ,true_and]

/-- The canonical inverse word has the literal, uniquely determined stack
matching edge and vertex permutations. -/
def matchingCanonical {n : ℕ} (w : SuccessfulWord n)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) : CanonicalTreeMap n where
  a := turns (D.first++D.second)
  s := (List.finRange (2*(n+1))).formPerm*turns D.first
  A := matchingEdges D.first D.second
  valid := matching_map_conditions D.first D.second D.first_arches D.second_arches D.covers
  tour := by
    have hn := D.covers.nodup_iff.mpr (List.nodup_finRange (2*(n+1)))
    rw [partialReversal_matchingEdges D.first D.second hn,mul_assoc,
      turns_self (by rw [endpoints_append] at hn;exact hn.of_append_left),mul_one]

lemma matchingCanonical_word {n : ℕ} (w : SuccessfulWord n)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) :
    (matchingCanonical w D).word=w := by
  apply Subtype.ext
  exact matchingWord_of_matchings w.val D.first D.second D.first_arches D.second_arches
    D.covers D.first_types D.second_types

lemma matchingCanonical_eq {n : ℕ} (w : SuccessfulWord n)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) :
    matchingCanonical w D=(canonicalWordEquiv n).symm w := by
  apply CanonicalTreeMap.word_injective
  exact (matchingCanonical_word w D).trans ((canonicalWordEquiv n).apply_symm_apply w).symm

/-- The quotient representative used by the main statement is a genuine rooted
relabelling of the matching map, not merely a map with the same size or law. -/
theorem matching_rooted_intertwine {n : ℕ} (w : SuccessfulWord n)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) :
    let M := ((rootedWordEquiv n).symm w).1
    ∃ r : Perm (Dart n),r 0=0 ∧ (∀ d,reversal M (r d)=r (D.mate d)) ∧
      (∀ d,rotation M (r d)=r (((List.finRange (2*(n+1))).formPerm*turns D.first) d)) := by
  dsimp only
  let x := (rootedWordEquiv n).symm w
  have hw : (rootedTreeNormal x).word=w := (rootedWordEquiv n).apply_symm_apply w
  have hh : matchingCanonical w D=rootedTreeNormal x :=
    CanonicalTreeMap.word_injective ((matchingCanonical_word w D).trans hw.symm)
  have hi := canonicalizeTree_iso x.1.out x.2.val x.2.property
  change MapIso (rootedTreeNormal x).toMap x.1.out at hi
  rw [← hh] at hi
  exact hi

end FKCRT
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*}

def listDartEquiv (l : List α) (hn : l.Nodup) (hl : ∀ d,d∈l) {N : ℕ}
    (hN : l.length=N) : Fin N ≃ α :=
  (finCongr hN.symm).trans (Equiv.ofBijective l.get
    ⟨List.nodup_iff_injective_get.mp hn,fun d => by
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp (hl d)
      exact ⟨i,hi⟩⟩)

lemma listDartEquiv_get (l : List α) (hn : l.Nodup) (hl : ∀ d,d∈l) {N : ℕ}
    (hN : l.length=N) (i : Fin N) :
    listDartEquiv l hn hl hN i=l[i.val]'(by omega) := rfl

lemma listDartEquiv_list (l : List α) (hn : l.Nodup) (hl : ∀ d,d∈l) {N : ℕ}
    (hN : l.length=N) : (List.finRange N).map (listDartEquiv l hn hl hN)=l := by
  apply List.ext_getElem
  · simp [hN]
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_finRange,listDartEquiv_get,Fin.val_cast]

lemma listDartEquiv_labels (l : List α) (hn : l.Nodup) (hl : ∀ d,d∈l) {N : ℕ}
    (hN : l.length=N) (v : α → TypedLetter) (w : Fin N → TypedLetter)
    (hw : l.map v=List.ofFn w) (i : Fin N) : v (listDartEquiv l hn hl hN i)=w i := by
  have hi : i.val<l.length := by omega
  have hi' : i.val<(l.map v).length := by simpa using hi
  have h := congrArg (fun a : List TypedLetter => a[i.val]?) hw
  simpa only [List.getElem?_eq_getElem hi',List.getElem_map,
    List.getElem?_eq_getElem (show i.val<(List.ofFn w).length by simp),List.getElem_ofFn,
    Option.some.injEq,← listDartEquiv_get l hn hl hN i] using h

variable [DecidableEq α]

/-- Literal finite-word normalization simultaneously intertwines edge and
vertex permutations of the original multigraph. -/
theorem StackMatching.word_intertwine {v : α → TypedLetter} {l : List α}
    (M : StackMatching v l) (hn : l.Nodup) (hl : ∀ d,d∈l) {n : ℕ}
    (w : FKCRT.SuccessfulWord n) (hw : l.map v=List.ofFn w.val)
    (D : StackMatching w.val (List.finRange (2*(n+1)))) :
    ∃ e : FKCRT.Dart n ≃ α,
      (∀ i,M.mate (e i)=e (D.mate i)) ∧
      (∀ i,(l.formPerm*turns M.first) (e i)=
        e (((List.finRange (2*(n+1))).formPerm*turns D.first) i)) := by
  have hN : l.length=2*(n+1) := by
    have h := congrArg List.length hw
    simpa only [List.length_map,List.length_ofFn] using h
  let e := listDartEquiv l hn hl hN
  have he : (List.finRange (2*(n+1))).map e=l := listDartEquiv_list l hn hl hN
  have hv (i : FKCRT.Dart n) (_hi : i∈List.finRange (2*(n+1))) : v (e i)=w.val i :=
    listDartEquiv_labels l hn hl hN v w.val hw i
  let Q := D.map e v hv
  let R : StackMatching v l := he ▸ Q
  have hm : M.mate=Q.mate := (M.unique_mate R hn).trans (Q.cast_mate he)
  have hf : turns M.first=turns Q.first := (M.unique_first R hn).trans
    (congrArg turns (Q.cast_first he))
  refine ⟨e,?_,?_⟩
  · intro i
    rw [hm]
    exact D.map_mate (List.nodup_finRange _) e e.injective v hv i (List.mem_finRange i)
  · intro i
    change l.formPerm (turns M.first (e i))=e ((List.finRange _).formPerm (turns D.first i))
    rw [hf,D.map_first (List.nodup_finRange _) e e.injective v hv]
    rw [← he]
    exact formPerm_map_on _ (List.nodup_finRange _) e e.injective _ (List.mem_finRange _)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- The actual FK representative and the recursively glued literal map are
isomorphic on their original darts, simultaneously for edges and vertices. -/
theorem realized_intertwine (t : CoreTree) {n : ℕ} (w : FKCRT.SuccessfulWord n)
    (hw : t.word=List.ofFn w.val) :
    let M := ((FKCRT.rootedWordEquiv n).symm w).1
    ∃ e : t.Dart ≃ FKCRT.Dart n,
      (∀ d,FKCRT.reversal M (e d)=e (t.matching.mate d)) ∧
      (∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) := by
  let D := StackMatching.ofEmpty (w := w.val) (l := List.finRange (2*(n+1)))
    (by simpa only [← List.ofFn_eq_map] using w.property)
  obtain ⟨e,he,hp⟩ := t.matching.word_intertwine t.darts_nodup t.darts_mem w
    (t.darts_word.trans hw) D
  obtain ⟨r,_hr,hrE,hrV⟩ := FKCRT.matching_rooted_intertwine w D
  refine ⟨e.symm.trans r,?_,?_⟩
  · intro d
    change FKCRT.reversal _ (r (e.symm d))=r (e.symm (t.matching.mate d))
    rw [hrE]
    apply congrArg r
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using (he (e.symm d)).symm
  · intro d
    change FKCRT.rotation _ (r (e.symm d))=r (e.symm ((t.darts.formPerm*turns t.matching.first) d))
    rw [hrV]
    apply congrArg r
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using (hp (e.symm d)).symm

/-- Original all-edge graph distances are preserved exactly by the finite
word/core realization; no block metric is substituted. -/
theorem realized_distance (t : CoreTree) {n : ℕ} (w : FKCRT.SuccessfulWord n)
    (hw : t.word=List.ofFn w.val) :
    let M := ((FKCRT.rootedWordEquiv n).symm w).1
    ∃ e : t.Dart ≃ FKCRT.Dart n,∀ a b,
      ((FKCRT.graph M Set.univ).dist (orbit (FKCRT.rotation M) (e a))
        (orbit (FKCRT.rotation M) (e b)):ℝ)=t.realDistance a b := by
  obtain ⟨e,he,hp⟩ := t.realized_intertwine w hw
  refine ⟨e,fun a b => ?_⟩
  have hh := dartGraph_embedding_edist e e.injective hp he a b
  rw [FKCRT.dartGraph_eq_spanning] at hh
  change (FKCRT.graph _ Set.univ).edist _ _=t.matching.distance a b at hh
  change (FKCRT.graph ((FKCRT.rootedWordEquiv n).symm w).1 Set.univ).edist
    (orbit (FKCRT.rotation _) (e a)) (orbit (FKCRT.rotation _) (e b))=t.matching.distance a b at hh
  rw [t.distance_eq_nat a b] at hh
  have hr : (FKCRT.graph ((FKCRT.rootedWordEquiv n).symm w).1 Set.univ).Reachable
      (orbit (FKCRT.rotation _) (e a)) (orbit (FKCRT.rotation _) (e b)) := by
    apply SimpleGraph.edist_ne_top_iff_reachable.mp
    rw [hh]
    exact ENat.natCast_ne_top _
  rw [← SimpleGraph.Reachable.coe_dist_eq_edist hr] at hh
  dsimp only [realDistance]
  exact_mod_cast hh

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma pole_root (t : CoreTree) : t.pole t.root=t.rootDart := by cases t <;> rfl

/-- Preorder nodes indexed at the true total word length. -/
def wordNodeEquiv (t : CoreTree) : t.Node ≃ Fin (t.word.length+1) :=
  t.nodeEquiv.trans (finCongr t.labels_length)

lemma wordNodeEquiv_root (t : CoreTree) : t.wordNodeEquiv t.root=0 := by
  apply Fin.ext
  exact t.nodeIndex_root

/-- Dropping precisely the preorder root leaves the exact multiset of all
original dart vertices. This is the degree measure's incidence identity. -/
theorem sum_nonroot_poles {A : Type*} [AddCancelCommMonoid A]
    (t : CoreTree) (f : t.Dart → A) (hf : t.VertexConstant f) (r : A) :
    (∑ i : Fin t.word.length,((t.pole (t.wordNodeEquiv.symm i.succ)).map f).getD r)=
      ∑ d : t.Dart,f d := by
  have hh := t.sum_poles f hf r
  have hs := t.wordNodeEquiv.symm.sum_comp (fun v => ((t.pole v).map f).getD r)
  rw [Fin.sum_univ_succ] at hs
  have hr : t.wordNodeEquiv.symm 0=t.root :=
    t.wordNodeEquiv.symm_apply_eq.mpr t.wordNodeEquiv_root.symm
  rw [hr,t.pole_root] at hs
  exact add_left_cancel (hs.trans hh)

lemma vertexConstant_of_intertwine {A : Type*} (t : CoreTree) {n : ℕ}
    (M : FKCRT.RootedMap n) (e : t.Dart ≃ FKCRT.Dart n)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d))
    (f : FKCRT.Vertex M → A) :
    t.VertexConstant (fun d => f (orbit (FKCRT.rotation M) (e d))) := by
  intro a b hab
  change (dartGraph t.matching.mate (t.darts.formPerm*turns t.matching.first)).edist
    (vertex _ a) (vertex _ b)=0 at hab
  have hh := SimpleGraph.edist_eq_zero_iff.mp hab
  exact congrArg (f ∘ dartVertexEquiv e hp) hh

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

def realizedPole (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (v : t.Node) : FKCRT.Vertex M :=
  ((t.pole v).map (fun d => orbit (FKCRT.rotation M) (e d))).getD (orbit (FKCRT.rotation M) 0)

def nonrootVertex (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (i : Fin t.word.length) : FKCRT.Vertex M :=
  t.realizedPole M e (t.wordNodeEquiv.symm i.succ)

lemma realizedPole_some (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (v : t.Node) (a : t.Dart) (ha : t.pole v=some a) :
    t.realizedPole M e v=orbit (FKCRT.rotation M) (e a) := by
  simp only [realizedPole,ha,Option.map_some,Option.getD_some]

/-- Exact uniform nonroot-preorder mass equals original uniform dart mass.
The finite root atom is cancelled, not ignored asymptotically. -/
theorem nonroot_dirac_eq (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) :
    let : MeasurableSpace (FKCRT.Vertex M) := ⊤
    (∑ i : Fin t.word.length,Measure.dirac (t.nonrootVertex M e i))=
      ∑ d : FKCRT.Dart n,Measure.dirac (orbit (FKCRT.rotation M) d) := by
  let : MeasurableSpace (FKCRT.Vertex M) := ⊤
  let r := orbit (FKCRT.rotation M) 0
  let f := fun d : t.Dart => Measure.dirac (orbit (FKCRT.rotation M) (e d))
  have hf : t.VertexConstant f := t.vertexConstant_of_intertwine M e hp Measure.dirac
  have hh := t.sum_poles f hf (Measure.dirac r)
  have hs := t.wordNodeEquiv.symm.sum_comp (fun v => ((t.pole v).map f).getD (Measure.dirac r))
  rw [Fin.sum_univ_succ] at hs
  have hr : t.wordNodeEquiv.symm 0=t.root :=
    t.wordNodeEquiv.symm_apply_eq.mpr t.wordNodeEquiv_root.symm
  rw [hr,t.pole_root] at hs
  have hz := hs.trans hh
  have hv (v : t.Node) : ((t.pole v).map f).getD (Measure.dirac r)=
      Measure.dirac (t.realizedPole M e v) := by
    dsimp [realizedPole]
    cases t.pole v <;> rfl
  have hroot : (t.rootDart.map f).getD (Measure.dirac r)=Measure.dirac (t.realizedPole M e t.root) := by
    rw [← t.pole_root]
    exact hv t.root
  rw [hroot] at hz
  simp_rw [hv] at hz
  have hsum : (∑ d : t.Dart,f d)=∑ d : FKCRT.Dart n,Measure.dirac (orbit (FKCRT.rotation M) d) :=
    e.sum_comp (fun d => Measure.dirac (orbit (FKCRT.rotation M) d))
  rw [hsum] at hz
  apply Measure.ext
  intro s hs
  have hh' := congrArg (fun μ : Measure (FKCRT.Vertex M) => μ s) hz
  simp only [Measure.add_apply] at hh'
  apply (ENNReal.add_left_inj (measure_ne_top (Measure.dirac (t.realizedPole M e t.root)) s)).mp
  simpa only [add_comm,nonrootVertex] using hh'

/-- Every original vertex is reached by a nonroot pole, even in the presence
of loops and coincident poles. -/
theorem nonrootVertex_surjective (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n)
    (hp : ∀ d,FKCRT.rotation M (e d)=e ((t.darts.formPerm*turns t.matching.first) d)) :
    Function.Surjective (t.nonrootVertex M e) := by
  intro v
  classical
  by_contra h
  have hn : ∀ i,t.nonrootVertex M e i≠v := by simpa only [not_exists] using h
  let : MeasurableSpace (FKCRT.Vertex M) := ⊤
  have hm := congrArg (fun μ : Measure (FKCRT.Vertex M) => μ {v}) (t.nonroot_dirac_eq M e hp)
  have hz : (∑ i : Fin t.word.length,Measure.dirac (t.nonrootVertex M e i)) {v}=0 := by
    simp only [Measure.finsetSum_apply,Measure.dirac_apply' _ (MeasurableSet.singleton v),
      Set.indicator_apply,Set.mem_singleton_iff]
    simp [hn]
  rw [hz] at hm
  obtain ⟨d,hd⟩ := Quotient.mk_surjective v
  have hh : (1:ℝ≥0∞)≤(∑ a : FKCRT.Dart n,Measure.dirac (orbit (FKCRT.rotation M) a)) {v} := by
    rw [Measure.finsetSum_apply]
    calc
      1=Measure.dirac (orbit (FKCRT.rotation M) d) {v} := by
        rw [show orbit (FKCRT.rotation M) d=v from hd]
        simp
      _≤∑ a : FKCRT.Dart n,Measure.dirac (orbit (FKCRT.rotation M) a) {v} :=
        Finset.single_le_sum (f := fun a : FKCRT.Dart n =>
          Measure.dirac (orbit (FKCRT.rotation M) a) {v})
          (fun _ _ => by positivity) (Finset.mem_univ d)
  rw [← hm] at hh
  exact not_le_of_gt zero_lt_one hh

end FKCRT.Inventory.CoreTree
end

end OAI
