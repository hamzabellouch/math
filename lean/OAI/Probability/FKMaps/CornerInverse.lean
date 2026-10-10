import OAI.Probability.FKMaps.CornerInsertion

namespace OAI

noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.Chords
variable {N K : ℕ}

/-- Transport a core matching through its strictly increasing position map. -/
def openerEmbedding (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (h : ∀ i,a (e i)=e (b i)) : Opener b ↪ Opener a where
  toFun x := ⟨e x.val,by rw [h]; exact e.strictMono x.property⟩
  inj' := by intro x y hxy; exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

lemma cross_embedding (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (h : ∀ i,a (e i)=e (b i)) (x y : Opener b) :
    Cross a (openerEmbedding a b e h x) (openerEmbedding a b e h y) ↔ Cross b x y := by
  change ((e x.val<e y.val ∧ e y.val<a (e x.val) ∧ a (e x.val)<a (e y.val)) ∨
    (e y.val<e x.val ∧ e x.val<a (e y.val) ∧ a (e y.val)<a (e x.val))) ↔ _
  simp only [h,e.lt_iff_lt,Cross]

def graphHom (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (h : ∀ i,a (e i)=e (b i)) : graph b →g graph a where
  toFun := openerEmbedding a b e h
  map_rel' := fun hx => (cross_embedding a b e h _ _).mpr hx

lemma opener_range (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (h : ∀ i,a (e i)=e (b i)) (x : Opener a)
    (hx : x.val∈Set.range e) : ∃ y : Opener b,openerEmbedding a b e h y=x := by
  obtain ⟨i,hi⟩ := hx
  have hp : i<b i := by
    apply e.lt_iff_lt.mp
    rw [← h,hi]
    exact x.property
  exact ⟨⟨i,hp⟩,Subtype.ext hi⟩

/-- Once every unmarked interval is matched internally, the core mask is
also matched internally; this is forced by the actual involution. -/
lemma core_closed_of_chunks (a : Perm (Fin N)) (ha : Function.Involutive a)
    (p : Fin N→Bool) (hN : 0<N) (hp : p ⟨0,hN⟩=true)
    (hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2) :
    ∀ d,p (a d)=p d := by
  have hunmarked : ∀ d,p d=false → p (a d)=false := by
    intro d hd
    obtain ⟨x,hx,hdx⟩ := unmarked_in_chunk p hN hp hd
    exact (CornerSplit.marked_corners p (List.finRange N) x hx).2 _ (hchunks x hx d hdx)
  intro d
  cases hd : p d with
  | false => exact hunmarked d hd
  | true =>
    cases had : p (a d) with
    | true => rfl
    | false =>
      have hh := hunmarked (a d) had
      rw [ha,hd] at hh
      cases hh

/-- Inserting internally matched words in the corners of a connected core
leaves precisely that core as the root crossing component. -/
theorem root_component_insertion (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (b : Perm (Fin K)) (e : Fin K ↪o Fin N)
    (hmatch : ∀ i,a (e i)=e (b i)) (r : Opener b) (hr : (e r.val).val=0)
    (hconnected : ∀ x : Opener b,(graph b).Reachable r x)
    (hchunks : ∀ x∈(CornerSplit.split (fun d => decide (d∈Set.range e)) (List.finRange N)).2,
      ∀ d∈x.2,a d∈x.2) :
    componentDarts a (openerEmbedding a b e hmatch r)=Finset.univ.filter (fun d => d∈Set.range e) := by
  classical
  let p : Fin N→Bool := fun d => decide (d∈Set.range e)
  have hp : p (e r.val)=true := decide_eq_true (Set.mem_range_self _)
  have hN : 0<N := (e r.val).pos
  have hp0 : p ⟨0,hN⟩=true := by
    have he : (⟨0,hN⟩ : Fin N)=e r.val := Fin.ext hr.symm
    rw [he]; exact hp
  have hcore := core_closed_of_chunks a ha p hN hp0 hchunks
  have he := root_component_of_core a ha hf p (openerEmbedding a b e hmatch r) hr hp hcore hchunks
    (by
      intro x hx
      obtain ⟨y,rfl⟩ := opener_range a b e hmatch x (of_decide_eq_true hx)
      exact (hconnected y).map (graphHom a b e hmatch))
  simpa only [p,decide_eq_true_eq] using he

end FKCRT.Chords
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.CornerSplit
lemma skeleton_sublist {α : Type*} (l : List (α×List α)) :
    (l.map Prod.fst).Sublist (join l) := by
  induction l with
  | nil => exact .refl _
  | cons x l ih =>
    change (x.1::l.map Prod.fst).Sublist (x.1::(x.2++join l))
    exact (ih.trans (List.sublist_append_right _ _)).cons_cons _
end FKCRT.CornerSplit
namespace FKCRT.MapCycles
variable {α : Type*}

lemma scanArches_corners_subset (f : α→Option Bool) (l : List (α×List α))
    (G : α×List α→List (α×α))
    (hg : ∀ x∈l,∀ S,scanArches f x.2 S=some (S,G x))
    {E F : List (α×α)}
    (hcore : scanArches f (l.map Prod.fst) []=some ([],E))
    (hfull : scanArches f (CornerSplit.join l) []=some ([],F)) :
    ∀ e∈E,e∈F := by
  obtain ⟨H,hH,hperm⟩ := scanArches_corners f l G hg hcore
  have he : H=F := congrArg Prod.snd (Option.some.inj (hH.symm.trans hfull))
  rw [he] at hperm
  intro e he
  exact hperm.mem_iff.mpr (List.mem_append_left _ he)

end FKCRT.MapCycles
namespace FKCRT.Inventory
open MapCycles
variable {α : Type*} [DecidableEq α]

lemma typed_corner_scans (w : α→TypedLetter) (l : List (α×List α))
    (hn : (CornerSplit.join l).Nodup)
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some []) (c : Bool) :
    ∃ G : α×List α→List (α×α),
      ∀ x∈l,∀ S,scanArches (fun a => colorInstruction c (w a)) x.2 S=some (S,G x) := by
  have hex : ∀ x∈l,∃ E,∀ S,scanArches (fun a => colorInstruction c (w a)) x.2 S=some (S,E) := by
    intro x hx
    have hxnodup : x.2.Nodup := (List.nodup_cons.mp ((List.nodup_flatMap.mp hn).1 x hx)).2
    obtain ⟨E,hE,_⟩ := empty_typed_scan w x.2 hxnodup (hw x hx) c
    exact ⟨E,hE⟩
  classical
  let G := fun x => if hx : x∈l then Classical.choose (hex x hx) else []
  refine ⟨G,?_⟩
  intro x hx S
  simpa only [G,dite_eq_left hx] using (Classical.choose_spec (hex x hx)) S

/-- Actual core pairs remain the same pairs after inserting *arbitrary*
successful corner words. This controls the adaptive matching itself. -/
theorem corner_core_pairs (w : α→TypedLetter) (l : List (α×List α))
    (hn : (CornerSplit.join l).Nodup)
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some [])
    (E F C D : List (α×α))
    (hE : Arches (CornerSplit.join l) E) (hF : Arches (CornerSplit.join l) F)
    (hc : (endpoints (E++F)).Perm (CornerSplit.join l))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (hC : Arches (l.map Prod.fst) C) (hD : Arches (l.map Prod.fst) D)
    (hd : (endpoints (C++D)).Perm (l.map Prod.fst))
    (htC : ∀ e∈C,w e.1=.burger true ∧ w e.2=.order true)
    (htD : ∀ e∈D,w e.1=.burger false ∧ w e.2=.order false) :
    (∀ e∈C,e∈E) ∧ (∀ e∈D,e∈F) := by
  have hfull := matching_color_coverage w (CornerSplit.join l) E F hc htE htF
  have hcore := matching_color_coverage w (l.map Prod.fst) C D hd htC htD
  have hncore := hn.sublist (CornerSplit.skeleton_sublist l)
  constructor
  · obtain ⟨G,hG⟩ := typed_corner_scans w l hn hw true
    obtain ⟨Ec,hEc,hEcC⟩ := hC.scan hncore (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htC e he).1,(htC e he).2]) hcore.1 []
    obtain ⟨Ef,hEf,hEfE⟩ := hE.scan hn (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hfull.1 []
    intro e he
    exact hEfE.mem_iff.mp (scanArches_corners_subset _ l G hG hEc hEf e (hEcC.mem_iff.mpr he))
  · obtain ⟨G,hG⟩ := typed_corner_scans w l hn hw false
    obtain ⟨Dc,hDc,hDcD⟩ := hD.scan hncore (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htD e he).1,(htD e he).2]) hcore.2 []
    obtain ⟨Df,hDf,hDfF⟩ := hF.scan hn (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hfull.2 []
    intro e he
    exact hDfF.mem_iff.mp (scanArches_corners_subset _ l G hG hDc hDf e (hDcD.mem_iff.mpr he))

/-- The exact matching restriction, stated on every actual core endpoint. -/
theorem corner_core_turns (w : α→TypedLetter) (l : List (α×List α))
    (hn : (CornerSplit.join l).Nodup)
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some [])
    (E F C D : List (α×α))
    (hE : Arches (CornerSplit.join l) E) (hF : Arches (CornerSplit.join l) F)
    (hc : (endpoints (E++F)).Perm (CornerSplit.join l))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (hC : Arches (l.map Prod.fst) C) (hD : Arches (l.map Prod.fst) D)
    (hd : (endpoints (C++D)).Perm (l.map Prod.fst))
    (htC : ∀ e∈C,w e.1=.burger true ∧ w e.2=.order true)
    (htD : ∀ e∈D,w e.1=.burger false ∧ w e.2=.order false) :
    ∀ a∈l.map Prod.fst,turns (E++F) a=turns (C++D) a := by
  obtain ⟨hCE,hDF⟩ := corner_core_pairs w l hn hw E F C D hE hF hc htE htF hC hD hd htC htD
  have hsub : ∀ e∈C++D,e∈E++F := by
    intro e he
    rcases List.mem_append.mp he with he|he
    · exact List.mem_append_left _ (hCE e he)
    · exact List.mem_append_right _ (hDF e he)
  have hnp := hc.nodup_iff.mpr hn
  have hncore : (endpoints (C++D)).Nodup :=
    hd.nodup_iff.mpr (hn.sublist (CornerSplit.skeleton_sublist l))
  intro a ha
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp (hd.mem_iff.mpr ha)
  · rw [(turns_pair hnp e (hsub e he)).1,(turns_pair hncore e he).1]
  · rw [(turns_pair hnp e (hsub e he)).2,(turns_pair hncore e he).2]

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.CornerSplit
variable {α : Type*}

lemma join_perm_parts (l : List (α×List α)) :
    (join l).Perm (l.map Prod.fst++l.flatMap Prod.snd) := by
  induction l with
  | nil => exact .refl _
  | cons x l ih =>
    change (x.1::(x.2++join l)).Perm (x.1::(l.map Prod.fst++(x.2++l.flatMap Prod.snd)))
    apply List.Perm.cons
    apply (ih.append_left x.2).trans
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁:=x.2) (l₂:=l.map Prod.fst)).append_right (l.flatMap Prod.snd)

lemma own_mask {α : Type*} [DecidableEq α] (l : List (α×List α)) (hn : (join l).Nodup) :
    ∀ x∈l,decide (x.1∈l.map Prod.fst)=true ∧
      ∀ d∈x.2,decide (d∈l.map Prod.fst)=false := by
  have hh := (join_perm_parts l).nodup_iff.mp hn
  intro x hx
  refine ⟨decide_eq_true (List.mem_map.mpr ⟨x,hx,rfl⟩),?_⟩
  intro d hd
  apply decide_eq_false
  intro hm
  exact (List.nodup_append.mp hh).2.2 d hm d (List.mem_flatMap.mpr ⟨x,hx,hd⟩) rfl

end FKCRT.CornerSplit
namespace FKCRT.Chords
variable {N : ℕ}

def partialOpener (a b : Perm (Fin N)) (p : Fin N→Bool)
    (hsupport : ∀ d,b d≠d → p d=true)
    (hmatch : ∀ d,p d=true → a d=b d) (x : Opener b) : Opener a :=
  ⟨x.val,by rw [hmatch _ (hsupport _ (ne_of_gt x.property))];exact x.property⟩

def partialGraphHom (a b : Perm (Fin N)) (p : Fin N→Bool)
    (hsupport : ∀ d,b d≠d → p d=true)
    (hmatch : ∀ d,p d=true → a d=b d) : graph b →g graph a where
  toFun := partialOpener a b p hsupport hmatch
  map_rel' := by
    intro x y h
    change Cross a (partialOpener a b p hsupport hmatch x) (partialOpener a b p hsupport hmatch y)
    change (x.val<y.val ∧ y.val<a x.val ∧ a x.val<a y.val) ∨
      (y.val<x.val ∧ x.val<a y.val ∧ a y.val<a x.val)
    rw [hmatch _ (hsupport _ (ne_of_gt x.property)),hmatch _ (hsupport _ (ne_of_gt y.property))]
    exact h

theorem root_component_partial (a b : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (p : Fin N→Bool)
    (hsupport : ∀ d,b d≠d → p d=true) (hmatch : ∀ d,p d=true → a d=b d)
    (r : Opener b) (hr : r.val.val=0)
    (hconnected : ∀ x : Opener b,(graph b).Reachable r x)
    (hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2) :
    componentDarts a (partialOpener a b p hsupport hmatch r)=Finset.univ.filter (fun d => p d=true) := by
  have hp := hsupport r.val (ne_of_gt r.property)
  have hN : 0<N := r.val.pos
  have hp0 : p ⟨0,hN⟩=true := by
    have he : (⟨0,hN⟩ : Fin N)=r.val := Fin.ext hr.symm
    rw [he];exact hp
  apply root_component_of_core a ha hf p (partialOpener a b p hsupport hmatch r) hr hp
    (core_closed_of_chunks a ha p hN hp0 hchunks) hchunks
  intro x hx
  let y : Opener b := ⟨x.val,by rw [← hmatch _ hx];exact x.property⟩
  exact (hconnected y).map (partialGraphHom a b p hsupport hmatch)

end FKCRT.Chords
namespace FKCRT.Inventory
open MapCycles Chords
variable {N : ℕ}

/-- Exact inverse of root-component extraction. Connectivity here specifies
which finite words are cores; all corner matching and separation facts are
proved from the original stack algorithm. -/
theorem connected_corner_inverse (w : Fin N→TypedLetter)
    (l : List (Fin N×List (Fin N))) (hjoin : CornerSplit.join l=List.finRange N)
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some [])
    (E F C D : List (Fin N×Fin N))
    (hE : Arches (List.finRange N) E) (hF : Arches (List.finRange N) F)
    (hc : (endpoints (E++F)).Perm (List.finRange N))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (hC : Arches (l.map Prod.fst) C) (hD : Arches (l.map Prod.fst) D)
    (hd : (endpoints (C++D)).Perm (l.map Prod.fst))
    (htC : ∀ e∈C,w e.1=.burger true ∧ w e.2=.order true)
    (htD : ∀ e∈D,w e.1=.burger false ∧ w e.2=.order false)
    (r : Opener (turns (C++D))) (hr : r.val.val=0)
    (hconnected : ∀ x : Opener (turns (C++D)),(Chords.graph (turns (C++D))).Reachable r x) :
    ∃ R : Opener (turns (E++F)),R.val=r.val ∧ rootSplit (turns (E++F)) R=l := by
  classical
  let a := turns (E++F)
  let b := turns (C++D)
  let p : Fin N→Bool := fun d => decide (d∈l.map Prod.fst)
  have hn : (CornerSplit.join l).Nodup := hjoin.symm ▸ List.nodup_finRange N
  have hnp : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange N)
  have hnc : (endpoints (C++D)).Nodup := hd.nodup_iff.mpr (hn.sublist (CornerSplit.skeleton_sublist l))
  have hs : CornerSplit.split p (List.finRange N)=([],l) := by
    rw [← hjoin];exact CornerSplit.split_join p l (CornerSplit.own_mask l hn)
  have hmatch : ∀ d,p d=true → a d=b d := by
    intro d hd'
    exact corner_core_turns w l hn hw E F C D (hjoin.symm ▸ hE) (hjoin.symm ▸ hF)
      (hjoin.symm ▸ hc) htE htF hC hD hd htC htD d (of_decide_eq_true hd')
  have hsupport : ∀ d,b d≠d → p d=true := by
    intro d hbd
    apply decide_eq_true
    apply hd.mem_iff.mp
    by_contra hh
    exact hbd (turns_fixed_of_notMem hh)
  have hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2 := by
    intro x hx
    have hxl : x∈l := by simpa only [hs] using hx
    obtain ⟨u,v,he,_⟩ := CornerSplit.located p (List.finRange N) x hx
    have he' : List.finRange N=(u++[x.1])++(x.2++v) := by simpa only [List.append_assoc,List.singleton_append] using he
    exact empty_interval_matching_closed w (u++[x.1]) x.2 v
      (he' ▸ List.nodup_finRange N) E F (he' ▸ hE) (he' ▸ hF) (he' ▸ hc) htE htF (hw x hxl)
  have hf : ∀ d,a d≠d := by
    intro d hh
    exact (turns_eq_self_iff hnp d).mp hh (hc.mem_iff.mpr (List.mem_finRange d))
  let R := partialOpener a b p hsupport hmatch r
  have hcomp := root_component_partial a b (turns_involutive hnp) hf p hsupport hmatch r hr hconnected hchunks
  refine ⟨R,rfl,?_⟩
  have hmask : (fun d => decide (d∈componentDarts a R))=p := by
    funext d
    rw [hcomp]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.decide_eq_true]
  change (CornerSplit.split (fun d => decide (d∈componentDarts a R)) (List.finRange N)).2=l
  rw [hmask,hs]

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α β : Type*}

lemma Arches.map {l : List α} {E : List (α×α)} (h : Arches l E) (f : α→β) :
    Arches (l.map f) (E.map (Prod.map f f)) := by
  induction h with
  | nil => exact .nil
  | skip a h ih => exact .skip (f a) ih
  | pair a b hL hR ihL ihR =>
    simpa only [List.map_cons,List.map_append,Prod.map_apply] using Arches.pair (f a) (f b) ihL ihR

lemma endpoints_map (f : α→β) (E : List (α×α)) :
    endpoints (E.map (Prod.map f f))=(endpoints E).map f := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    rcases e with ⟨a,b⟩
    simp only [List.map_cons,endpoints_cons,Prod.map_apply,ih]

lemma Arches.filter {l : List α} {E : List (α×α)} (h : Arches l E) (p : α→Bool)
    (hp : ∀ e∈E,p e.1=p e.2) :
    Arches (l.filter p) (E.filter (fun e => p e.1)) := by
  induction h with
  | nil => exact .nil
  | @skip a l E h ih =>
    cases ha : p a with
    | true => simpa only [List.filter_cons,ha,ite_true] using Arches.skip a (ih hp)
    | false => simpa only [List.filter_cons,ha,Bool.false_eq_true,ite_false] using ih hp
  | @pair a b L R E F hL hR ihL ihR =>
    have hab := hp (a,b) (List.mem_cons_self)
    have hE := ihL (fun e he => hp e (List.mem_cons_of_mem _ (List.mem_append_left _ he)))
    have hF := ihR (fun e he => hp e (List.mem_cons_of_mem _ (List.mem_append_right _ he)))
    cases ha : p a with
    | true =>
      have hb : p b=true := hab.symm.trans ha
      simpa only [List.filter_cons,List.filter_append,ha,hb,ite_true] using Arches.pair a b hE hF
    | false =>
      have hb : p b=false := hab.symm.trans ha
      simpa only [List.filter_cons,List.filter_append,ha,hb,Bool.false_eq_true,ite_false] using hE.append hF

lemma endpoints_filter (p : α→Bool) (E : List (α×α))
    (hp : ∀ e∈E,p e.1=p e.2) :
    endpoints (E.filter (fun e => p e.1))=(endpoints E).filter p := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    have he := hp e (List.mem_cons_self)
    have hh := ih (fun f hf => hp f (List.mem_cons_of_mem _ hf))
    cases ha : p e.1 <;> have hb := he.symm.trans ha <;>
      simp only [List.filter_cons,endpoints_cons,ha,hb,Bool.false_eq_true,ite_true,ite_false,hh]

end FKCRT.MapCycles
namespace FKCRT.Inventory
open MapCycles
variable {α : Type*} [DecidableEq α]

/-- Restrict the actual successful word to any union of its matched pairs.
This includes both its root component and each real corner interval. -/
theorem matching_subword_empty (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (E F : List (α×α)) (hE : Arches l E) (hF : Arches l F)
    (hc : (endpoints (E++F)).Perm l)
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (p : α→Bool) (hp : ∀ d∈l,p (turns (E++F) d)=p d) :
    stackTypedRun ((l.filter p).map w) []=some [] := by
  have hnp := hc.nodup_iff.mpr hn
  have heq : ∀ e∈E++F,p e.1=p e.2 := by
    intro e he
    have hm : e.1∈l := hc.mem_iff.mp (mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩)
    have hh := hp e.1 hm
    rw [(turns_pair hnp e he).1] at hh
    exact hh.symm
  have he : ∀ e∈E,p e.1=p e.2 := fun e he => heq e (List.mem_append_left _ he)
  have hf : ∀ e∈F,p e.1=p e.2 := fun e he => heq e (List.mem_append_right _ he)
  apply typedRun_of_matchings w (l.filter p) (hn.filter _)
    (E.filter (fun e => p e.1)) (F.filter (fun e => p e.1)) (hE.filter p he) (hF.filter p hf)
  · rw [← List.filter_append,endpoints_filter p (E++F) heq]
    exact hc.filter p
  · intro e he';exact htE e (List.mem_filter.mp he').1
  · intro e he';exact htF e (List.mem_filter.mp he').1

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma turns_map_on (f : α→β) (hf : Function.Injective f) (E : List (α×α))
    (hn : (endpoints E).Nodup) (i : α) (hi : i∈endpoints E) :
    turns (E.map (Prod.map f f)) (f i)=f (turns E i) := by
  have hn' : (endpoints (E.map (Prod.map f f))).Nodup := by
    rw [endpoints_map];exact hn.map hf
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hi
  · have hh := (turns_pair hn' (Prod.map f f e) (List.mem_map.mpr ⟨e,he,rfl⟩)).1
    simpa only [Prod.map_fst,Prod.map_snd,(turns_pair hn e he).1] using hh
  · have hh := (turns_pair hn' (Prod.map f f e) (List.mem_map.mpr ⟨e,he,rfl⟩)).2
    simpa only [Prod.map_fst,Prod.map_snd,(turns_pair hn e he).2] using hh

end FKCRT.MapCycles
namespace FKCRT.Inventory
open MapCycles Chords
variable {α β : Type*}

/-- A certificate for the actual two stack matchings of a finite typed word.
The matching uniqueness theorem makes its induced mate choice-independent. -/
structure StackMatching (w : α→TypedLetter) (l : List α) where
  first : List (α×α)
  second : List (α×α)
  first_arches : Arches l first
  second_arches : Arches l second
  covers : (endpoints (first++second)).Perm l
  first_types : ∀ e∈first,w e.1=.burger true ∧ w e.2=.order true
  second_types : ∀ e∈second,w e.1=.burger false ∧ w e.2=.order false

namespace StackMatching
variable {w : α→TypedLetter} {l : List α}

def ofEmpty (hw : stackTypedRun (l.map w) []=some []) : StackMatching w l :=
  let h := ordered_matchings w l hw
  ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.1,h.choose_spec.choose_spec.2.2.1,
    h.choose_spec.choose_spec.2.2.2.1,h.choose_spec.choose_spec.2.2.2.2⟩

def mate [DecidableEq α] (M : StackMatching w l) : Perm α := turns (M.first++M.second)

lemma empty [DecidableEq α] (M : StackMatching w l) (hn : l.Nodup) :
    stackTypedRun (l.map w) []=some [] :=
  typedRun_of_matchings w l hn M.first M.second M.first_arches M.second_arches
    M.covers M.first_types M.second_types

lemma unique_mate [DecidableEq α] (M P : StackMatching w l) (hn : l.Nodup) : M.mate=P.mate := by
  obtain ⟨hE,hF⟩ := typed_matchings_unique w l hn M.first M.second P.first P.second
    M.first_arches M.second_arches P.first_arches P.second_arches M.covers P.covers
    M.first_types M.second_types P.first_types P.second_types
  exact turns_perm (hE.append hF) (M.covers.nodup_iff.mpr hn)

lemma involutive [DecidableEq α] (M : StackMatching w l) (hn : l.Nodup) :
    Function.Involutive M.mate := turns_involutive (M.covers.nodup_iff.mpr hn)

lemma no_fixed [DecidableEq α] (M : StackMatching w l) (hn : l.Nodup) (i : α) (hi : i∈l) :
    M.mate i≠i := by
  intro hh
  exact (turns_eq_self_iff (M.covers.nodup_iff.mpr hn) i).mp hh (M.covers.mem_iff.mpr hi)

lemma endpoints_mem (M : StackMatching w l) (e : α×α) (he : e∈M.first++M.second) :
    e.1∈l ∧ e.2∈l :=
  ⟨M.covers.mem_iff.mp (mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩),
   M.covers.mem_iff.mp (mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩)⟩

def map (M : StackMatching w l) (f : α→β) (v : β→TypedLetter)
    (hv : ∀ i∈l,v (f i)=w i) : StackMatching v (l.map f) where
  first := M.first.map (Prod.map f f)
  second := M.second.map (Prod.map f f)
  first_arches := M.first_arches.map f
  second_arches := M.second_arches.map f
  covers := by rw [← List.map_append,endpoints_map];exact M.covers.map f
  first_types := by
    intro e he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    have hh := M.endpoints_mem x (List.mem_append_left _ hx)
    simpa only [Prod.map_fst,Prod.map_snd,hv _ hh.1,hv _ hh.2] using M.first_types x hx
  second_types := by
    intro e he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
    have hh := M.endpoints_mem x (List.mem_append_right _ hx)
    simpa only [Prod.map_fst,Prod.map_snd,hv _ hh.1,hv _ hh.2] using M.second_types x hx

lemma map_mate [DecidableEq α] [DecidableEq β] (M : StackMatching w l)
    (hn : l.Nodup) (f : α→β) (hf : Function.Injective f) (v : β→TypedLetter)
    (hv : ∀ i∈l,v (f i)=w i) (i : α) (hi : i∈l) :
    (M.map f v hv).mate (f i)=f (M.mate i) := by
  change turns (List.map (Prod.map f f) M.first++List.map (Prod.map f f) M.second) (f i)=_
  rw [← List.map_append]
  exact turns_map_on f hf _ (M.covers.nodup_iff.mpr hn) i (M.covers.mem_iff.mpr hi)

lemma cast_mate [DecidableEq α] {l' : List α} (h : l=l') (M : StackMatching w l) :
    (h ▸ M).mate=M.mate := by cases h; rfl

end StackMatching

variable [LinearOrder α]
/-- The literal increasing compression map, not a fresh random matching. -/
def positionEmbedding (l : List α) (hs : l.Pairwise (·<·)) : Fin l.length ↪o α :=
  OrderEmbedding.ofStrictMono l.get (fun _ _ h => hs.rel_get_of_lt h)

omit [LinearOrder α] in
lemma positions_word (w : α→TypedLetter) (l : List α) :
    (List.finRange l.length).map (w ∘ l.get)=l.map w := by
  rw [← List.map_map,List.map_get_finRange]

/-- Normalization preserves the actual mate permutation on all positions. -/
theorem normalized_matching_mate (w : α→TypedLetter) (l : List α) (hs : l.Pairwise (·<·))
    (M : StackMatching w l) :
    ∃ P : StackMatching (w ∘ l.get) (List.finRange l.length),
      ∀ i,M.mate (l.get i)=l.get (P.mate i) := by
  have hn : l.Nodup := hs.nodup
  have hw : stackTypedRun ((List.finRange l.length).map (w ∘ l.get)) []=some [] := by
    rw [positions_word];exact M.empty hn
  let P := StackMatching.ofEmpty hw
  let Q := P.map l.get w (fun _ _ => rfl)
  have hQ : (List.finRange l.length).map l.get=l := List.map_get_finRange l
  let R : StackMatching w l := hQ ▸ Q
  have hmate := M.unique_mate R hn
  refine ⟨P,fun i => ?_⟩
  rw [hmate]
  have hR : R.mate=Q.mate := StackMatching.cast_mate hQ Q
  rw [hR]
  exact P.map_mate (List.nodup_finRange _) l.get (List.nodup_iff_injective_get.mp hn)
    w (fun _ _ => rfl) i (List.mem_finRange i)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

lemma turns_sublist_preserves {E F : List (α×α)} (hn : (endpoints F).Nodup)
    (hEF : E<+F) {S : Set α} (hF : ∀ d∈S,turns F d∈S) :
    ∀ d,turns E d∈S ↔ d∈S := by
  have he : (endpoints E).Nodup := hn.sublist (hEF.flatMap _)
  have hf (d : α) (hd : d∈S) : turns E d∈S := by
    by_cases hx : d∈endpoints E
    · rw [turns_sublist_apply hn hEF hx]
      exact hF d hd
    · simpa only [turns_fixed_of_notMem hx] using hd
  intro d
  constructor
  · intro hd
    simpa only [turns_involutive he d] using hf (turns E d) hd
  · exact hf d

end FKCRT.MapCycles
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma StackMatching.empty_prefix_preserves {w : α→TypedLetter} {v z : List α}
    (M : StackMatching w (v++z)) (hn : (v++z).Nodup)
    (hv : stackTypedRun (v.map w) []=some []) :
    (∀ d,M.mate d∈v ↔ d∈v) ∧ (∀ d,turns M.first d∈v ↔ d∈v) := by
  have hm (d : α) (hd : d∈v) : turns (M.first++M.second) d∈v := by
    exact empty_interval_matching_closed w [] v z (by simpa using hn)
      M.first M.second (by simpa using M.first_arches) (by simpa using M.second_arches)
      (by simpa using M.covers) M.first_types M.second_types hv d hd
  have hn' : (endpoints (M.first++M.second)).Nodup := M.covers.nodup_iff.mpr hn
  exact ⟨turns_sublist_preserves hn' (List.Sublist.refl _) hm,
    turns_sublist_preserves hn' (List.sublist_append_left _ _) hm⟩

/-- A genuine successful inserted interval of the actual typed matching
creates a one-vertex union for the full, all-edge map graph. The local graph
metric conclusions now follow unconditionally from `GraphWedge.Data`. -/
def StackMatching.empty_prefix_wedge {w : α→TypedLetter} (a b : α) (L R : List α)
    (M : StackMatching w ((a::L)++(b::R))) (hn : ((a::L)++(b::R)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) :
    let p := (a::L).formPerm*(b::R).formPerm*turns M.first
    let S : Set α := {d | d∈a::L}
    GraphWedge.Data (sideGraph M.mate p S (M.empty_prefix_preserves hn hv).1)
      (sideGraph M.mate p Sᶜ (fun d => not_congr ((M.empty_prefix_preserves hn hv).1 d)))
      (dartGraph M.mate (swap a b*p)) := by
  let S : Set α := {d | d∈a::L}
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  have hpres := M.empty_prefix_preserves hn hv
  have hd : (a::L).Disjoint (b::R) := List.disjoint_iff_ne.mpr (List.nodup_append.mp hn).2.2
  have hp : ∀ d,p d∈S ↔ d∈S := by
    intro d
    simp only [p,S,Set.mem_ofPred_eq,mul_apply,List.formPerm_mem_iff_mem,
      formPerm_other_mem_iff hd,hpres.2]
  have ha : a∈S := by simp [S]
  have hb : b∉S := fun h => List.disjoint_left.mp hd h (by simp)
  exact PermutationWedge.data hp ha hb hpres.1

/-- Literal all-edge distance preservation for actual typed insertion,
not merely the selected spanning tree or a replacement metric. -/
theorem StackMatching.empty_prefix_distance {w : α→TypedLetter} (a b : α) (L R : List α)
    (M : StackMatching w ((a::L)++(b::R))) (hn : ((a::L)++(b::R)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (x y : α)
    (hx : x∈a::L) (hy : y∈a::L) :
    let p := (a::L).formPerm*(b::R).formPerm*turns M.first
    let s := ((a::L)++(b::R)).formPerm*turns M.first
    let S : Set α := {d | d∈a::L}
    (dartGraph M.mate s).edist (vertex s x) (vertex s y)=
      (sideGraph M.mate p S (M.empty_prefix_preserves hn hv).1).edist
        (sideMk p S x hx) (sideMk p S y hy) := by
  dsimp only
  have hj := (contour_vertex_join a b L R (by simpa only [List.cons_append] using hn)
    (turns M.first) (M.empty_prefix_preserves hn hv).2).1
  have hj' : ((a::L)++(b::R)).formPerm*turns M.first=
      swap a b*((a::L).formPerm*(b::R).formPerm*turns M.first) := by
    simpa only [List.cons_append] using hj
  rw [hj']
  exact (M.empty_prefix_wedge a b L R hn hv).edist_left
    (sideMk _ _ x hx) (sideMk _ _ y hy)

/-- Cross-block distances in the original all-edge map add through the
unique identified vertex. This includes coincident poles and loop edges. -/
theorem StackMatching.empty_prefix_cross_distance {w : α→TypedLetter} (a b : α) (L R : List α)
    (M : StackMatching w ((a::L)++(b::R))) (hn : ((a::L)++(b::R)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (x y : α)
    (hx : x∈a::L) (hy : y∉a::L) :
    let p := (a::L).formPerm*(b::R).formPerm*turns M.first
    let s := ((a::L)++(b::R)).formPerm*turns M.first
    let S : Set α := {d | d∈a::L}
    (dartGraph M.mate s).edist (vertex s x) (vertex s y)=
      (sideGraph M.mate p S (M.empty_prefix_preserves hn hv).1).edist
        (sideMk p S x hx) (sideMk p S a (by simp [S]))+
      (sideGraph M.mate p Sᶜ (fun d => not_congr ((M.empty_prefix_preserves hn hv).1 d))).edist
        (sideMk p Sᶜ b (fun hb => List.disjoint_left.mp
          (List.disjoint_iff_ne.mpr (List.nodup_append.mp hn).2.2) hb (by simp)))
        (sideMk p Sᶜ y hy) := by
  dsimp only
  have hj := (contour_vertex_join a b L R (by simpa only [List.cons_append] using hn)
    (turns M.first) (M.empty_prefix_preserves hn hv).2).1
  have hj' : ((a::L)++(b::R)).formPerm*turns M.first=
      swap a b*((a::L).formPerm*(b::R).formPerm*turns M.first) := by
    simpa only [List.cons_append] using hj
  rw [hj']
  exact (M.empty_prefix_wedge a b L R hn hv).edist_cross
    (sideMk _ _ x hx) (sideMk _ _ y hy)

end FKCRT.Inventory
end

end OAI
