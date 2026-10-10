import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BlueLookup

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueTable
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
noncomputable def row (x : List Bool) : List Bool := pairBits (discardPrefix x,BinaryBlueCell.run x)
noncomputable def row_computes : PolyComputes row := discardPrefix_computes.pair BinaryBlueCell.run_computes
noncomputable def next (x : List Bool) : List Bool := mapWith row (pairBits (x,field 2 x))
noncomputable def next_computes : PolyComputes next := by
  unfold next
  have computes := (id_computes.pair (field_computes 2)).comp (mapWith_computes row_computes)
  simpa only [Function.comp_def,id_eq] using computes
lemma next_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) :
    next (BinaryBlueCell.ctxPack er B F label q U T)=
      BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueCell.atomEnc er) (BlueDP.nextTable (BlueDP.block B F label q) U T) := by
  unfold next
  rw [show field 2 (BinaryBlueCell.ctxPack er B F label q U T)=encode ((BlueDP.states U).map BinaryFinSet.encode) by
    simp only [BinaryBlueCell.ctxPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]]
  simp only [mapWith_encode,List.map_map,Function.comp_def,BinaryBlueLookup.encode,BlueDP.nextTable]
  congr 1
  apply List.map_congr_left
  intro W hW
  simp only [row,discardPrefix_pairBits,BinaryBlueCell.run_pack er B F label q U W T ((BlueDP.mem_states U W).mp hW)]
noncomputable def initRow (x : List Bool) : List Bool := pairBits (discardPrefix x,
  if discardPrefix x=[] then BinaryBlueChoice.encode id (some (0,[])) else [])
noncomputable def initRow_computes : PolyComputes initRow := by
  unfold initRow
  simpa only [decide_eq_true_eq] using discardPrefix_computes.pair ((discardPrefix_computes.comp isEmpty_computes).cond
    (const_computes (BinaryBlueChoice.encode id (some (0,[])))) (const_computes []))
noncomputable def initial (x : List Bool) : List Bool := mapWith initRow (pairBits ([],x))
noncomputable def initial_computes : PolyComputes initial := by
  unfold initial
  have computes := ((const_computes []).pair id_computes).comp (mapWith_computes initRow_computes)
  simpa only [Function.comp_def,id_eq] using computes
omit [LinearOrder R] in
lemma initial_pack (er : R→List Bool) (U : Finset (Fin m)) :
    initial (encode ((BlueDP.states U).map BinaryFinSet.encode))=
      BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueCell.atomEnc (n:=n) (m:=m) er) (BlueDP.initialTable U) := by
  simp only [initial,mapWith_encode,List.map_map,Function.comp_def,initRow,discardPrefix_pairBits,
    BinaryBlueStates.key_empty,BinaryBlueLookup.encode,BlueDP.initialTable]
  congr 1
  apply List.map_congr_left
  intro W _
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryBlueTable

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y]
def labels (xs : List (Atom L R Y)) : List L := xs.map Prod.fst
def destinations (xs : List (Atom L R Y)) : Finset Y := (xs.map (fun a=>a.2.2)).toFinset
def cost (q : R→Y→ℚ) (xs : List (Atom L R Y)) : ℚ := (xs.map (fun a=>q a.2.1 a.2.2)).sum
def Valid (B : Finset R) (F : Finset Y) (label : R→L) (xs : List (Atom L R Y)) : Prop :=
  ∀ a∈xs,a.2.1∈B ∧ label a.2.1=a.1 ∧ a.2.2∈F
def Route (U : Finset L) (xs : List (Atom L R Y)) : Prop := (labels xs).Nodup ∧ (labels xs).toFinset=U
def Spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U : Finset L) (c : ℕ) : Candidate (List (Atom L R Y))→Prop
  | none=>True
  | some (k,xs)=>Route U xs ∧ Valid B F label xs ∧ (destinations xs).card≤c ∧ k=cost q xs
lemma select_spec {A : Type*} (P : Candidate A→Prop) (xs : List (Candidate A)) (h0 : P none)
    (hxs : ∀ x∈xs,P x) : P (select xs) := fold_property P xs none h0 hxs
omit [LinearOrder R] [LinearOrder Y] in
lemma route_append (U V : Finset L) (xs ys : List (Atom L R Y)) (hx : Route U xs) (hy : Route V ys)
    (hUV : Disjoint U V) : Route (U∪V) (xs++ys) := by
  rcases hx with ⟨hxn,hx⟩
  rcases hy with ⟨hyn,hy⟩
  refine ⟨?_,?_⟩
  · rw [labels,List.map_append,List.nodup_append]
    refine ⟨hxn,hyn,?_⟩
    intro a hax b hay hab
    subst b
    exact (Finset.disjoint_left.mp hUV (hx ▸ List.mem_toFinset.mpr hax) (hy ▸ List.mem_toFinset.mpr hay))
  · simp only [labels,List.map_append,List.toFinset_append] at hx hy ⊢
    rw [hx,hy]
omit [LinearOrder L] [LinearOrder R] [LinearOrder Y] in
lemma valid_append (B : Finset R) (F : Finset Y) (label : R→L) (xs ys : List (Atom L R Y))
    (hx : Valid B F label xs) (hy : Valid B F label ys) : Valid B F label (xs++ys) := by
  intro a ha
  rcases List.mem_append.mp ha with h|h
  · exact hx a h
  · exact hy a h
omit [LinearOrder R] in
lemma merge_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U V : Finset L) (c d : ℕ) (x y : Candidate (List (Atom L R Y)))
    (hx : Spec B F label q U c x) (hy : Spec B F label q V d y) (hUV : Disjoint U V) :
    Spec B F label q (U∪V) (c+d) (merge x y) := by
  cases x with
  | none=>trivial
  | some x=>
    cases y with
    | none=>trivial
    | some y=>
      rcases x with ⟨k,xs⟩
      rcases y with ⟨j,ys⟩
      rcases hx with ⟨hx,hxv,hxc,rfl⟩
      rcases hy with ⟨hy,hyv,hyc,rfl⟩
      refine ⟨route_append U V xs ys hx hy hUV,valid_append B F label xs ys hxv hyv,?_,?_⟩
      · simp only [destinations,List.map_append,List.toFinset_append]
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add hxc hyc)
      · simp [cost,List.sum_append]
omit [LinearOrder R] in
lemma empty_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ) :
    Spec B F label q ∅ c (some (0,[])) := by
  simp [Spec,Route,labels,Valid,destinations,cost]
omit [LinearOrder Y] in
lemma item_witness (B : Finset R) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y)
    (k : ℚ) (xs : List (Atom L R Y)) (h : item B label q l y=some (k,xs)) :
    ∃ r∈B,label r=l ∧ k=q r y ∧ xs=[(l,r,y)] := by
  have hh:=fold_mem (((B.filter (label ·=l)).sort (·≤·)).map (fun r=>some (q r y,[(l,r,y)]))) none
  change item B label q l y=none ∨ item B label q l y∈_ at hh
  rcases hh with he|hm
  · rw [h] at he;cases he
  · rw [h] at hm
    obtain ⟨r,hr,he⟩:=List.mem_map.mp hm
    have hr':=Finset.mem_filter.mp ((Finset.mem_sort (·≤·)).mp hr)
    have he':=Option.some.inj he
    exact ⟨r,hr'.1,hr'.2,(congrArg Prod.fst he').symm,(congrArg Prod.snd he').symm⟩
lemma item_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (l : L) (y : Y) (hy : y∈F) :
    Spec B F label q {l} 1 (item B label q l y) := by
  cases he : item B label q l y with
  | none=>trivial
  | some x=>
    rcases x with ⟨k,xs⟩
    obtain ⟨r,hr,hlabel,rfl,rfl⟩:=item_witness B label q l y k xs he
    simp [Spec,Route,labels,Valid,destinations,cost,hr,hlabel,hy]
lemma collect_items_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (ls : List L) (hls : ls.Nodup) (y : Y) (hy : y∈F) :
    Spec B F label q ls.toFinset ls.length (collect (ls.map (fun l=>item B label q l y))) := by
  induction ls with
  | nil=>exact empty_spec B F label q 0
  | cons l ls ih=>
    have hls':=List.nodup_cons.mp hls
    have hh:=merge_spec B F label q {l} ls.toFinset 1 ls.length _ _ (item_spec B F label q l y hy) (ih hls'.2)
      (by simpa using hls'.1)
    simpa only [List.map_cons,collect,List.foldr_cons,List.toFinset_cons,List.length_cons,
      Finset.singleton_union,Nat.add_comm 1] using hh
omit [LinearOrder Y] in
lemma collect_dest (B : Finset R) (label : R→L) (q : R→Y→ℚ) (ls : List L) (y : Y)
    (k : ℚ) (xs : List (Atom L R Y)) (h : collect (ls.map (fun l=>item B label q l y))=some (k,xs)) :
    ∀ a∈xs,a.2.2=y := by
  induction ls generalizing k xs with
  | nil=>simp only [List.map_nil,collect,List.foldr_nil,Option.some.injEq,Prod.mk.injEq] at h;rw [←h.2];simp
  | cons l ls ih=>
    change merge (item B label q l y) (collect (ls.map (fun l=>item B label q l y)))=some (k,xs) at h
    cases hi : item B label q l y with
    | none=>simp [hi,merge] at h
    | some v=>
      rcases v with ⟨j,ys⟩
      obtain ⟨r,_,_,rfl,rfl⟩:=item_witness B label q l y j ys hi
      cases ht : collect (ls.map (fun l=>item B label q l y)) with
      | none=>simp [hi,ht,merge] at h
      | some v=>
        rcases v with ⟨z,zs⟩
        rw [hi,ht,merge] at h
        have he:=congrArg Prod.snd (Option.some.inj h)
        dsimp only at he
        rw [←he]
        intro a ha
        rcases List.mem_append.mp ha with ha|ha
        · simpa using (List.mem_singleton.mp ha ▸ rfl : a.2.2=y)
        · exact ih z zs ht a ha
lemma blockAt_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ)
    (U : Finset L) (y : Y) (hy : y∈F) : Spec B F label q U 1 (blockAt B label q U y) := by
  have hs:=collect_items_spec B F label q (U.sort (·≤·)) (Finset.sort_nodup U (·≤·)) y hy
  simp only [Finset.sort_toFinset,Finset.length_sort] at hs
  cases he : blockAt B label q U y with
  | none=>trivial
  | some v=>
    rcases v with ⟨k,xs⟩
    change Spec B F label q U U.card (blockAt B label q U y) at hs
    rw [he] at hs
    refine ⟨hs.1,hs.2.1,?_,hs.2.2.2⟩
    have hsub : destinations xs⊆{y} := by
      intro z hz
      obtain ⟨a,ha,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hz)
      exact Finset.mem_singleton.mpr (collect_dest B label q (U.sort (·≤·)) y k xs he a ha)
    exact (Finset.card_le_card hsub).trans (by simp)
lemma block_spec (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (U : Finset L) :
    Spec B F label q U 1 (block B F label q U) := by
  apply select_spec _ _ trivial
  intro x hx
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
  exact blockAt_spec B F label q U y ((Finset.mem_sort (·≤·)).mp hy)
end MetricKMedianRecovery.BlueDP

end OAI
