import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.RoutedFamilies

namespace OAI

/-!
# Ranked galleries with fresh parents

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical

/-- The main parent has its own occurrence label. All secondary facet labels
remain available without any distinctness requirement. -/
def freshRank {F : Type} (N : ℕ) (r : F → ℕ) : Option F → ℕ
  | none => N
  | some a => r a

variable {F : Type} {N : ℕ} {r : F → ℕ}

lemma listRank_some (a : List F) : listRank (freshRank N r) (a.map some) = listRank r a := by
  simp [listRank, List.map_map, freshRank, Function.comp_def]

/-- A property of an actual ranked program, not an assumed property of a band
chosen from its weaker original specification. -/
def RankedChain.Fresh {a b : List (Option F)}
    (c : RankedChain (freshRank N r) none a b) : Prop :=
  match c with
  | .refl _ => True
  | .step s _ p => (∃ d : s.kind.SecondaryNames F,
      s.decoration = s.kind.freshDecoration d) ∧ p.Fresh

namespace RankedChain
theorem exists_fresh_congr {a b a' b' : List (Option F)}
    (ha : a = a') (hb : b = b')
    (h : ∃ c : RankedChain (freshRank N r) none a b, c.Fresh) :
    ∃ c : RankedChain (freshRank N r) none a' b', c.Fresh := by
  subst a'
  subst b'
  exact h

lemma fresh_trans {a b c : List (Option F)}
    (p : RankedChain (freshRank N r) none a b)
    (q : RankedChain (freshRank N r) none b c) (hp : p.Fresh) (hq : q.Fresh) :
    (p.trans q).Fresh := by
  induction p with
  | refl _ => exact hq
  | step s hs p ih => exact ⟨hp.1, ih q hp.2 hq⟩

lemma fresh_single {a b : List (Option F)}
    (s : OrderedStep none a b) (hs : s.decoration.Conservative (freshRank N r))
    (h : ∃ d : s.kind.SecondaryNames F, s.decoration = s.kind.freshDecoration d) :
    (single s hs).Fresh := ⟨h,trivial⟩

lemma fresh_split (big : F) (left mid right : List F)
    (hp : N = listRank r (left ++ big :: right)) (hm : r big = listRank r mid) :
    ∃ c : RankedChain (freshRank N r) none
        ((left ++ big :: right).map some) ((left ++ (mid ++ right)).map some), c.Fresh := by
  have hp' : freshRank N r none = listRank (freshRank N r)
      (left.map some ++ some big :: right.map some) := by
    simpa only [← List.map_cons, ← List.map_append, listRank_some, freshRank] using hp
  have hm' : freshRank N r (some big) = listRank (freshRank N r) (mid.map some) := by
    simpa only [listRank_some, freshRank] using hm
  let c := RankedChain.split (some big) (left.map some) (mid.map some) (right.map some) hp' hm'
  have h : c.Fresh := by
    refine fresh_single _ _ ?_
    refine ⟨(big, (fun j => left.get (Fin.cast (List.length_map ..) j)),
      (fun j => mid.get (Fin.cast (List.length_map ..) j)),
      (fun j => right.get (Fin.cast (List.length_map ..) j))), ?_⟩
    simp only [OrderedStep.split, splitLists, Kind.freshDecoration]
    congr 1 <;> funext j <;> simp [List.get_eq_getElem]
  exact exists_fresh_congr (by simp only [List.map_append, List.map_cons])
    (by simp only [List.map_append]) ⟨c,h⟩

lemma fresh_merge (big : F) (left mid right : List F)
    (hp : N = listRank r (left ++ big :: right)) (hm : r big = listRank r mid) :
    ∃ c : RankedChain (freshRank N r) none
        ((left ++ (mid ++ right)).map some) ((left ++ big :: right).map some), c.Fresh := by
  have hp' : freshRank N r none = listRank (freshRank N r)
      (left.map some ++ some big :: right.map some) := by
    simpa only [← List.map_cons, ← List.map_append, listRank_some, freshRank] using hp
  have hm' : freshRank N r (some big) = listRank (freshRank N r) (mid.map some) := by
    simpa only [listRank_some, freshRank] using hm
  let c := RankedChain.merge (some big) (left.map some) (mid.map some) (right.map some) hp' hm'
  have h : c.Fresh := by
    refine fresh_single _ _ ?_
    refine ⟨(big, (fun j => left.get (Fin.cast (List.length_map ..) j)),
      (fun j => mid.get (Fin.cast (List.length_map ..) j)),
      (fun j => right.get (Fin.cast (List.length_map ..) j))), ?_⟩
    simp only [OrderedStep.merge, splitLists, Kind.freshDecoration]
    congr 1 <;> funext j <;> simp [List.get_eq_getElem]
  exact exists_fresh_congr (by simp only [List.map_append])
    (by simp only [List.map_append, List.map_cons]) ⟨c,h⟩

lemma fresh_passage {m : ℕ} (t : Passage m) (f : Fin m → F)
    (hp : N = listRank r (List.ofFn f)) :
    ∃ c : RankedChain (freshRank N r) none
        ((List.ofFn f).map some) ((List.ofFn (f ∘ t.permutation.symm)).map some), c.Fresh := by
  have hp' : freshRank N r none = listRank (freshRank N r) (List.ofFn (fun i => some (f i))) := by
    rw [show List.ofFn (fun i => some (f i)) = (List.ofFn f).map some by simp [List.map_ofFn, Function.comp_def]]
    exact hp.trans (listRank_some _).symm
  let c := RankedChain.passage t (fun i => some (f i)) hp'
  have h : c.Fresh := fresh_single _ _ ⟨f, rfl⟩
  exact exists_fresh_congr (by simp [List.map_ofFn, Function.comp_def])
    (by simp [List.map_ofFn, Function.comp_def]) ⟨c,h⟩
end RankedChain

/-- A finite genuine ranked gallery with a verified fresh-parent decoration
at every vertex. This is constructed below, not included as a main hypothesis. -/
def FreshGallery (N : ℕ) (r : F → ℕ) (a b : List F) : Prop :=
  ∃ c : RankedChain (freshRank N r) none (a.map some) (b.map some), c.Fresh

namespace FreshGallery
lemma refl (a : List F) : FreshGallery N r a a := ⟨.refl _, trivial⟩
lemma trans {a b c : List F} (h : FreshGallery N r a b) (k : FreshGallery N r b c) :
    FreshGallery N r a c := by
  obtain ⟨p,hp⟩ := h
  obtain ⟨q,hq⟩ := k
  exact ⟨p.trans q, p.fresh_trans q hp hq⟩

lemma split (big : F) (left mid right : List F)
    (hp : N = listRank r (left ++ big :: right)) (hm : r big = listRank r mid) :
    FreshGallery N r (left ++ big :: right) (left ++ (mid ++ right)) :=
  RankedChain.fresh_split big left mid right hp hm
lemma merge (big : F) (left mid right : List F)
    (hp : N = listRank r (left ++ big :: right)) (hm : r big = listRank r mid) :
    FreshGallery N r (left ++ (mid ++ right)) (left ++ big :: right) :=
  RankedChain.fresh_merge big left mid right hp hm
lemma passage {m : ℕ} (t : Passage m) (f : Fin m → F)
    (hp : N = listRank r (List.ofFn f)) :
    FreshGallery N r (List.ofFn f) (List.ofFn (f ∘ t.permutation.symm)) :=
  RankedChain.fresh_passage t f hp

lemma refine_rows (rows : List (F × List F)) (left right : List F)
    (hp : N = listRank r (left ++ (rows.map Prod.fst ++ right)))
    (hr : ∀ x ∈ rows, r x.1 = listRank r x.2) :
    FreshGallery N r (left ++ (rows.map Prod.fst ++ right))
      (left ++ (rows.flatMap Prod.snd ++ right)) ∧
    FreshGallery N r (left ++ (rows.flatMap Prod.snd ++ right))
      (left ++ (rows.map Prod.fst ++ right)) := by
  induction rows generalizing left with
  | nil => exact ⟨.refl _, .refl _⟩
  | cons x rows ih =>
    have hx := hr x (by simp)
    have ht : ∀ y ∈ rows, r y.1 = listRank r y.2 := fun y hy => hr y (by simp [hy])
    have hp' : N = listRank r ((left ++ x.2) ++ (rows.map Prod.fst ++ right)) := by
      simpa only [List.map_cons,listRank_append,listRank_cons,hx,add_assoc] using hp
    obtain ⟨p,q⟩ := ih (left ++ x.2) hp' ht
    constructor
    · have h := (split x.1 left x.2 (rows.map Prod.fst ++ right) hp hx).trans
        (by simpa [List.append_assoc] using p)
      simpa [List.append_assoc] using h
    · have h := q.trans (by simpa [List.append_assoc] using
        (merge x.1 left x.2 (rows.map Prod.fst ++ right) hp hx))
      simpa [List.append_assoc] using h

/-- Freshness is retained under adjacent interchanges even when names repeat.
The later common-splitting argument additionally uses a no-recrossing order. -/
lemma permutation {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    ∀ (f : Fin m → F), N = listRank r (List.ofFn f) →
      FreshGallery N r (List.ofFn f) (List.ofFn (f ∘ σ.symm)) := by
  cases m with
  | zero =>
    intro f _
    simpa using (refl (N:=N) (r:=r) ([] : List F))
  | succ n =>
    have hs : σ ∈ Submonoid.closure (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hs using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i,rfl⟩
      intro f hf
      exact passage (.interchange (m:=n+1) i) f hf
    | one => intro f _; exact .refl _
    | mul x y hx hy ihx ihy =>
      intro f hf
      have p := ihy f hf
      have hf' : N = listRank r (List.ofFn (f ∘ y.symm)) := by
        simp only [listRank_ofFn] at hf ⊢
        exact hf.trans (Equiv.sum_comp y.symm (fun i => r (f i))).symm
      exact p.trans (ihx (f ∘ y.symm) hf')

lemma equivalence {m n : ℕ} (e : Fin m ≃ Fin n) (f : Fin m → F)
    (hf : N = listRank r (List.ofFn f)) :
    FreshGallery N r (List.ofFn f) (List.ofFn (f ∘ e.symm)) := by
  have h : m = n := by simpa using Fintype.card_congr e
  subst n
  exact permutation e f hf

lemma rectangular {m n : ℕ} (f : Fin m → Fin n → F)
    (hf : N = listRank r ((List.ofFn fun i => List.ofFn (f i)).flatten)) :
    FreshGallery N r ((List.ofFn fun i => List.ofFn (f i)).flatten)
      ((List.ofFn fun j => List.ofFn fun i => f i j).flatten) := by
  have h := equivalence (gridTranspose m n)
    (fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (by simpa only [matrix_list] using hf)
  rw [gridTranspose_colors,matrix_list] at h
  have hc := matrix_list (fun j i => f i j)
  exact hc ▸ h

lemma two_flag_gallery {m n : ℕ} (row : Fin m → F) (col : Fin n → F)
    (grid : Fin m → Fin n → F) (hp : N = ∑ i, r (row i))
    (hr : ∀ i, r (row i) = ∑ j, r (grid i j))
    (hc : ∀ j, r (col j) = ∑ i, r (grid i j)) :
    FreshGallery N r (List.ofFn row) (List.ofFn col) := by
  have hpc : N = ∑ j, r (col j) := by
    rw [hp]
    simp_rw [hr,hc]
    exact Finset.sum_comm
  have Hrows : ∀ x ∈ (List.ofFn fun i => (row i,List.ofFn (grid i))),
      r x.1 = listRank r x.2 := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hr i
  have Hcols : ∀ x ∈ (List.ofFn fun j => (col j,List.ofFn fun i => grid i j)),
      r x.1 = listRank r x.2 := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hc j
  have hrow := (refine_rows (List.ofFn fun i => (row i,List.ofFn (grid i))) [] []
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hp) Hrows).1
  have hcol := (refine_rows (List.ofFn fun j => (col j,List.ofFn fun i => grid i j)) [] []
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hpc) Hcols).2
  simp only [List.nil_append,List.append_nil,List.flatMap_def,List.map_ofFn] at hrow hcol
  have hgrid : N = listRank r ((List.ofFn fun i => List.ofFn (grid i)).flatten) := by
    simp only [listRank_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply,listRank_ofFn]
    simpa only [hr] using hp
  exact hrow.trans ((rectangular grid hgrid).trans hcol)
end FreshGallery

namespace OrderedWalk
variable {a b c : List (Option F)}
/-- Genuine secondary-name witnesses at every vertex of the walk. -/
def Fresh (w : OrderedWalk none a b) : Prop :=
  ∀ j, ∃ d : (w.vertex j).kind.SecondaryNames F,
    (w.vertex j).decoration = (w.vertex j).kind.freshDecoration d

lemma fresh_cons (s : OrderedStep none a b) (w : OrderedWalk none b c)
    (hs : ∃ d : s.kind.SecondaryNames F, s.decoration = s.kind.freshDecoration d)
    (hw : w.Fresh) : (w.cons s).Fresh := by
  rcases w with ⟨l,state,vertex,first,last⟩
  subst b
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hs
  · exact hw i

lemma fresh_headIdentity (a : List F) (w : OrderedWalk none (a.map some) b)
    (hw : w.Fresh) : w.headIdentity.Fresh := by
  apply fresh_cons _ _ ?_ hw
  refine ⟨(fun j => a.get (Fin.cast (List.length_map ..) j)), ?_⟩
  change passageDecoration .continuation none (a.map some).get = _
  simp only [Kind.freshDecoration]
  congr 1
  funext j
  simp [List.get_eq_getElem]

lemma realize_fresh (a : List F) (w : OrderedWalk none (a.map some) b)
    (hw : w.Fresh) :
    ∀ v, ∃ d : (w.realize.kind v).SecondaryNames F,
      w.realize.decoration v = (w.realize.kind v).freshDecoration d :=
  w.fresh_headIdentity a hw
end OrderedWalk

namespace RankedChain
lemma walk_fresh {a b : List (Option F)}
    (p : RankedChain (freshRank N r) none a b) (hp : p.Fresh) :
    p.forget.walk.Fresh := by
  induction p with
  | refl a => intro j; exact Fin.elim0 j
  | step s hs p ih => exact OrderedWalk.fresh_cons s p.forget.walk hp.1 (ih hp.2)
end RankedChain

lemma RealizedBand.exists_fresh_congr {a b a' b' : List (Option F)}
    (ha : a = a') (hb : b = b')
    (H : ∃ B : RealizedBand none a b,
      (∀ v, (B.decoration v).Conservative (freshRank N r)) ∧
      (∀ v, ∃ d : (B.kind v).SecondaryNames F,
        B.decoration v = (B.kind v).freshDecoration d)) :
    ∃ B : RealizedBand none a' b',
      (∀ v, (B.decoration v).Conservative (freshRank N r)) ∧
      (∀ v, ∃ d : (B.kind v).SecondaryNames F,
        B.decoration v = (B.kind v).freshDecoration d) := by
  subst a'
  subst b'
  exact H

/-- A rank-conservative band whose secondary parents and children are all
disjoint from its fresh main parent. -/
theorem fresh_ranked_two_flag_band {m n : ℕ} (row : Fin m → F) (col : Fin n → F)
    (grid : Fin m → Fin n → F) (hp : N = ∑ i, r (row i))
    (hr : ∀ i, r (row i) = ∑ j, r (grid i j))
    (hc : ∀ j, r (col j) = ∑ i, r (grid i j)) :
    ∃ B : RealizedBand none (List.ofFn (some ∘ row)) (List.ofFn (some ∘ col)),
      (∀ v, (B.decoration v).Conservative (freshRank N r)) ∧
      (∀ v, ∃ d : (B.kind v).SecondaryNames F,
        B.decoration v = (B.kind v).freshDecoration d) := by
  obtain ⟨p,hp'⟩ := FreshGallery.two_flag_gallery row col grid hp hr hc
  have h : freshRank N r none = listRank (freshRank N r) ((List.ofFn row).map some) := by
    simpa only [listRank_some,listRank_ofFn,freshRank] using hp
  have H : ∃ B : RealizedBand none ((List.ofFn row).map some) ((List.ofFn col).map some),
      (∀ v, (B.decoration v).Conservative (freshRank N r)) ∧
      (∀ v, ∃ d : (B.kind v).SecondaryNames F,
        B.decoration v = (B.kind v).freshDecoration d) := by
    exact ⟨p.forget.walk.realize, p.forget.walk.realize_conservative p.walk_conservative h,
      p.forget.walk.realize_fresh (List.ofFn row) (p.walk_fresh hp')⟩
  exact RealizedBand.exists_fresh_congr (List.map_ofFn ..) (List.map_ofFn ..) H

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
variable {F : Type} {a b : List (Option F)}

/-- The very same band, with all branch ports and all colours. The fresh-name
proof supplies exhaustion, rather than replacing the band by an unrelated
cyclic template with identical endpoints. -/
noncomputable def VertexTable.RealizedBand.parentTemplate (B : RealizedBand none a b)
    (h : ∀ v, ∃ d : (B.kind v).SecondaryNames F,
      B.decoration v = (B.kind v).freshDecoration d) : ParentTemplate F where
  V := Fin (B.length+1)
  I := Fin B.length
  A := {p : PortAt B.kind true // p∉Set.range (VariableGallery.internalPlus B.kind)}
  B := {p : PortAt B.kind false // p∉Set.range (VariableGallery.internalMinus B.kind)}
  finiteV := inferInstance
  kind := B.kind
  patch := B.patch
  input := ⟨VariableGallery.input B.kind 0,VariableGallery.first_exposed B.kind⟩
  output := ⟨VariableGallery.output B.kind (Fin.last B.length),VariableGallery.last_exposed B.kind⟩
  length := B.length
  path := VariableGallery.parentPath B.kind B.arity_match
  decoration := B.decoration
  nodes j := by
    obtain ⟨d,hd⟩ := h j
    change (B.decoration j).color ⟨(B.kind j).input,none⟩ = none
    rw [hd]
    exact ((B.kind j).fresh_color_none d _).2 (Or.inl rfl)
  exhaustive x hx := by
    obtain ⟨v,p,c⟩ := x
    obtain ⟨d,hd⟩ := h v
    change (B.decoration v).color ⟨p,c⟩ = none at hx
    rw [hd] at hx
    obtain he|he := ((B.kind v).fresh_color_none d _).1 hx
    · exact ⟨v,Or.inl (congrArg (fun z => (⟨v,z⟩ : LocalEnd _ B.kind)) he)⟩
    · refine ⟨v,Or.inr ?_⟩
      change (⟨v,p,c⟩ : LocalEnd _ B.kind)=localMate ⟨v,(B.kind v).input,none⟩
      rw [VariableGallery.parent_corner B.kind]
      exact congrArg (fun z => (⟨v,z⟩ : LocalEnd _ B.kind)) he

/-- Literal equality of decorations after conversion, not just equality of
ranks or matching named endpoints. -/
lemma VertexTable.RealizedBand.parentTemplate_decoration (B : RealizedBand none a b)
    (h : ∀ v, ∃ d : (B.kind v).SecondaryNames F,
      B.decoration v = (B.kind v).freshDecoration d) :
    (B.parentTemplate h).decoration = B.decoration := rfl

end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.DirectedSort
open scoped Classical
variable {α : Type} [LinearOrder α]

/-- A directed adjacent sorting gallery. Labels here are occurrences, not
facet names. Every crossing removes an inversion in the target order. -/
inductive Program : List α → List α → Type
  | refl (a : List α) : Program a a
  | step (left : List α) (a b : α) (right : List α) (h : b < a)
      {out : List α} (next : Program (left ++ b :: a :: right) out) :
      Program (left ++ a :: b :: right) out

namespace Program
variable {a b c : List α}
def events : {a b : List α} → Program a b → List (α × α)
  | _,_,.refl _ => []
  | _,_,.step _ a b _ _ p => (b,a) :: p.events

def trans : {a b c : List α} → Program a b → Program b c → Program a c
  | _,_,_,.refl _,q => q
  | _,_,_,.step l x y r h p,q => .step l x y r h (p.trans q)

lemma events_trans (p : Program a b) (q : Program b c) :
    (p.trans q).events = p.events ++ q.events := by
  induction p with
  | refl _ => rfl
  | step l x y r h p ih => exact congrArg (List.cons (y,x)) (ih q)

def reindex {a b a' b' : List α} (ha : a = a') (hb : b = b')
    (p : Program a b) : Program a' b' := ha ▸ hb ▸ p

lemma events_reindex {a b a' b' : List α} (ha : a = a') (hb : b = b')
    (p : Program a b) : (p.reindex ha hb).events = p.events := by
  subst a'
  subst b'
  rfl

def prepend (l : List α) : {a b : List α} → Program a b → Program (l ++ a) (l ++ b)
  | _,_,.refl a => .refl (l++a)
  | _,_,.step k x y r h p =>
    (Program.step (l++k) x y r h
      ((p.prepend l).reindex (List.append_assoc l k (y::x::r)).symm rfl)).reindex
      (List.append_assoc l k (x::y::r)) rfl

lemma events_prepend (l : List α) (p : Program a b) :
    (p.prepend l).events = p.events := by
  induction p with
  | refl a => rfl
  | step k x y r h p ih =>
    simp only [prepend, events_reindex, events, ih]

lemma perm (p : Program a b) : a.Perm b := by
  induction p with
  | refl a => exact List.Perm.refl _
  | step l x y r h p ih => exact ((List.Perm.swap y x r).append_left l).trans ih

/-- Insertion moves the one new label right, crossing each encountered label
at most once. The recursive tail sorting never involves this new occurrence. -/
theorem insert (x : α) (l : List α) (hl : l.Nodup) :
    ∃ p : Program (x :: l) (l.orderedInsert (· ≤ ·) x),
      p.events.Nodup ∧ ∀ e ∈ p.events, e.2 = x ∧ e.1 ∈ l ∧ e.1 < x := by
  induction l with
  | nil => exact ⟨.refl [x],List.nodup_nil,by simp [events]⟩
  | cons y l ih =>
    by_cases hxy : x ≤ y
    · rw [List.orderedInsert_cons_of_le _ _ hxy]
      exact ⟨.refl _,List.nodup_nil,by simp [events]⟩
    · rw [List.orderedInsert_of_not_le _ _ hxy]
      obtain ⟨p,hp,hm⟩ := ih hl.of_cons
      let q : Program (x :: y :: l) (y :: l.orderedInsert (· ≤ ·) x) :=
        .step [] x y l (lt_of_not_ge hxy) (p.prepend [y])
      refine ⟨q,?_,?_⟩
      · change ((y,x)::(p.prepend [y]).events).Nodup
        rw [events_prepend,List.nodup_cons]
        refine ⟨?_,hp⟩
        intro he
        exact (List.nodup_cons.mp hl).1 (hm _ he).2.1
      · intro e he
        change e ∈ (y,x)::(p.prepend [y]).events at he
        rw [events_prepend,List.mem_cons] at he
        rcases he with rfl|he
        · exact ⟨rfl,List.mem_cons_self,lt_of_not_ge hxy⟩
        · exact ⟨(hm _ he).1,List.mem_cons_of_mem _ (hm _ he).2.1,(hm _ he).2.2⟩

/-- Constructive no-recrossing sort. Its event list names the actual pair of
occurrences exchanged at each adjacent vertex, and contains no repetition. -/
theorem sort (l : List α) (hl : l.Nodup) :
    ∃ p : Program l (l.insertionSort (· ≤ ·)), p.events.Nodup ∧
      ∀ e ∈ p.events, e.1 ∈ l ∧ e.2 ∈ l ∧ e.1 < e.2 := by
  induction l with
  | nil => exact ⟨.refl [],List.nodup_nil,by simp [events]⟩
  | cons x l ih =>
    change ∃ p : Program (x::l) ((l.insertionSort (· ≤ ·)).orderedInsert (· ≤ ·) x),
      p.events.Nodup ∧ ∀ e ∈ p.events, e.1 ∈ x::l ∧ e.2 ∈ x::l ∧ e.1 < e.2
    obtain ⟨p,hp,hm⟩ := ih hl.of_cons
    have hsorted : (l.insertionSort (· ≤ ·)).Nodup :=
      (List.perm_insertionSort _ _).nodup_iff.mpr hl.of_cons
    obtain ⟨q,hq,hn⟩ := insert x (l.insertionSort (· ≤ ·)) hsorted
    refine ⟨(p.prepend [x]).trans q,?_,?_⟩
    · rw [events_trans,events_prepend,List.nodup_append]
      refine ⟨hp,hq,?_⟩
      intro e he e' he' heq
      subst e'
      have h := (hm _ he).2.1
      rw [(hn _ he').1] at h
      exact (List.nodup_cons.mp hl).1 h
    · intro e he
      rw [events_trans,events_prepend,List.mem_append] at he
      rcases he with he|he
      · exact ⟨List.mem_cons_of_mem _ (hm _ he).1,
          List.mem_cons_of_mem _ (hm _ he).2.1,(hm _ he).2.2⟩
      · exact ⟨List.mem_cons_of_mem _ ((List.mem_insertionSort _).mp (hn _ he).2.1),
          (hn _ he).1 ▸ List.mem_cons_self, (hn _ he).1 ▸ (hn _ he).2.2⟩
end Program
end IntegralCharacterVarieties.DirectedSort

namespace IntegralCharacterVarieties.DirectedSort.Program
open scoped Classical
/-- Sorting an arbitrary finite enumeration ends at the literal target order;
no abstract change of labels is applied afterwards. -/
theorem sort_equiv {m n : ℕ} (e : Fin m ≃ Fin n) :
    ∃ p : Program (List.ofFn e) (List.finRange n), p.events.Nodup := by
  have hn : (List.ofFn e).Nodup := List.nodup_ofFn.mpr e.injective
  have hperm : (List.ofFn e).Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup hn (List.nodup_finRange n)).mpr
    intro k
    constructor
    · intro _; exact List.mem_finRange _
    · intro _; exact List.mem_ofFn.mpr ⟨e.symm k,e.apply_symm_apply k⟩
  have hs : (List.ofFn e).insertionSort (· ≤ ·) = List.finRange n := by
    apply List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
      (List.pairwise_insertionSort _ _) (List.pairwise_le_finRange n)
    exact (List.perm_insertionSort _ _).trans hperm
  obtain ⟨p,hp,_⟩ := sort (List.ofFn e) hn
  exact ⟨p.reindex rfl hs,by rwa [events_reindex]⟩
end IntegralCharacterVarieties.DirectedSort.Program
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

def adjacentIndex (l : List F) (x y : F) (r : List F) :
    Fin ((l ++ x :: y :: r).length - 1) :=
  ⟨l.length,by simp only [List.length_append,List.length_cons]; omega⟩

lemma adjacent_ofFn (l : List F) (x y : F) (r : List F) :
    List.ofFn ((l ++ x :: y :: r).get ∘
      (Passage.interchange (adjacentIndex l x y r)).permutation.symm) =
    l ++ y :: x :: r := by
  apply List.ext_getElem (by simp [Nat.add_assoc])
  intro k hk hk'
  simp only [List.getElem_ofFn,Function.comp_apply,Passage.permutation,Equiv.symm_swap,
    Equiv.swap_apply_def,adjacentIndex,Fin.ext_iff,Fin.val_mk]
  by_cases hka : k = l.length
  · subst k
    simp [List.get_eq_getElem,List.getElem_append_right]
  · by_cases hkb : k = l.length+1
    · subst k
      simp [List.get_eq_getElem,List.getElem_append_right]
    · simp only [hka,hkb,ite_false,List.get_eq_getElem]
      by_cases hkl : k < l.length
      · rw [List.getElem_append_left hkl,List.getElem_append_left hkl]
      · rw [List.getElem_append_right (by omega),List.getElem_append_right (by omega)]
        have hz : k-l.length ≠ 0 := by omega
        have ho : k-l.length-1 ≠ 0 := by omega
        simp [List.getElem_cons,hz,ho]

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

/-- Literal child lists for one adjacent event; the decoration is exactly the
allowed passage table, with its full two-block identified quotient. -/
def OrderedStep.adjacent (parent : F) (l : List F) (x y : F) (r : List F) :
    OrderedStep parent (l ++ x :: y :: r) (l ++ y :: x :: r) where
  kind := .passage (l ++ x :: y :: r).length (.interchange (adjacentIndex l x y r))
  decoration := passageDecoration (.interchange (adjacentIndex l x y r)) parent
    (l ++ x :: y :: r).get
  input_parent := rfl
  output_parent := rfl
  input_children := List.ofFn_get _
  output_children := adjacent_ofFn l x y r

def OrderedStep.reindex {parent : F} {a b a' b' : List F}
    (s : OrderedStep parent a b) (ha : a = a') (hb : b = b') : OrderedStep parent a' b' where
  kind := s.kind
  decoration := s.decoration
  input_parent := s.input_parent
  output_parent := s.output_parent
  input_children := s.input_children.trans ha
  output_children := s.output_children.trans hb

lemma OrderedStep.adjacent_conservative (rnk : F → ℕ) (parent : F)
    (l : List F) (x y : F) (r : List F)
    (h : rnk parent = listRank rnk (l ++ x :: y :: r)) :
    (adjacent parent l x y r).decoration.Conservative rnk :=
  passage_conservative rnk parent _ _ (by simpa only [List.ofFn_get] using h)

lemma OrderedStep.adjacent_fresh (l : List F) (x y : F) (r : List F) :
    let s := adjacent none (l.map some) (some x) (some y) (r.map some)
    ∃ d : s.kind.SecondaryNames F, s.decoration = s.kind.freshDecoration d := by
  dsimp only
  refine ⟨(fun j => (l ++ x :: y :: r).get
    (Fin.cast (by simp [Nat.add_assoc]) j)), ?_⟩
  simp only [adjacent,Kind.freshDecoration]
  congr 1
  funext j
  simp only [List.get_eq_getElem,Fin.val_cast,← List.map_cons,← List.map_append,
    List.getElem_map]

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.DirectedSort.Program
open scoped Classical
open OccurrenceIncidence.VertexTable
variable {α F : Type} [LinearOrder α] {a b : List α} {N : ℕ} {r : F → ℕ}

/-- A direct realization of the displayed program, one literal passage for
each recorded adjacent crossing. It does not choose an arbitrary permutation
word after forgetting the no-recrossing property. -/
noncomputable def ranked (f : α → F) (p : Program a b)
    (hp : N = listRank r (a.map f)) :
    RankedChain (freshRank N r) none ((a.map f).map some) ((b.map f).map some) := by
  induction p with
  | refl a => exact .refl _
  | step l x y rt hyx p ih =>
    let s0 := OrderedStep.adjacent none ((l.map f).map some) (some (f x)) (some (f y))
      ((rt.map f).map some)
    let s : OrderedStep none (((l++x::y::rt).map f).map some)
        (((l++y::x::rt).map f).map some) := s0.reindex (by simp only [List.map_append,List.map_cons])
      (by simp only [List.map_append,List.map_cons])
    have hs : s.decoration.Conservative (freshRank N r) := by
      apply OrderedStep.adjacent_conservative
      simpa only [← List.map_cons,← List.map_append,listRank_some,freshRank] using hp
    have hn : N = listRank r ((l++y::x::rt).map f) := by
      simpa only [List.map_append,List.map_cons,listRank_append,listRank_cons,
        add_comm,add_left_comm,add_assoc] using hp
    exact .step s hs (ih hn)

lemma ranked_fresh (f : α → F) (p : Program a b) (hp : N = listRank r (a.map f)) :
    (p.ranked f hp).Fresh := by
  induction p with
  | refl a => trivial
  | step l x y rt hyx p ih =>
    change (∃ d : (OrderedStep.adjacent none ((l.map f).map some) (some (f x))
      (some (f y)) ((rt.map f).map some)).kind.SecondaryNames F, _) ∧ _
    exact ⟨OrderedStep.adjacent_fresh (l.map f) (f x) (f y) (rt.map f), ih _⟩

lemma ranked_length (f : α → F) (p : Program a b) (hp : N = listRank r (a.map f)) :
    (p.ranked f hp).forget.walk.length = p.events.length := by
  induction p with
  | refl a => rfl
  | step l x y rt hyx p ih =>
    change ((p.ranked f _).forget.walk.length+1) = p.events.length+1
    exact congrArg (· + 1) (ih _)

end IntegralCharacterVarieties.DirectedSort.Program
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

/-- Actual crossing pairs read from the literal vertex decoration, with the
right (moving left) label first. Splits, merges and continuations do not add
crossings. This retains occurrence labels when the colours label occurrences. -/
def Decoration.crossings : {k : Kind} → Decoration k F → List (F × F)
  | .passage _ (.interchange i),d =>
    [(d.color ⟨false,some ⟨i.val+1,by omega⟩⟩,
      d.color ⟨false,some ⟨i.val,by omega⟩⟩)]
  | .passage _ .continuation,_ => []
  | .splitting _ _ _ _,_ => []

lemma OrderedStep.adjacent_crossings (parent : F) (l : List F) (x y : F) (r : List F) :
    (adjacent parent l x y r).decoration.crossings = [(y,x)] := by
  simp [adjacent,Decoration.crossings,passageDecoration,adjacentIndex,
    List.get_eq_getElem,List.getElem_append_right]

namespace RankedChain
variable {r : F → ℕ} {parent : F}
def crossings : {a b : List F} → RankedChain r parent a b → List (F × F)
  | _,_,.refl _ => []
  | _,_,.step s _ p => s.decoration.crossings ++ p.crossings

lemma crossings_trans {a b c : List F} (p : RankedChain r parent a b)
    (q : RankedChain r parent b c) : (p.trans q).crossings = p.crossings ++ q.crossings := by
  induction p with
  | refl a => rfl
  | step s hs p ih => simp only [trans,crossings,ih,List.append_assoc]
end RankedChain
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.DirectedSort.Program
open scoped Classical
open OccurrenceIncidence.VertexTable
variable {α F : Type} [LinearOrder α] {a b : List α} {N : ℕ} {r : F → ℕ}

lemma ranked_crossings (f : α → F) (p : Program a b) (hp : N = listRank r (a.map f)) :
    (p.ranked f hp).crossings = p.events.map (fun e => (some (f e.1),some (f e.2))) := by
  induction p with
  | refl a => rfl
  | step l x y rt hyx p ih =>
    change (OrderedStep.adjacent none ((l.map f).map some) (some (f x)) (some (f y))
      ((rt.map f).map some)).decoration.crossings ++ (p.ranked f _).crossings = _
    rw [OrderedStep.adjacent_crossings,ih]
    rfl

lemma ranked_no_recrossing (f : α → F) (hf : Function.Injective f)
    (p : Program a b) (hp : N = listRank r (a.map f)) (he : p.events.Nodup) :
    (p.ranked f hp).crossings.Nodup := by
  rw [ranked_crossings]
  apply he.map
  intro u v huv
  apply Prod.ext
  · exact hf (Option.some.inj (congrArg Prod.fst huv))
  · exact hf (Option.some.inj (congrArg Prod.snd huv))

end IntegralCharacterVarieties.DirectedSort.Program
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} {N : ℕ} {r : F → ℕ}

namespace RankedChain
variable {a b a' b' : List (Option F)}
def reindex (p : RankedChain (freshRank N r) none a b) (ha : a=a') (hb : b=b') :
    RankedChain (freshRank N r) none a' b' := ha ▸ hb ▸ p
lemma reindex_fresh (p : RankedChain (freshRank N r) none a b) (ha : a=a') (hb : b=b')
    (hp : p.Fresh) : (p.reindex ha hb).Fresh := by subst a'; subst b'; exact hp
lemma reindex_crossings (p : RankedChain (freshRank N r) none a b) (ha : a=a') (hb : b=b') :
    (p.reindex ha hb).crossings=p.crossings := by subst a'; subst b'; rfl
end RankedChain

/-- A refinement/coarsening containing no crossings, with actual fresh names. -/
def CleanGallery (N : ℕ) (r : F → ℕ) (a b : List F) : Prop :=
  ∃ p : RankedChain (freshRank N r) none (a.map some) (b.map some),
    p.Fresh ∧ p.crossings=[]

namespace CleanGallery
lemma refl (a : List F) : CleanGallery N r a a := ⟨.refl _,trivial,rfl⟩
lemma trans {a b c : List F} (p : CleanGallery N r a b) (q : CleanGallery N r b c) :
    CleanGallery N r a c := by
  obtain ⟨p,hp,hpc⟩ := p
  obtain ⟨q,hq,hqc⟩ := q
  exact ⟨p.trans q,p.fresh_trans q hp hq,by rw [RankedChain.crossings_trans,hpc,hqc]; rfl⟩

lemma split (big : F) (left mid right : List F)
    (hp : N = listRank r (left ++ big :: right)) (hm : r big = listRank r mid) :
    CleanGallery N r (left ++ big :: right) (left ++ (mid ++ right)) := by
  have hp' : freshRank N r none = listRank (freshRank N r)
      (left.map some ++ some big :: right.map some) := by
    simpa only [← List.map_cons, ← List.map_append, listRank_some, freshRank] using hp
  have hm' : freshRank N r (some big) = listRank (freshRank N r) (mid.map some) := by
    simpa only [listRank_some, freshRank] using hm
  let c := RankedChain.split (some big) (left.map some) (mid.map some) (right.map some) hp' hm'
  have h : c.Fresh := by
    refine RankedChain.fresh_single _ _ ?_
    refine ⟨(big, (fun j => left.get (Fin.cast (List.length_map ..) j)),
      (fun j => mid.get (Fin.cast (List.length_map ..) j)),
      (fun j => right.get (Fin.cast (List.length_map ..) j))), ?_⟩
    simp only [OrderedStep.split, splitLists, Kind.freshDecoration]
    congr 1 <;> funext j <;> simp [List.get_eq_getElem]
  let p : RankedChain (freshRank N r) none ((left ++ big :: right).map some)
      ((left ++ (mid ++ right)).map some) := c.reindex (by simp only [List.map_append,List.map_cons])
    (by simp only [List.map_append])
  exact ⟨p,c.reindex_fresh _ _ h,by rw [RankedChain.reindex_crossings]; rfl⟩

lemma merge (big : F) (left mid right : List F)
    (hp : N = listRank r (left ++ big :: right)) (hm : r big = listRank r mid) :
    CleanGallery N r (left ++ (mid ++ right)) (left ++ big :: right) := by
  have hp' : freshRank N r none = listRank (freshRank N r)
      (left.map some ++ some big :: right.map some) := by
    simpa only [← List.map_cons, ← List.map_append, listRank_some, freshRank] using hp
  have hm' : freshRank N r (some big) = listRank (freshRank N r) (mid.map some) := by
    simpa only [listRank_some, freshRank] using hm
  let c := RankedChain.merge (some big) (left.map some) (mid.map some) (right.map some) hp' hm'
  have h : c.Fresh := by
    refine RankedChain.fresh_single _ _ ?_
    refine ⟨(big, (fun j => left.get (Fin.cast (List.length_map ..) j)),
      (fun j => mid.get (Fin.cast (List.length_map ..) j)),
      (fun j => right.get (Fin.cast (List.length_map ..) j))), ?_⟩
    simp only [OrderedStep.merge, splitLists, Kind.freshDecoration]
    congr 1 <;> funext j <;> simp [List.get_eq_getElem]
  let p : RankedChain (freshRank N r) none ((left ++ (mid ++ right)).map some)
      ((left ++ big :: right).map some) := c.reindex (by simp only [List.map_append])
    (by simp only [List.map_append,List.map_cons])
  exact ⟨p,c.reindex_fresh _ _ h,by rw [RankedChain.reindex_crossings]; rfl⟩

lemma refine_rows (rows : List (F × List F)) (left right : List F)
    (hp : N = listRank r (left ++ (rows.map Prod.fst ++ right)))
    (hr : ∀ x ∈ rows, r x.1 = listRank r x.2) :
    CleanGallery N r (left ++ (rows.map Prod.fst ++ right))
      (left ++ (rows.flatMap Prod.snd ++ right)) ∧
    CleanGallery N r (left ++ (rows.flatMap Prod.snd ++ right))
      (left ++ (rows.map Prod.fst ++ right)) := by
  induction rows generalizing left with
  | nil => exact ⟨.refl _, .refl _⟩
  | cons x rows ih =>
    have hx := hr x (by simp)
    have ht : ∀ y ∈ rows, r y.1 = listRank r y.2 := fun y hy => hr y (by simp [hy])
    have hp' : N = listRank r ((left ++ x.2) ++ (rows.map Prod.fst ++ right)) := by
      simpa only [List.map_cons,listRank_append,listRank_cons,hx,add_assoc] using hp
    obtain ⟨p,q⟩ := ih (left ++ x.2) hp' ht
    constructor
    · have h := (split x.1 left x.2 (rows.map Prod.fst ++ right) hp hx).trans
        (by simpa [List.append_assoc] using p)
      simpa [List.append_assoc] using h
    · have h := q.trans (by simpa [List.append_assoc] using
        (merge x.1 left x.2 (rows.map Prod.fst ++ right) hp hx))
      simpa [List.append_assoc] using h
end CleanGallery
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} {N : ℕ} {r : F → ℕ}

/-- A genuinely fresh ranked gallery whose literal passage trace never repeats
an ordered pair of occurrence labels. -/
def ReducedGallery (N : ℕ) (r : F → ℕ) (a b : List F) : Prop :=
  ∃ p : RankedChain (freshRank N r) none (a.map some) (b.map some),
    p.Fresh ∧ p.crossings.Nodup

namespace ReducedGallery
lemma clean_left {a b c : List F} (p : CleanGallery N r a b) (q : ReducedGallery N r b c) :
    ReducedGallery N r a c := by
  obtain ⟨p,hp,hpc⟩ := p
  obtain ⟨q,hq,hqc⟩ := q
  exact ⟨p.trans q,p.fresh_trans q hp hq,by rw [RankedChain.crossings_trans,hpc]; exact hqc⟩
lemma clean_right {a b c : List F} (p : ReducedGallery N r a b) (q : CleanGallery N r b c) :
    ReducedGallery N r a c := by
  obtain ⟨p,hp,hpc⟩ := p
  obtain ⟨q,hq,hqc⟩ := q
  exact ⟨p.trans q,p.fresh_trans q hp hq,by rw [RankedChain.crossings_trans,hqc,List.append_nil]; exact hpc⟩

/-- The finite program is built in the target column order. Each block is
labelled by its occurrence, even when ranks and underlying modules coincide. -/
lemma rectangular {m n : ℕ} (f : Fin m → Fin n → F)
    (hinj : Function.Injective (fun p : Fin m × Fin n => f p.1 p.2))
    (hf : N = listRank r ((List.ofFn fun i => List.ofFn (f i)).flatten)) :
    ReducedGallery N r ((List.ofFn fun i => List.ofFn (f i)).flatten)
      ((List.ofFn fun j => List.ofFn fun i => f i j).flatten) := by
  let e := gridTranspose m n
  let g : Fin (n*m) → F := fun k => f (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  have hg : Function.Injective g := by
    intro x y h
    have hxy := @hinj ((finProdFinEquiv.symm x).2,(finProdFinEquiv.symm x).1)
      ((finProdFinEquiv.symm y).2,(finProdFinEquiv.symm y).1) h
    apply finProdFinEquiv.symm.injective
    exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  have ha : (List.ofFn e).map g = (List.ofFn fun i => List.ofFn (f i)).flatten := by
    rw [List.map_ofFn]
    have H : (fun k : Fin (m*n) => g (e k)) =
        (fun k : Fin (m*n) => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
      funext k
      change f (finProdFinEquiv.symm (finProdFinEquiv
        ((finProdFinEquiv.symm k).2,(finProdFinEquiv.symm k).1))).2
        (finProdFinEquiv.symm (finProdFinEquiv
        ((finProdFinEquiv.symm k).2,(finProdFinEquiv.symm k).1))).1 = _
      rw [Equiv.symm_apply_apply]
    change List.ofFn (fun k => g (e k)) = _
    rw [H,matrix_list]
  have hb : (List.finRange (n*m)).map g =
      (List.ofFn fun j => List.ofFn fun i => f i j).flatten := by
    rw [← List.ofFn_id,List.map_ofFn]
    exact matrix_list (fun j i => f i j)
  obtain ⟨p,hp⟩ := DirectedSort.Program.sort_equiv e
  have hrank : N = listRank r ((List.ofFn e).map g) := ha.symm ▸ hf
  let q := p.ranked g hrank
  let q' : RankedChain (freshRank N r) none
      (((List.ofFn fun i => List.ofFn (f i)).flatten).map some)
      (((List.ofFn fun j => List.ofFn fun i => f i j).flatten).map some) :=
    q.reindex (congrArg (List.map some) ha) (congrArg (List.map some) hb)
  refine ⟨q',q.reindex_fresh _ _ (p.ranked_fresh g hrank),?_⟩
  rw [RankedChain.reindex_crossings]
  exact p.ranked_no_recrossing g hg hrank hp

lemma two_flag_gallery {m n : ℕ} (row : Fin m → F) (col : Fin n → F)
    (grid : Fin m → Fin n → F)
    (hinj : Function.Injective (fun p : Fin m × Fin n => grid p.1 p.2))
    (hp : N = ∑ i, r (row i))
    (hr : ∀ i, r (row i) = ∑ j, r (grid i j))
    (hc : ∀ j, r (col j) = ∑ i, r (grid i j)) :
    ReducedGallery N r (List.ofFn row) (List.ofFn col) := by
  have hpc : N = ∑ j, r (col j) := by
    rw [hp]
    simp_rw [hr,hc]
    exact Finset.sum_comm
  have Hrows : ∀ x ∈ (List.ofFn fun i => (row i,List.ofFn (grid i))),
      r x.1 = listRank r x.2 := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hr i
  have Hcols : ∀ x ∈ (List.ofFn fun j => (col j,List.ofFn fun i => grid i j)),
      r x.1 = listRank r x.2 := by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    simpa only [listRank_ofFn] using hc j
  have hrow := (CleanGallery.refine_rows (List.ofFn fun i => (row i,List.ofFn (grid i))) [] []
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hp) Hrows).1
  have hcol := (CleanGallery.refine_rows (List.ofFn fun j => (col j,List.ofFn fun i => grid i j)) [] []
    (by simpa only [List.nil_append,List.append_nil,List.map_ofFn,Function.comp_apply,listRank_ofFn] using hpc) Hcols).2
  simp only [List.nil_append,List.append_nil,List.flatMap_def,List.map_ofFn] at hrow hcol
  have hgrid : N = listRank r ((List.ofFn fun i => List.ofFn (grid i)).flatten) := by
    simp only [listRank_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply,listRank_ofFn]
    simpa only [hr] using hp
  exact clean_left hrow (clean_right (rectangular grid hinj hgrid) hcol)
end ReducedGallery
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

end OAI
