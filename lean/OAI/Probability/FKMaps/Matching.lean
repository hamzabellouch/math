import OAI.Probability.FKMaps.GraphWedge
import OAI.Probability.FKMaps.WordMaps

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
variable {N : ℕ}

def liveAt (a : Perm (Fin N)) (k : ℕ) : List (Fin N) :=
  ((List.finRange N).filter (fun x => decide (x.val<k ∧ k≤(a x).val))).reverse

lemma mem_liveAt (a : Perm (Fin N)) (k : ℕ) (x : Fin N) :
    x∈liveAt a k ↔ x.val<k ∧ k≤(a x).val := by simp [liveAt]

lemma liveAt_sorted (a : Perm (Fin N)) (k : ℕ) : (liveAt a k).Pairwise (·>·) := by
  exact ((List.pairwise_lt_finRange N).filter _).reverse

lemma liveAt_zero (a : Perm (Fin N)) : liveAt a 0=[] := by simp [liveAt]
lemma liveAt_end (a : Perm (Fin N)) : liveAt a N=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have := (mem_liveAt a N x).mp hx
  omega

lemma liveAt_open (a : Perm (Fin N)) (ha : Function.Involutive a) (i : Fin N)
    (hi : i < a i) : liveAt a (i.val+1)=i::liveAt a i.val := by
  have hs : (i::liveAt a i.val).Pairwise (·>·) :=
    List.pairwise_cons.mpr ⟨fun x hx => (mem_liveAt a i.val x).mp hx |>.1,liveAt_sorted a _⟩
  apply List.Pairwise.eq_of_mem_iff (liveAt_sorted a _) hs
  intro x
  rw [mem_liveAt,List.mem_cons,mem_liveAt]
  have hx : a x=i → x=a i := fun h => by rw [← h,ha]
  constructor
  · rintro ⟨h1,h2⟩
    by_cases hxi : x=i
    · exact Or.inl hxi
    · exact Or.inr ⟨by have := Fin.val_ne_of_ne hxi; omega,by omega⟩
  · rintro (rfl|⟨h1,h2⟩)
    · exact ⟨by omega,hi⟩
    · refine ⟨by omega,?_⟩
      by_contra hh
      have he : a x=i := Fin.ext (by omega)
      have he' := hx he
      subst x
      have hi' : i.val<(a i).val := hi
      omega

lemma liveAt_close (a : Perm (Fin N)) (ha : Function.Involutive a) (i : Fin N)
    (hi : a i < i) : liveAt a (i.val+1)=(liveAt a i.val).erase (a i) := by
  apply List.Pairwise.eq_of_mem_iff (liveAt_sorted a _) ((liveAt_sorted a _).sublist List.erase_sublist)
  intro x
  rw [mem_liveAt,(liveAt_sorted a _).nodup.mem_erase_iff,mem_liveAt]
  have hx : x=a i ↔ a x=i := by
    constructor
    · intro h; rw [h,ha]
    · intro h; rw [← h,ha]
  have hi' : (a i).val < i.val := hi
  constructor
  · rintro ⟨h1,h2⟩
    refine ⟨?_,?_,by omega⟩
    · intro he; have := hx.mp he; subst x; rw [ha] at h2; omega
    · by_contra h
      have he : x=i := Fin.ext (by omega)
      subst x
      omega
  · rintro ⟨h1,h2,h3⟩
    refine ⟨by omega,?_⟩
    by_contra h
    have he : a x=i := Fin.ext (by omega)
    exact h1 (hx.mpr he)

lemma liveAt_mate (a : Perm (Fin N)) (ha : Function.Involutive a) (i : Fin N)
    (hi : a i < i) : a i∈liveAt a i.val := by rw [mem_liveAt,ha]; exact ⟨hi,le_rfl⟩

lemma pop_map_erase {α : Type*} [DecidableEq α] (c : α→Bool) (s : List α) (x : α)
    (hx : x∈s) (hfirst : ∀ t u,s=t++x::u → ∀ y∈t,c y≠c x) :
    pop (some (c x)) (s.map c)=some ((s.erase x).map c) := by
  induction s with
  | nil => simp at hx
  | cons y s ih =>
    by_cases hy : y=x
    · subst y; simp [pop,eligible]
    · have hxs : x∈s := List.mem_of_ne_of_mem (Ne.symm hy) hx
      obtain ⟨t,u,htu⟩ := List.mem_iff_append.mp hxs
      have hcy := hfirst (y::t) u (by rw [htu]; rfl) y (by simp)
      have hh := ih hxs (by
        intro t u he z hz
        exact hfirst (y::t) u (by rw [he]; rfl) z (List.mem_cons_of_mem y hz))
      simp [pop,eligible,Ne.symm hcy,hy,hh]

/-- For noncrossing same-colour arcs, the literal typed stack is the list of
live openers in reverse chronological order. No choice of a stack matching
is assumed. -/
lemma matching_step_live (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ x,a x≠x) (c : Fin N→Bool) (hc : ∀ x,c (a x)=c x)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False) (i : Fin N) :
    stackTypedStep ((liveAt a i.val).map c)
      (if i < a i then .burger (c i) else .order (c i))=
        some ((liveAt a (i.val+1)).map c) := by
  by_cases hi : i < a i
  · rw [ite_eq_left hi,liveAt_open a ha i hi]
    rfl
  · have hlt : a i < i := lt_of_le_of_ne (le_of_not_gt hi) (hf i)
    rw [ite_eq_right hi,stackTypedStep,liveAt_close a ha i hlt,← hc i]
    apply pop_map_erase c _ _ (liveAt_mate a ha i hlt)
    intro t u he y hy hcy
    have hs := liveAt_sorted a i.val
    rw [he,List.pairwise_append] at hs
    have hiy : a i<y := hs.2.2 y hy (a i) (by simp)
    have hym : y∈liveAt a i.val := he ▸ List.mem_append_left _ hy
    obtain ⟨hy1,hy2⟩ := (mem_liveAt a i.val y).mp hym
    have hneq : a y≠i := fun hh => (ne_of_lt hiy) (by rw [← hh,ha])
    have hy3 : i < a y := by have := Fin.val_ne_of_ne hneq; change (i : ℕ)<(a y : ℕ); omega
    exact hn (a i) y hcy.symm hiy (by rwa [ha]) (by rwa [ha])

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
variable {N : ℕ}

lemma liveAt_first_colour (a : Perm (Fin N)) (ha : Function.Involutive a)
    (c : Fin N→Bool)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False)
    (i : Fin N) (_hi : a i < i) :
    ∀ t u,liveAt a i.val=t++a i::u → ∀ y∈t,c y≠c (a i) := by
  intro t u he y hy hcy
  have hs := liveAt_sorted a i.val
  rw [he,List.pairwise_append] at hs
  have hiy : a i < y := hs.2.2 y hy (a i) (by simp)
  have hym : y∈liveAt a i.val := he ▸ List.mem_append_left _ hy
  obtain ⟨hy1,hy2⟩ := (mem_liveAt a i.val y).mp hym
  have hneq : a y≠i := fun hh => (ne_of_lt hiy) (by rw [← hh,ha])
  have hy3 : i < a y := by have := Fin.val_ne_of_ne hneq; change (i : ℕ)<(a y : ℕ); omega
  exact hn (a i) y hcy.symm hiy (by rwa [ha]) (by rwa [ha])

lemma head_map_eq_of_first {α : Type*} (c : α→Bool) (s : List α) (x : α)
    (hx : x∈s) (hfirst : ∀ t u,s=t++x::u → ∀ y∈t,c y≠c x) :
    (s.map c).head?=some (c x) ↔ s.head?=some x := by
  obtain ⟨t,u,rfl⟩ := List.mem_iff_append.mp hx
  cases t with
  | nil => simp
  | cons y t =>
    have hh := hfirst (y::t) u rfl y (by simp)
    have hy : y≠x := fun he => hh (congrArg c he)
    simp [hh,hy]

lemma head_eq_iff_greatest {α : Type*} [LinearOrder α] (s : List α)
    (hs : s.Pairwise (·>·)) (x : α) (hx : x∈s) :
    s.head?=some x ↔ ∀ y∈s,y≤x := by
  cases s with
  | nil => simp at hx
  | cons z s =>
    simp only [List.head?_cons,Option.some.injEq]
    constructor
    · rintro rfl y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact le_rfl
      · exact ((List.pairwise_cons.mp hs).1 y hy).le
    · intro hh
      have hz := hh z (by simp)
      rcases List.mem_cons.mp hx with rfl|hx
      · rfl
      · exact False.elim (not_lt_of_ge hz ((List.pairwise_cons.mp hs).1 x hx))

/-- The source's flexible-mark obstruction, with the strict first-occurrence
order and both closing endpoints retained exactly. -/
theorem flexibleClosing_iff_no_later_cross (a : Perm (Fin N)) (ha : Function.Involutive a)
    (c : Fin N→Bool) (hc : ∀ x,c (a x)=c x)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False)
    (i : Fin N) (hi : a i < i) :
    flexibleClosing ((liveAt a i.val).map c) (.order (c i)) ↔
      ¬∃ j : Fin N,a i < j ∧ j < i ∧ i < a j := by
  change (List.map c (liveAt a i.val)).head?=some (c i) ↔ _
  rw [← hc i,head_map_eq_of_first c _ _ (liveAt_mate a ha i hi)
    (liveAt_first_colour a ha c hn i hi),
    head_eq_iff_greatest _ (liveAt_sorted a _) _ (liveAt_mate a ha i hi)]
  constructor
  · intro hh ⟨j,h1,h2,h3⟩
    exact not_lt_of_ge (hh j ((mem_liveAt a _ j).mpr ⟨h2,h3.le⟩)) h1
  · intro hh j hj
    by_contra h
    obtain ⟨h2,h3⟩ := (mem_liveAt a _ j).mp hj
    have h1 : a i < j := lt_of_not_ge h
    have hne : a j≠i := fun he => (ne_of_lt h1) (by rw [← he,ha])
    have h4 : i < a j := by have := Fin.val_ne_of_ne hne; change i.val<(a j).val; omega
    exact hh ⟨j,h1,h2,h4⟩

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

lemma flexibleCount_ofFn {N : ℕ} (w : Fin N→TypedLetter) (S : Fin (N+1)→List Bool)
    (hs : ∀ i,stackTypedStep (S i.castSucc) (w i)=some (S i.succ)) :
    flexibleCount (List.ofFn w) (S 0)=
      ∑ i,if flexibleClosing (S i.castSucc) (w i) then 1 else 0 := by
  induction N with
  | zero => simp [flexibleCount]
  | succ N ih =>
    have h0 := hs 0
    simp only [Fin.castSucc_zero] at h0
    rw [List.ofFn_succ,flexibleCount,h0,Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero]
    congr 1
    exact ih (fun i => w i.succ) (fun i => S i.succ) (fun i => hs i.succ)

/-- The complete flexible exponent of the actual identified word is the
number of its matched pairs with no later-first crossing edge. -/
theorem matching_flexibleCount {N : ℕ} (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ x,a x≠x) (c : Fin N→Bool) (hc : ∀ x,c (a x)=c x)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False) :
    flexibleCount (List.ofFn (fun i => if i<a i then .burger (c i) else .order (c i))) []=
      ∑ i : Fin N,if a i < i ∧ ¬∃ j : Fin N,a i < j ∧ j < i ∧ i < a j then 1 else 0 := by
  let w : Fin N→TypedLetter := fun i => if i<a i then .burger (c i) else .order (c i)
  let S : Fin (N+1)→List Bool := fun i => (liveAt a i.val).map c
  have hs : ∀ i,stackTypedStep (S i.castSucc) (w i)=some (S i.succ) :=
    matching_step_live a ha hf c hc hn
  have hS : S 0=[] := by simp [S,liveAt_zero]
  rw [← hS,flexibleCount_ofFn w S hs]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i<a i
  · have hn' : ¬a i < i := not_lt_of_ge hi.le
    simp [w,hi,flexibleClosing,hn']
  · have hlt : a i < i := lt_of_le_of_ne (le_of_not_gt hi) (hf i)
    have hh := flexibleClosing_iff_no_later_cross a ha c hc hn i hlt
    change (if flexibleClosing ((liveAt a i.val).map c)
      (if i<a i then .burger (c i) else .order (c i)) then 1 else 0)=_
    simp only [ite_eq_right hi,hh,hlt,true_and]

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT.Chords
variable {N : ℕ}

lemma componentDarts_mate (a : Perm (Fin N)) (ha : Function.Involutive a)
    (r : Opener a) (d : Fin N) :
    a d∈componentDarts a r ↔ d∈componentDarts a r := by
  have hd (i : Fin N) : i∈componentDarts a r → a i∈componentDarts a r := by
    intro hi
    obtain ⟨x,hx,rfl|rfl⟩ := (mem_componentDarts a r i).mp hi
    · exact (mem_componentDarts a r _).mpr ⟨x,hx,Or.inr rfl⟩
    · rw [ha]
      exact (mem_componentDarts a r _).mpr ⟨x,hx,Or.inl rfl⟩
  constructor
  · intro h
    have hh := hd (a d) h
    rw [ha] at hh
    exact hh
  · exact hd d

def opener (a : Perm (Fin N)) (ha : Function.Involutive a) (hf : ∀ d,a d≠d)
    (d : Fin N) : Opener a :=
  if h : d<a d then ⟨d,h⟩ else ⟨a d,by rw [ha]; exact lt_of_le_of_ne (le_of_not_gt h) (hf d)⟩

lemma opener_endpoints (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (d : Fin N) :
    d=(opener a ha hf d).val ∨ d=a (opener a ha hf d).val := by
  unfold opener
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (ha d).symm

lemma gapIndex_mate (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (r : Opener a) (hr : r.val.val=0)
    (d : Fin N) (hd : d∉componentDarts a r) : gapIndex a r (a d)=gapIndex a r d := by
  let f := opener a ha hf d
  have hroot : r.val≤f.val := by change r.val.val≤f.val.val; rw [hr]; omega
  have he := opener_endpoints a ha hf d
  have hn : ¬(graph a).Reachable r f := fun h => hd ((mem_componentDarts a r d).mpr ⟨f,h,he⟩)
  have hh := exterior_same_gap a ha r f hroot hn
  rcases he with he|he
  · rw [he]; exact hh.symm
  · rw [he,ha]; exact hh

def cornerDarts (a : Perm (Fin N)) (r : Opener a) (k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun d => d∉componentDarts a r ∧ gapIndex a r d=k)

lemma cornerDarts_mate (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (r : Opener a) (hr : r.val.val=0) (d : Fin N) (k : ℕ) :
    a d∈cornerDarts a r k ↔ d∈cornerDarts a r k := by
  simp only [cornerDarts,Finset.mem_filter,Finset.mem_univ,true_and,componentDarts_mate a ha]
  by_cases hd : d∈componentDarts a r
  · simp [hd]
  · simp only [gapIndex_mate a ha hf r hr d hd]

lemma component_card_even (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (S : Finset (Fin N)) (hS : ∀ d∈S,a d∈S) :
    S.card=2*(S.filter (fun d => d<a d)).card := by
  let O := S.filter (fun d => d<a d)
  have he : S=O∪O.image a := by
    ext d
    simp only [Finset.mem_union,Finset.mem_image]
    constructor
    · intro hd
      by_cases h : d<a d
      · exact Or.inl (Finset.mem_filter.mpr ⟨hd,h⟩)
      · refine Or.inr ⟨a d,?_,ha d⟩
        apply Finset.mem_filter.mpr
        exact ⟨hS d hd,by rw [ha]; exact lt_of_le_of_ne (le_of_not_gt h) (hf d)⟩
    · rintro (hd|⟨i,hi,rfl⟩)
      · exact Finset.mem_of_mem_filter _ hd
      · exact hS i (Finset.mem_of_mem_filter _ hi)
  have hd : Disjoint O (O.image a) := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd'
    have hi' := (Finset.mem_filter.mp hi).2
    have hd'' := (Finset.mem_filter.mp hd).2
    rw [ha] at hd''
    exact (not_lt_of_ge hi'.le) hd''
  calc
    S.card=(O∪O.image a).card := congrArg Finset.card he
    _=O.card+O.card := by rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ a.injective]
    _=2*O.card := by omega

end Chords
namespace Inventory
open MapCycles
variable {N : ℕ}

def pairWord (a : Perm (Fin N)) (c : Fin N→Bool) (i : Fin N) : TypedLetter :=
  if i<a i then .burger (c i) else .order (c i)

/-- Any pair-closed ordered subword of a two-colour noncrossing matching is
itself an actual successful inventory word. This applies both to a root
crossing component and to each of its corner intervals. -/
theorem typedRun_closed_subword (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ x,a x≠x) (c : Fin N→Bool) (hc : ∀ x,c (a x)=c x)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False)
    (l : List (Fin N)) (hl : l.Pairwise (·<·)) (hclosed : ∀ x∈l,a x∈l) :
    stackTypedRun (l.map (pairWord a c)) []=some [] := by
  have hm (b : Bool) : ∃ E,Arches l E ∧
      (endpoints E).Perm (l.filter (fun i => decide (c i=b))) ∧
      ∀ e∈E,e.2=a e.1 ∧ c e.1=b := by
    obtain ⟨E,hE,hcov,hp⟩ := arches_of_noncrossing a ha (fun i => decide (c i=b))
      (fun i => by rw [hc]) l hl (fun x hx _ => hclosed x hx) (fun x _ _ => hf x)
      (by
        intro x _ y _ hx hy hxy hyx hax
        exact hn x y ((of_decide_eq_true hx).trans (of_decide_eq_true hy).symm) hxy hyx hax)
    exact ⟨E,hE,hcov,fun e he => ⟨(hp e he).1,of_decide_eq_true (hp e he).2⟩⟩
  obtain ⟨E,hE,hce,hpe⟩ := hm true
  obtain ⟨F,hF,hcf,hpf⟩ := hm false
  have hcov : (endpoints (E++F)).Perm l := by
    rw [endpoints_append]
    apply (hce.append hcf).trans
    simpa using List.filter_append_perm c l
  have hlabel (b : Bool) (G : List (Fin N×Fin N)) (hG : Arches l G)
      (hp : ∀ e∈G,e.2=a e.1 ∧ c e.1=b) :
      ∀ e∈G,pairWord a c e.1=.burger b ∧ pairWord a c e.2=.order b := by
    intro e he
    obtain ⟨hpair,hcol⟩ := hp e he
    have hlt := hG.increasing hl e he
    have hmate : a e.2=e.1 := by rw [hpair,ha]
    have hcol' : c e.2=b := by rw [hpair,hc,hcol]
    simp only [pairWord,← hpair,hmate,ite_eq_left hlt,ite_eq_right (not_lt_of_ge hlt.le),hcol,hcol',and_self]
  exact typedRun_of_matchings _ _ hl.nodup E F hE hF hcov (hlabel true E hE hpe) (hlabel false F hF hpf)

/-- Every root component and every one of its literal corner subwords reduce
empty. The conclusion uses the full ordered subword, not independent fresh
words postulated at a random cut. -/
theorem component_and_corners_empty (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ x,a x≠x) (c : Fin N→Bool) (hc : ∀ x,c (a x)=c x)
    (hn : ∀ x y,c x=c y → x < y → y < a x → a x < a y → False)
    (r : Chords.Opener a) (hr : r.val.val=0) :
    stackTypedRun (((List.finRange N).filter (fun d => decide (d∈Chords.componentDarts a r))).map
      (pairWord a c)) []=some [] ∧
    ∀ k,stackTypedRun (((List.finRange N).filter (fun d => decide (d∈Chords.cornerDarts a r k))).map
      (pairWord a c)) []=some [] := by
  constructor
  · apply typedRun_closed_subword a ha hf c hc hn _ ((List.pairwise_lt_finRange N).filter _)
    intro x hx
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] at hx ⊢
    exact (Chords.componentDarts_mate a ha r x).mpr hx
  · intro k
    apply typedRun_closed_subword a ha hf c hc hn _ ((List.pairwise_lt_finRange N).filter _)
    intro x hx
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] at hx ⊢
    exact (Chords.cornerDarts_mate a ha hf r hr x k).mpr hx

end Inventory
end FKCRT
end

end OAI
