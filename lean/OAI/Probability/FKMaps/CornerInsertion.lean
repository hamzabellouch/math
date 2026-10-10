import OAI.Probability.FKMaps.Matching

namespace OAI

noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory

lemma typedStep_suffix {s t r : List Bool} {a : TypedLetter}
    (h : stackTypedStep s a=some t) : stackTypedStep (s++r) a=some (t++r) := by
  cases a with
  | burger b => simpa only [stackTypedStep,Option.some.injEq,List.cons_append] using congrArg (·++r) (Option.some.inj h)
  | order b =>
    simp only [stackTypedStep,pop_fixed] at h ⊢
    split_ifs at h with hb
    · cases h
      rw [ite_eq_left (List.mem_append_left _ hb),List.erase_append_left r hb]

lemma flexibleClosing_suffix {s t r : List Bool} {a : TypedLetter}
    (h : stackTypedStep s a=some t) : flexibleClosing (s++r) a ↔ flexibleClosing s a := by
  cases a with
  | burger b => rfl
  | order b =>
    cases s with
    | nil => simp [stackTypedStep,pop] at h
    | cons c s => rfl

lemma typedRun_suffix {w : List TypedLetter} {s t : List Bool}
    (h : stackTypedRun w s=some t) (r : List Bool) :
    stackTypedRun w (s++r)=some (t++r) ∧ flexibleCount w (s++r)=flexibleCount w s := by
  induction w generalizing s with
  | nil =>
    simp only [stackTypedRun,Option.some.injEq] at h
    subst t
    simp [stackTypedRun,flexibleCount]
  | cons a w ih =>
    cases hs : stackTypedStep s a with
    | none => simp [stackTypedRun,hs] at h
    | some s' =>
      simp only [stackTypedRun,hs,Option.bind_some] at h
      obtain ⟨hr,hf⟩ := ih h
      have hS := typedStep_suffix (r:=r) hs
      constructor
      · simpa [stackTypedRun,hS] using hr
      · simp only [flexibleCount,hS,hs,hf,flexibleClosing_suffix hs]

lemma flexibleCount_append {u : List TypedLetter} (v : List TypedLetter) {s t : List Bool}
    (h : stackTypedRun u s=some t) : flexibleCount (u++v) s=flexibleCount u s+flexibleCount v t := by
  induction u generalizing s with
  | nil =>
    simp only [stackTypedRun,Option.some.injEq] at h
    subst t
    simp [flexibleCount]
  | cons a u ih =>
    cases hs : stackTypedStep s a with
    | none => simp [stackTypedRun,hs] at h
    | some s' =>
      simp only [stackTypedRun,hs,Option.bind_some] at h
      simp only [List.cons_append,flexibleCount,hs,ih h,Nat.add_assoc]

lemma empty_word_context {w : List TypedLetter} (h : stackTypedRun w []=some []) (s : List Bool) :
    stackTypedRun w s=some s ∧ flexibleCount w s=flexibleCount w [] := by
  simpa using typedRun_suffix h s

/-- Literal corner insertion, keeping the root skeleton letters in order. -/
def cornerInsert (l : List (TypedLetter×List TypedLetter)) : List TypedLetter :=
  l.flatMap (fun x => x.1::x.2)

/-- Successful corner words preserve the current stack and have exactly the
same flexible exponent there as from the empty stack. This proves weight
multiplicativity, including empty inserts, with no independence hypothesis. -/
theorem cornerInsert_run_count (l : List (TypedLetter×List TypedLetter))
    (hg : ∀ x∈l,stackTypedRun x.2 []=some []) {s t : List Bool}
    (h : stackTypedRun (l.map Prod.fst) s=some t) :
    stackTypedRun (cornerInsert l) s=some t ∧
      flexibleCount (cornerInsert l) s=flexibleCount (l.map Prod.fst) s+
        (l.map (fun x => flexibleCount x.2 [])).sum := by
  induction l generalizing s with
  | nil => simpa [cornerInsert,stackTypedRun,flexibleCount] using h
  | cons x l ih =>
    cases hs : stackTypedStep s x.1 with
    | none => simp [stackTypedRun,hs] at h
    | some s' =>
      simp only [List.map_cons,stackTypedRun,hs,Option.bind_some] at h
      obtain ⟨hr,hc⟩ := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) h
      obtain ⟨hgr,hgc⟩ := empty_word_context (hg x (List.mem_cons_self)) s'
      constructor
      · simp only [cornerInsert,List.flatMap_cons,List.cons_append,stackTypedRun,hs,Option.bind_some]
        rw [typedRun_append,hgr,Option.bind_some]
        exact hr
      · simp only [cornerInsert,List.flatMap_cons,List.cons_append,flexibleCount,hs,
          List.map_cons,List.sum_cons]
        rw [flexibleCount_append _ hgr,hgc]
        change _+(_+flexibleCount (cornerInsert l) s')=_
        rw [hc]
        omega

end FKCRT.Inventory
end


noncomputable section
open List
namespace FKCRT.CornerSplit
variable {α : Type*}

/-- Split at marked letters, retaining every letter and the possibly empty
prefix before the first mark. The marks themselves label the corners. -/
def split (p : α→Bool) : List α→List α × List (α×List α)
  | [] => ([],[])
  | a::w => let r := split p w
    if p a then ([],(a,r.1)::r.2) else (a::r.1,r.2)

def join (l : List (α×List α)) : List α := l.flatMap (fun x => x.1::x.2)

lemma reassemble (p : α→Bool) (w : List α) :
    (split p w).1++join (split p w).2=w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases hp : p a <;> simpa [split,hp,join] using congrArg (a::·) ih

lemma skeleton (p : α→Bool) (w : List α) :
    ((split p w).2.map Prod.fst)=w.filter p := by
  induction w with
  | nil => rfl
  | cons a w ih => cases hp : p a <;> simp [split,hp,ih]

lemma unmarked_prefix (p : α→Bool) (w : List α) :
    ∀ a∈(split p w).1,p a=false := by
  induction w with
  | nil => simp [split]
  | cons a w ih =>
    cases hp : p a with
    | false => simpa [split,hp] using ih
    | true => simp [split,hp]

lemma marked_corners (p : α→Bool) (w : List α) :
    ∀ x∈(split p w).2,p x.1=true ∧ ∀ a∈x.2,p a=false := by
  induction w with
  | nil => simp [split]
  | cons a w ih =>
    cases hp : p a with
    | false => simpa [split,hp] using ih
    | true =>
      simp only [split,hp,ite_true,List.mem_cons]
      intro x hx
      rcases hx with rfl|hx
      · exact ⟨hp,unmarked_prefix p w⟩
      · exact ih x hx

lemma prefix_nil (p : α→Bool) {a : α} {w : List α} (h : p a=true) :
    (split p (a::w)).1=[] := by simp [split,h]

lemma split_unmarked_append (p : α→Bool) {u : List α}
    (hu : ∀ a∈u,p a=false) (v : List α) :
    split p (u++v)=(u++(split p v).1,(split p v).2) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have ha := hu a (List.mem_cons_self)
    have hh := ih (fun b hb => hu b (List.mem_cons_of_mem _ hb))
    simp [split,ha,hh]

/-- Exact inverse, including empty corner inserts and the final corner. -/
lemma split_join (p : α→Bool) (l : List (α×List α))
    (h : ∀ x∈l,p x.1=true ∧ ∀ a∈x.2,p a=false) :
    split p (join l)=([],l) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨hx,hu⟩ := h x (List.mem_cons_self)
    have hh := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [join,List.flatMap_cons,List.cons_append,split,hx,ite_true]
    rw [split_unmarked_append p hu]
    change ([],(x.1,x.2++(split p (join l)).1)::(split p (join l)).2)=([],x::l)
    simp [hh]

lemma join_injective_on (p : α→Bool) {l r : List (α×List α)}
    (hl : ∀ x∈l,p x.1=true ∧ ∀ a∈x.2,p a=false)
    (hr : ∀ x∈r,p x.1=true ∧ ∀ a∈x.2,p a=false)
    (he : join l=join r) : l=r := by
  have h := congrArg (fun w => (split p w).2) he
  simpa only [split_join p l hl,split_join p r hr] using h

lemma join_first_marked (p : α→Bool) (l : List (α×List α))
    (h : ∀ x∈l,p x.1=true) :
    join l=[] ∨ ∃ a v,join l=a::v ∧ p a=true := by
  cases l with
  | nil => exact Or.inl rfl
  | cons x l =>
    exact Or.inr ⟨x.1,x.2++join l,rfl,h x (List.mem_cons_self)⟩

/-- Every extracted corner is an actual consecutive interval, bounded on
its right by the next marked letter (or the end of the word). -/
lemma located (p : α→Bool) (w : List α) (x : α×List α) (hx : x∈(split p w).2) :
    ∃ u v,w=u++x.1::(x.2++v) ∧
      (v=[] ∨ ∃ b t,v=b::t ∧ p b=true) := by
  induction w with
  | nil => simp [split] at hx
  | cons a w ih =>
    cases hp : p a with
    | false =>
      simp only [split,hp,Bool.false_eq_true,ite_false] at hx
      obtain ⟨u,v,hw,hv⟩ := ih hx
      exact ⟨a::u,v,by simp only [hw,List.cons_append],hv⟩
    | true =>
      simp only [split,hp,ite_true,List.mem_cons] at hx
      rcases hx with rfl|hx
      · refine ⟨[],join (split p w).2,?_,?_⟩
        · simpa only [List.nil_append] using congrArg (a::·) (reassemble p w).symm
        · exact join_first_marked p _ (fun y hy => (marked_corners p w y hy).1)
      · obtain ⟨u,v,hw,hv⟩ := ih hx
        exact ⟨a::u,v,by simp only [hw,List.cons_append],hv⟩



end FKCRT.CornerSplit
end


noncomputable section
open List
namespace FKCRT.MapCycles
variable {α : Type*}

/-- Empty corner scans preserve the pre-existing stack while contributing
exactly their own pairs. Thus insertion creates no cross-corner matching. -/
theorem scanArches_corners (f : α→Option Bool) (l : List (α×List α))
    (G : α×List α→List (α×α))
    (hg : ∀ x∈l,∀ S,scanArches f x.2 S=some (S,G x))
    {S T : List α} {E : List (α×α)}
    (h : scanArches f (l.map Prod.fst) S=some (T,E)) :
    ∃ F,scanArches f (CornerSplit.join l) S=some (T,F) ∧
      F.Perm (E++l.flatMap G) := by
  induction l generalizing S E with
  | nil =>
    simp only [List.map_nil,scanArches,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨[],rfl,.refl _⟩
  | cons x l ih =>
    have hcore : scanArches f ([x.1]++l.map Prod.fst) S=some (T,E) := h
    rw [scanArches_append] at hcore
    cases hs : scanArches f [x.1] S with
    | none => simp [hs] at hcore
    | some V =>
      cases ht : scanArches f (l.map Prod.fst) V.1 with
      | none => simp [hs,ht] at hcore
      | some W =>
        simp only [hs,Option.bind_some,ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hcore
        have hw : scanArches f (l.map Prod.fst) V.1=some (T,W.2) := by
          rw [ht,← hcore.1]
        obtain ⟨F,hF,hperm⟩ := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) hw
        refine ⟨V.2++G x++F,?_,?_⟩
        · change scanArches f ([x.1]++(x.2++CornerSplit.join l)) S=_
          simp only [scanArches_append,hs,Option.bind_some,hg x List.mem_cons_self,
            hF,Option.map_some]
          simp only [List.append_assoc]
        · rw [← hcore.2,List.flatMap_cons]
          simp only [List.append_assoc]
          apply ((hperm.append_left (G x)).append_left V.2).trans
          simpa only [List.append_assoc] using
            ((List.perm_append_comm (l₁:=G x) (l₂:=W.2)).append_right (l.flatMap G)).append_left V.2

/-- A standalone empty scan is unchanged by an arbitrary underlying stack. -/
lemma scanArches_suffix (f : α→Option Bool) {l S T : List α} {E : List (α×α)}
    (h : scanArches f l S=some (T,E)) (R : List α) :
    scanArches f l (S++R)=some (T++R,E) := by
  induction l generalizing S E with
  | nil =>
    simp only [scanArches,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    rfl
  | cons a l ih =>
    cases hf : f a with
    | none =>
      simp only [scanArches,hf] at h ⊢
      exact ih h
    | some b =>
      cases b with
      | true =>
        simp only [scanArches,hf] at h
        simpa only [scanArches,hf,List.cons_append] using ih h
      | false =>
        cases S with
        | nil => simp [scanArches,hf] at h
        | cons s S =>
          simp only [scanArches,hf] at h
          obtain ⟨p,hp,he⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨hT,hE⟩ := Prod.mk.inj he
          have hp' : scanArches f l S=some (T,p.2) := by
            rw [hp,← hT]
          have hh := ih hp'
          simp only [scanArches,hf,List.cons_append,hh,Option.map_some,hE]

end FKCRT.MapCycles

namespace FKCRT.Inventory
open MapCycles
variable {α : Type*}

/-- Matchings on an arbitrary ordered subword. The original positions are
retained, so this lemma can be applied inside a larger inventory word. -/
theorem ordered_matchings (w : α→TypedLetter) (l : List α)
    (hw : stackTypedRun (l.map w) []=some []) :
    ∃ E F : List (α×α),Arches l E ∧ Arches l F ∧
      (endpoints (E++F)).Perm l ∧
      (∀ e∈E,w e.1=.burger true ∧ w e.2=.order true) ∧
      (∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) := by
  let L (c : Bool) := l.filter (fun i => (w i).color == c)
  have hh (c : Bool) : (L c).map (fun i => (w i).step)=(identifiedDyck hw c).toList :=
    (colorWord_map w l c).symm
  obtain ⟨E,hE,hEp,hEf⟩ := dyck_arches (identifiedDyck hw true) (L true) _ (hh true)
  obtain ⟨F,hF,hFp,hFf⟩ := dyck_arches (identifiedDyck hw false) (L false) _ (hh false)
  have hp : (L true++L false).Perm l := by
    have hp := List.filter_append_perm (fun i => (w i).color) l
    simpa [L] using hp
  refine ⟨E,F,hE.mono (List.filter_sublist),hF.mono (List.filter_sublist),?_,?_,?_⟩
  · rw [endpoints_append]
    exact (hEp.append hFp).trans hp
  · intro e he
    have he' := hE.endpoints e he
    have h1 : (w e.1).color=true := by simpa [L] using (List.mem_filter.mp he'.1).2
    have h2 : (w e.2).color=true := by simpa [L] using (List.mem_filter.mp he'.2).2
    have hs := hEf e he
    constructor
    · cases hh : w e.1 <;> simp_all [TypedLetter.color,TypedLetter.step]
    · cases hh : w e.2 <;> simp_all [TypedLetter.color,TypedLetter.step]
  · intro e he
    have he' := hF.endpoints e he
    have h1 : (w e.1).color=false := by simpa [L] using (List.mem_filter.mp he'.1).2
    have h2 : (w e.2).color=false := by simpa [L] using (List.mem_filter.mp he'.2).2
    have hs := hFf e he
    constructor
    · cases hh : w e.1 <;> simp_all [TypedLetter.color,TypedLetter.step]
    · cases hh : w e.2 <;> simp_all [TypedLetter.color,TypedLetter.step]


/-- An actually empty typed subword has a deterministic one-colour
matching which is unchanged by any underlying stack. -/
theorem empty_typed_scan (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (hw : stackTypedRun (l.map w) []=some []) (c : Bool) :
    ∃ E, (∀ S,scanArches (fun x => colorInstruction c (w x)) l S=some (S,E)) ∧
      (endpoints E).Perm (l.filter (fun x => (w x).color == c)) := by
  obtain ⟨E,F,hE,hF,hc,htE,htF⟩ := ordered_matchings w l hw
  have hcov := matching_color_coverage w l E F hc htE htF
  have hscan : ∃ G,scanArches (fun x => colorInstruction c (w x)) l []=some ([],G) := by
    cases c with
    | true =>
      obtain ⟨G,hG,_⟩ := hE.scan hn (fun x => colorInstruction true (w x))
        (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hcov.1 []
      exact ⟨G,hG⟩
    | false =>
      obtain ⟨G,hG,_⟩ := hF.scan hn (fun x => colorInstruction false (w x))
        (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hcov.2 []
      exact ⟨G,hG⟩
  obtain ⟨G,hG⟩ := hscan
  refine ⟨G,(fun S => by simpa using scanArches_suffix _ hG S),?_⟩
  have hcG : (endpoints G).Nodup := by
    cases c with
    | true =>
      obtain ⟨H,hH,hHE⟩ := hE.scan hn (fun x => colorInstruction true (w x))
        (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hcov.1 []
      have he : G=H := congrArg Prod.snd (Option.some.inj (hG.symm.trans hH))
      rw [he]
      exact (endpoints_perm hHE).nodup_iff.mpr (by
        have hh := hc.nodup_iff.mpr hn
        rw [endpoints_append] at hh
        exact hh.of_append_left)
    | false =>
      obtain ⟨H,hH,hHF⟩ := hF.scan hn (fun x => colorInstruction false (w x))
        (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hcov.2 []
      have he : G=H := congrArg Prod.snd (Option.some.inj (hG.symm.trans hH))
      rw [he]
      exact (endpoints_perm hHF).nodup_iff.mpr (by
        have hh := hc.nodup_iff.mpr hn
        rw [endpoints_append] at hh
        exact hh.of_append_right)
  apply List.perm_ext_iff_of_nodup hcG (hn.filter _)|>.mpr
  intro x
  cases c with
  | true =>
    obtain ⟨H,hH,hHE⟩ := hE.scan hn (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hcov.1 []
    have he : G=H := congrArg Prod.snd (Option.some.inj (hG.symm.trans hH))
    rw [he,(endpoints_perm hHE).mem_iff]
    constructor
    · intro hx
      obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
      · simp [List.mem_filter,(hE.endpoints e he).1,(htE e he).1,TypedLetter.color]
      · simp [List.mem_filter,(hE.endpoints e he).2,(htE e he).2,TypedLetter.color]
    · intro hx
      obtain ⟨hx,hcol⟩ := List.mem_filter.mp hx
      apply hcov.1 x hx
      cases h : w x <;> simpa [h,TypedLetter.color,colorInstruction] using hcol
  | false =>
    obtain ⟨H,hH,hHF⟩ := hF.scan hn (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hcov.2 []
    have he : G=H := congrArg Prod.snd (Option.some.inj (hG.symm.trans hH))
    rw [he,(endpoints_perm hHF).mem_iff]
    constructor
    · intro hx
      obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
      · simp [List.mem_filter,(hF.endpoints e he).1,(htF e he).1,TypedLetter.color]
      · simp [List.mem_filter,(hF.endpoints e he).2,(htF e he).2,TypedLetter.color]
    · intro hx
      obtain ⟨hx,hcol⟩ := List.mem_filter.mp hx
      apply hcov.2 x hx
      cases h : w x <;> simpa [h,TypedLetter.color,colorInstruction] using hcol

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*}

/-- Exact locality of the actual stack matching on an empty interval. -/
lemma scanArches_interval_subset (f : α→Option Bool) (u v z S T : List α)
    {E G : List (α×α)} (h : scanArches f (u++(v++z)) S=some (T,E))
    (hv : scanArches f v []=some ([],G)) : ∀ e∈G,e∈E := by
  rw [scanArches_append] at h
  cases hu : scanArches f u S with
  | none => simp [hu] at h
  | some U =>
    have hv' : scanArches f v U.1=some (U.1,G) := by simpa using scanArches_suffix f hv U.1
    simp only [hu,Option.bind_some,scanArches_append,hv'] at h
    cases hz : scanArches f z U.1 with
    | none => simp [hz] at h
    | some Z =>
      simp only [hz,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      intro e he
      rw [← h.2]
      exact List.mem_append_right _ (List.mem_append_left _ he)

end FKCRT.MapCycles
namespace FKCRT.Inventory
open MapCycles
variable {α : Type*} [DecidableEq α]

/-- Any actual successful consecutive subword is closed under the *full*
word's matching. In particular successful corner inserts do not rematch an
old endpoint to a new one. -/
theorem empty_interval_matching_closed (w : α→TypedLetter) (u v z : List α)
    (hn : (u++(v++z)).Nodup) (E F : List (α×α))
    (hE : Arches (u++(v++z)) E) (hF : Arches (u++(v++z)) F)
    (hcov : (endpoints (E++F)).Perm (u++(v++z)))
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (hv : stackTypedRun (v.map w) []=some []) :
    ∀ d∈v,turns (E++F) d∈v := by
  obtain ⟨E',F',hE',hF',hc',htE',htF'⟩ := ordered_matchings w v hv
  have hfullcov := matching_color_coverage w (u++(v++z)) E F hcov htE htF
  have hlocalcov := matching_color_coverage w v E' F' hc' htE' htF'
  have hnv : v.Nodup := hn.of_append_right.of_append_left
  have hsubE : ∀ e∈E',e∈E := by
    obtain ⟨G,hG,hGE⟩ := hE.scan hn (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hfullcov.1 []
    obtain ⟨G',hG',hGE'⟩ := hE'.scan hnv (fun x => colorInstruction true (w x))
      (fun e he => by simp [colorInstruction,(htE' e he).1,(htE' e he).2]) hlocalcov.1 []
    intro e he
    exact hGE.mem_iff.mp (scanArches_interval_subset _ u v z [] [] hG hG' e (hGE'.mem_iff.mpr he))
  have hsubF : ∀ e∈F',e∈F := by
    obtain ⟨G,hG,hGF⟩ := hF.scan hn (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hfullcov.2 []
    obtain ⟨G',hG',hGF'⟩ := hF'.scan hnv (fun x => colorInstruction false (w x))
      (fun e he => by simp [colorInstruction,(htF' e he).1,(htF' e he).2]) hlocalcov.2 []
    intro e he
    exact hGF.mem_iff.mp (scanArches_interval_subset _ u v z [] [] hG hG' e (hGF'.mem_iff.mpr he))
  have hnE : (endpoints (E++F)).Nodup := hcov.nodup_iff.mpr hn
  intro d hd
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp (hc'.mem_iff.mpr hd)
  · rcases List.mem_append.mp he with he|he
    · rw [(turns_pair hnE e (List.mem_append_left _ (hsubE e he))).1]
      exact (hE'.endpoints e he).2
    · rw [(turns_pair hnE e (List.mem_append_right _ (hsubF e he))).1]
      exact (hF'.endpoints e he).2
  · rcases List.mem_append.mp he with he|he
    · rw [(turns_pair hnE e (List.mem_append_left _ (hsubE e he))).2]
      exact (hE'.endpoints e he).1
    · rw [(turns_pair hnE e (List.mem_append_right _ (hsubF e he))).2]
      exact (hF'.endpoints e he).1

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT.Chords
variable {N : ℕ}

lemma gapIndex_strict (a : Perm (Fin N)) (r : Opener a)
    {i j c : Fin N} (hc : c∈componentDarts a r) (hic : i≤c) (hcj : c<j) :
    gapIndex a r i<gapIndex a r j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro d hd
    obtain ⟨hd,hdi⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hd,(hdi.trans_le hic).trans hcj⟩
  · intro h
    have hmem : c∈(componentDarts a r).filter (·<j) := Finset.mem_filter.mpr ⟨hc,hcj⟩
    rw [← h] at hmem
    exact not_lt_of_ge hic (Finset.mem_filter.mp hmem).2

def rootSplit (a : Perm (Fin N)) (r : Opener a) : List (Fin N×List (Fin N)) :=
  (CornerSplit.split (fun d => decide (d∈componentDarts a r)) (List.finRange N)).2

lemma rootSplit_prefix (a : Perm (Fin N)) (r : Opener a) (hr : r.val.val=0) :
    (CornerSplit.split (fun d => decide (d∈componentDarts a r)) (List.finRange N)).1=[] := by
  cases N with
  | zero => exact Fin.elim0 r.val
  | succ N =>
    rw [List.finRange_succ]
    apply CornerSplit.prefix_nil
    apply decide_eq_true
    have hr0 : r.val=0 := Fin.ext hr
    exact (mem_componentDarts a r 0).mpr ⟨r,SimpleGraph.Reachable.refl r,Or.inl hr0.symm⟩

lemma rootSplit_join (a : Perm (Fin N)) (r : Opener a) (hr : r.val.val=0) :
    CornerSplit.join (rootSplit a r)=List.finRange N := by
  have h := CornerSplit.reassemble (fun d => decide (d∈componentDarts a r)) (List.finRange N)
  simpa only [rootSplit_prefix a r hr,List.nil_append,rootSplit] using h

/-- The literal interval chunks extracted from a root crossing component
are closed under the actual edge pairing. No fresh independent matching
is substituted at the corners. -/
theorem rootSplit_closed (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (r : Opener a) (hr : r.val.val=0)
    (x : Fin N×List (Fin N)) (hx : x∈rootSplit a r) :
    ∀ d∈x.2,a d∈x.2 := by
  let p := fun d => decide (d∈componentDarts a r)
  have hx' : x∈(CornerSplit.split p (List.finRange N)).2 := hx
  obtain ⟨hmark,hunmark⟩ := CornerSplit.marked_corners p (List.finRange N) x hx'
  obtain ⟨u,v,he,hv⟩ := CornerSplit.located p (List.finRange N) x hx'
  have hcm : x.1∈componentDarts a r := of_decide_eq_true hmark
  have hs : (u++x.1::(x.2++v)).Pairwise (·<·) := he ▸ List.pairwise_lt_finRange N
  obtain ⟨_,hrest,hleft⟩ := List.pairwise_append.mp hs
  obtain ⟨hfirst,htail⟩ := List.pairwise_cons.mp hrest
  obtain ⟨_,_,hright⟩ := List.pairwise_append.mp htail
  intro d hd
  have hdn : d∉componentDarts a r := of_decide_eq_false (hunmark d hd)
  have han : a d∉componentDarts a r := fun h => hdn ((componentDarts_mate a ha r d).mp h)
  have hgap := gapIndex_mate a ha hf r hr d hdn
  have hm : a d∈u++x.1::(x.2++v) := by rw [← he]; exact List.mem_finRange _
  rcases List.mem_append.mp hm with hu|hm
  · have hlt := hleft (a d) hu x.1 (List.mem_cons_self)
    have hlt' := hfirst d (List.mem_append_left _ hd)
    have hh := gapIndex_strict a r hcm hlt.le hlt'
    omega
  · rcases List.mem_cons.mp hm with h|hm
    · exact False.elim (han (h ▸ hcm))
    · rcases List.mem_append.mp hm with hm|hh
      · exact hm
      · rcases hv with rfl|⟨b,t,rfl,hb⟩
        · simp at hh
        · have hbm : b∈componentDarts a r := of_decide_eq_true hb
          have hdb : d<b := hright d hd b (List.mem_cons_self)
          rcases List.mem_cons.mp hh with hab|hab
          · exact False.elim (han (hab ▸ hbm))
          · have hbt : b<a d := (List.pairwise_cons.mp (List.pairwise_append.mp htail).2.1).1 _ hab
            have hg := gapIndex_strict a r hbm hdb.le hbt
            omega

lemma rootSplit_length_lt (a : Perm (Fin N)) (r : Opener a)
    (x : Fin N×List (Fin N)) (hx : x∈rootSplit a r) : x.2.length<N := by
  obtain ⟨u,v,he,_⟩ := CornerSplit.located (fun d => decide (d∈componentDarts a r))
    (List.finRange N) x hx
  have h := congrArg List.length he
  simp only [List.length_finRange,List.length_append,List.length_cons] at h
  omega

end FKCRT.Chords

namespace FKCRT.Inventory
open Chords
variable {N : ℕ}

lemma cornerInsert_map {α : Type*} (f : α→TypedLetter) (l : List (α×List α)) :
    cornerInsert (l.map (fun x => (f x.1,x.2.map f)))=(CornerSplit.join l).map f := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [cornerInsert,CornerSplit.join] using congrArg (fun z => f x.1::(x.2.map f++z)) ih

/-- The exact forward rooted-corner decomposition of a genuine matching
word, including successful empty corners and multiplicative activity weight. -/
theorem root_component_decomposition (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (c : Fin N→Bool) (hc : ∀ d,c (a d)=c d)
    (hn : ∀ x y,c x=c y → x<y → y<a x → a x<a y → False)
    (r : Opener a) (hr : r.val.val=0) :
    let l := (rootSplit a r).map (fun x => (pairWord a c x.1,x.2.map (pairWord a c)))
    cornerInsert l=(List.finRange N).map (pairWord a c) ∧
    stackTypedRun (l.map Prod.fst) []=some [] ∧
    (∀ x∈l,stackTypedRun x.2 []=some []) ∧
    flexibleCount ((List.finRange N).map (pairWord a c)) []=
      flexibleCount (l.map Prod.fst) []+(l.map (fun x => flexibleCount x.2 [])).sum := by
  dsimp only
  let l := (rootSplit a r).map (fun x => (pairWord a c x.1,x.2.map (pairWord a c)))
  have hjoin : cornerInsert l=(List.finRange N).map (pairWord a c) := by
    rw [cornerInsert_map,rootSplit_join a r hr]
  have hskeleton : l.map Prod.fst=
      ((List.finRange N).filter (fun d => decide (d∈componentDarts a r))).map (pairWord a c) := by
    change ((rootSplit a r).map _).map _=_
    rw [List.map_map]
    have h := congrArg (List.map (pairWord a c))
      (CornerSplit.skeleton (fun d => decide (d∈componentDarts a r)) (List.finRange N))
    simpa only [List.map_map,Function.comp_def,rootSplit] using h
  have hske : stackTypedRun (l.map Prod.fst) []=some [] := by
    rw [hskeleton]
    exact (component_and_corners_empty a ha hf c hc hn r hr).1
  have hchunks : ∀ x∈l,stackTypedRun x.2 []=some [] := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    apply typedRun_closed_subword a ha hf c hc hn y.2
    · obtain ⟨u,v,he,_⟩ := CornerSplit.located (fun d => decide (d∈componentDarts a r))
        (List.finRange N) y hy
      have hs : (u++y.1::(y.2++v)).Pairwise (·<·) := he ▸ List.pairwise_lt_finRange N
      exact ((List.pairwise_append.mp (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2).1)
    · exact rootSplit_closed a ha hf r hr y hy
  refine ⟨hjoin,hske,hchunks,?_⟩
  rw [← hjoin]
  exact (cornerInsert_run_count l hchunks hske).2

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Chords
variable {N : ℕ}

/-- Consecutive chunks are order-convex in the actual dart tour. -/
lemma chunk_convex (p : Fin N→Bool) (x : Fin N×List (Fin N))
    (hx : x∈(CornerSplit.split p (List.finRange N)).2)
    {i j k : Fin N} (hi : i∈x.2) (hj : j∈x.2) (hik : i≤k) (hkj : k≤j) : k∈x.2 := by
  obtain ⟨u,v,he,_⟩ := CornerSplit.located p (List.finRange N) x hx
  have hs : (u++x.1::(x.2++v)).Pairwise (·<·) := he ▸ List.pairwise_lt_finRange N
  obtain ⟨_,hs',hleft⟩ := List.pairwise_append.mp hs
  obtain ⟨hfirst,hs''⟩ := List.pairwise_cons.mp hs'
  obtain ⟨_,_,hright⟩ := List.pairwise_append.mp hs''
  have hk : k∈u++x.1::(x.2++v) := by rw [← he]; exact List.mem_finRange _
  rcases List.mem_append.mp hk with hk|hk
  · have hlt := hleft k hk i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
    exact False.elim ((not_lt_of_ge hik) hlt)
  · rcases List.mem_cons.mp hk with rfl|hk
    · exact False.elim ((not_lt_of_ge hik) (hfirst i (List.mem_append_left _ hi)))
    · rcases List.mem_append.mp hk with hk|hk
      · exact hk
      · exact False.elim ((not_lt_of_ge hkj) (hright j hj k hk))

lemma unmarked_in_chunk (p : Fin N→Bool) (hN : 0<N) (hp : p ⟨0,hN⟩=true)
    {d : Fin N} (hd : p d=false) :
    ∃ x∈(CornerSplit.split p (List.finRange N)).2,d∈x.2 := by
  have hpref : (CornerSplit.split p (List.finRange N)).1=[] := by
    cases N with
    | zero => omega
    | succ N => rw [List.finRange_succ]; exact CornerSplit.prefix_nil p hp
  have he := CornerSplit.reassemble p (List.finRange N)
  rw [hpref,List.nil_append] at he
  have hm : d∈CornerSplit.join (CornerSplit.split p (List.finRange N)).2 := by
    rw [he]; exact List.mem_finRange _
  obtain ⟨x,hx,hdx⟩ := List.mem_flatMap.mp hm
  refine ⟨x,hx,?_⟩
  rcases List.mem_cons.mp hdx with rfl|hdx
  · have ht := (CornerSplit.marked_corners p (List.finRange N) x hx).1
    simp [ht] at hd
  · exact hdx

/-- Matching edges in distinct empty corners cannot cross a core edge. -/
theorem no_cross_core_corner (a : Perm (Fin N)) (p : Fin N→Bool)
    (hcore : ∀ d,p (a d)=p d)
    (hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2)
    (hp : ∀ d : Fin N,d.val=0 → p d=true)
    (x y : Opener a) (hx : p x.val=true) (hy : p y.val=false) : ¬Cross a x y := by
  have hN : 0<N := y.val.pos
  obtain ⟨z,hz,hyz⟩ := unmarked_in_chunk p hN (hp ⟨0,hN⟩ rfl) hy
  have hayz := hchunks z hz y.val hyz
  have hn := (CornerSplit.marked_corners p (List.finRange N) z hz).2
  intro hc
  rcases hc with h|h
  · have hm := chunk_convex p z hz hyz hayz h.2.1.le h.2.2.le
    have hf := hn (a x.val) hm
    rw [hcore,hx] at hf
    cases hf
  · have hm := chunk_convex p z hz hyz hayz h.1.le h.2.1.le
    have hf := hn x.val hm
    rw [hx] at hf
    cases hf

/-- Insertion cannot enlarge a connected root core. Reachability here is
inside the finite crossing graph, not a probabilistic limiting assertion. -/
theorem root_component_of_core (a : Perm (Fin N)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) (p : Fin N→Bool) (r : Opener a) (hr : r.val.val=0)
    (hp : p r.val=true) (hcore : ∀ d,p (a d)=p d)
    (hchunks : ∀ x∈(CornerSplit.split p (List.finRange N)).2,∀ d∈x.2,a d∈x.2)
    (hconnected : ∀ x : Opener a,p x.val=true → (graph a).Reachable r x) :
    componentDarts a r=Finset.univ.filter (fun d => p d=true) := by
  have hp0 : ∀ d : Fin N,d.val=0 → p d=true := by
    intro d hd
    have he : d=r.val := Fin.ext (hd.trans hr.symm)
    simpa only [he] using hp
  have hreach : ∀ x : Opener a,(graph a).Reachable r x → p x.val=true := by
    intro x hx
    have h := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hx
    induction h with
    | refl => exact hp
    | @tail y z hpath hadj ih =>
      have hy : (graph a).Reachable r y := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hpath
      cases hh : p z.val with
      | true => rfl
      | false => exact False.elim (no_cross_core_corner a p hcore hchunks hp0 y z (ih hy) hh hadj)
  ext d
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_componentDarts]
  constructor
  · rintro ⟨x,hx,rfl|rfl⟩
    · exact hreach x hx
    · rw [hcore]; exact hreach x hx
  · intro hd
    let x := opener a ha hf d
    have hends := opener_endpoints a ha hf d
    have hx : p x.val=true := by
      rcases hends with h|h
      · exact (congrArg p h.symm).trans hd
      · exact (hcore x.val).symm.trans ((congrArg p h.symm).trans hd)
    exact ⟨x,hconnected x hx,hends⟩

end FKCRT.Chords
end

end OAI
