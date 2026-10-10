import OAI.Probability.FKMaps.MapEncoding
import OAI.Probability.FKMaps.WordLaw

namespace OAI

noncomputable section
open List
namespace FKCRT.Inventory
open MapCycles

def TypedLetter.color : TypedLetter → Bool
  | .burger c => c
  | .order c => c

def TypedLetter.step : TypedLetter → DyckStep
  | .burger _ => .U
  | .order _ => .D

lemma colorWord_map {α : Type*} (f : α→TypedLetter) (l : List α) (c : Bool) :
    colorWord c (l.map f) = (l.filter (fun i => (f i).color == c)).map (fun i => (f i).step) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hf : f a with
    | burger b => by_cases hb : b=c <;> simp_all [colorWord,colorStep,TypedLetter.color,TypedLetter.step]
    | order b => by_cases hb : b=c <;> simp_all [colorWord,colorStep,TypedLetter.color,TypedLetter.step]

/-- Actual identified words produce a complete pair of noncrossing matchings;
the labels on each pair are the matching burger and fixed order. -/
theorem identified_matchings {n : ℕ} (w : Dart n→TypedLetter)
    (hw : stackTypedRun ((List.finRange (2*(n+1))).map w) []=some []) :
    ∃ E F : List (Dart n × Dart n),
      Arches (List.finRange (2*(n+1))) E ∧
      Arches (List.finRange (2*(n+1))) F ∧
      (endpoints (E++F)).Perm (List.finRange (2*(n+1))) ∧
      (∀ e∈E,w e.1=.burger true ∧ w e.2=.order true) ∧
      (∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) := by
  let l := List.finRange (2*(n+1))
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

/-- The finite inverse in words.tex is defined on every nonempty identified
word, and lands in the exact genus-zero maps rather than an auxiliary class. -/
theorem identified_map_exists {n : ℕ} (w : Dart n→TypedLetter)
    (hw : stackTypedRun ((List.finRange (2*(n+1))).map w) []=some []) :
    ∃ E F : List (Dart n × Dart n),
      MapConditions (turns (E++F),(List.finRange (2*(n+1))).formPerm * turns E) ∧
      (∀ e∈E,w e.1=.burger true ∧ w e.2=.order true) ∧
      (∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) := by
  obtain ⟨E,F,hE,hF,hc,h1,h2⟩ := identified_matchings w hw
  exact ⟨E,F,matching_map_conditions E F hE hF hc,h1,h2⟩

end FKCRT.Inventory
end


noncomputable section
open List
namespace FKCRT.MapCycles
variable {α : Type*} 

/-- Deterministic stack matching of one colour; `none` skips the other colour. -/
def scanArches (f : α→Option Bool) : List α → List α → Option (List α × List (α×α))
  | [],S => some (S,[])
  | a::l,S => match f a with
      | none => scanArches f l S
      | some true => scanArches f l (a::S)
      | some false => match S with
        | [] => none
        | b::S => (scanArches f l S).map (fun z => (z.1,(b,a)::z.2))

lemma scanArches_append (f : α→Option Bool) (l r S : List α) :
    scanArches f (l++r) S=(scanArches f l S).bind (fun z =>
      (scanArches f r z.1).map (fun w => (w.1,z.2++w.2))) := by
  induction l generalizing S with
  | nil => simp [scanArches]
  | cons a l ih =>
    cases hf : f a with
    | none => simpa [scanArches,hf] using ih S
    | some b =>
      cases b with
      | true => simpa [scanArches,hf] using ih (a::S)
      | false =>
        cases S with
        | nil => simp [scanArches,hf]
        | cons b S =>
          simp only [List.cons_append,scanArches,hf,ih]
          cases h1 : scanArches f l S with
          | none => rfl
          | some z => cases h2 : scanArches f r z.1 <;> simp [h2]

lemma Arches.mem_endpoints {l : List α} {E : List (α×α)} (h : Arches l E)
    {x : α} (hx : x∈MapCycles.endpoints E) : x∈l := by
  obtain ⟨e,he,hx⟩ := MapCycles.mem_endpoints.mp hx
  rcases hx with rfl|rfl
  · exact (h.endpoints e he).1
  · exact (h.endpoints e he).2

/-- Noncrossing typed pairings are uniquely recovered by the stack. In
particular no hidden choice of an arch pairing enters the map inverse. -/
theorem Arches.scan {l : List α} {E : List (α×α)} (h : Arches l E)
    (hn : l.Nodup) (f : α→Option Bool)
    (hp : ∀ e∈E,f e.1=some true ∧ f e.2=some false)
    (hc : ∀ x∈l,f x≠none → x∈MapCycles.endpoints E) (S : List α) :
    ∃ F,scanArches f l S=some (S,F) ∧ F.Perm E := by
  induction h generalizing S with
  | nil => exact ⟨[],rfl,.refl _⟩
  | @skip a l E h ih =>
    have ha : f a=none := by
      by_contra ha
      exact hn.notMem (h.mem_endpoints (hc a (by simp) ha))
    obtain ⟨F,hF,hFE⟩ := ih hn.of_cons (fun e he => hp e he)
      (fun x hx ht => hc x (List.mem_cons_of_mem _ hx) ht) S
    exact ⟨F,by simpa [scanArches,ha] using hF,hFE⟩
  | @pair a b L R E G hL hR ihL ihR =>
    have hab := hp (a,b) (by simp)
    have hLsub : ∀ x∈L,f x≠none → x∈MapCycles.endpoints E := by
      intro x hx hfx
      have hh := hc x (by simp [hx]) hfx
      simp only [endpoints_cons,endpoints_append,List.mem_cons,List.mem_append] at hh
      rcases hh with rfl|rfl|he|hg
      · exact False.elim (hn.notMem (by simp [hx]))
      · have hb : x∉L := by
          have hh := (List.nodup_append.mp hn.of_cons).2.2
          exact fun h => hh x h x (by simp) rfl
        exact False.elim (hb hx)
      · exact he
      · have hxR := hR.mem_endpoints hg
        have hh := (List.nodup_append.mp hn.of_cons).2.2
        exact False.elim (hh x hx x (by simp [hxR]) rfl)
    have hRsub : ∀ x∈R,f x≠none → x∈MapCycles.endpoints G := by
      intro x hx hfx
      have hh := hc x (by simp [hx]) hfx
      simp only [endpoints_cons,endpoints_append,List.mem_cons,List.mem_append] at hh
      rcases hh with rfl|rfl|he|hg
      · exact False.elim (hn.notMem (by simp [hx]))
      · exact False.elim (hn.of_cons.of_append_right.notMem hx)
      · have hxL := hL.mem_endpoints he
        have hh := (List.nodup_append.mp hn.of_cons).2.2
        exact False.elim (hh x hxL x (by simp [hx]) rfl)
      · exact hg
    obtain ⟨F,hF,hFE⟩ := ihL hn.of_cons.of_append_left (fun e he => hp e (by simp [he])) hLsub (a::S)
    obtain ⟨H,hH,hHG⟩ := ihR hn.of_cons.of_append_right.of_cons (fun e he => hp e (by simp [he])) hRsub S
    refine ⟨F++(a,b)::H,?_,?_⟩
    · simp only [scanArches,hab.1,scanArches_append,hF,Option.bind_some,hab.2,hH,Option.map_some]
    · exact (List.perm_middle).trans ((hFE.append hHG).cons (a,b))

/-- Uniqueness is literal up to the irrelevant order of disjoint pairs. -/
theorem arches_unique {l : List α} {E F : List (α×α)}
    (hE : Arches l E) (hF : Arches l F) (hn : l.Nodup) (f : α→Option Bool)
    (hpE : ∀ e∈E,f e.1=some true ∧ f e.2=some false)
    (hpF : ∀ e∈F,f e.1=some true ∧ f e.2=some false)
    (hcE : ∀ x∈l,f x≠none → x∈MapCycles.endpoints E)
    (hcF : ∀ x∈l,f x≠none → x∈MapCycles.endpoints F) : E.Perm F := by
  obtain ⟨G,hG,hGE⟩ := hE.scan hn f hpE hcE []
  obtain ⟨H,hH,hHF⟩ := hF.scan hn f hpF hcF []
  have he : G=H := by simpa only [hG,Option.some.injEq,Prod.mk.injEq,true_and] using hH
  exact hGE.symm.trans (he.symm ▸ hHF)

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*}

lemma endpoints_perm {E F : List (α×α)} (h : E.Perm F) :
    (endpoints E).Perm (endpoints F) := h.flatMap (fun _ _ => List.Perm.refl _)

variable [DecidableEq α]

lemma turns_perm {E F : List (α×α)} (h : E.Perm F) (hn : (endpoints E).Nodup) :
    turns E=turns F := by
  have hnF := h |> endpoints_perm |>.nodup_iff.mp hn
  apply Equiv.ext
  intro x
  by_cases hx : x∈endpoints E
  · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
    · exact (turns_pair hn e he).1.trans (turns_pair hnF e (h.mem_iff.mp he)).1.symm
    · exact (turns_pair hn e he).2.trans (turns_pair hnF e (h.mem_iff.mp he)).2.symm
  · rw [turns_fixed_of_notMem hx,turns_fixed_of_notMem (fun hh => hx ((endpoints_perm h).mem_iff.mpr hh))]

end MapCycles
namespace Inventory
open MapCycles
variable {α : Type*}

/-- The one-colour stack instruction attached to a typed inventory symbol. -/
def colorInstruction (c : Bool) : TypedLetter→Option Bool
  | .burger b => if b=c then some true else none
  | .order b => if b=c then some false else none

lemma matching_color_coverage (w : α→TypedLetter) (l : List α)
    (E F : List (α×α)) (hc : (endpoints (E++F)).Perm l)
    (hE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (hF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) :
    (∀ x∈l,colorInstruction true (w x)≠none → x∈endpoints E) ∧
    (∀ x∈l,colorInstruction false (w x)≠none → x∈endpoints F) := by
  constructor
  · intro x hx hw
    have hh := hc.mem_iff.mpr hx
    rw [endpoints_append,List.mem_append] at hh
    rcases hh with hh|hh
    · exact hh
    · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hh
      · exact False.elim (hw (by simp [colorInstruction,(hF e he).1]))
      · exact False.elim (hw (by simp [colorInstruction,(hF e he).2]))
  · intro x hx hw
    have hh := hc.mem_iff.mpr hx
    rw [endpoints_append,List.mem_append] at hh
    rcases hh with hh|hh
    · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hh
      · exact False.elim (hw (by simp [colorInstruction,(hE e he).1]))
      · exact False.elim (hw (by simp [colorInstruction,(hE e he).2]))
    · exact hh

/-- Literal uniqueness of the inverse map's two matchings, including empty
colour classes. This removes all pairing choices in `identified_map_exists`. -/
theorem typed_matchings_unique (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (E F E' F' : List (α×α))
    (hE : Arches l E) (hF : Arches l F) (hE' : Arches l E') (hF' : Arches l F')
    (hc : (endpoints (E++F)).Perm l) (hc' : (endpoints (E'++F')).Perm l)
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (htE' : ∀ e∈E',w e.1=.burger true ∧ w e.2=.order true)
    (htF' : ∀ e∈F',w e.1=.burger false ∧ w e.2=.order false) :
    E.Perm E' ∧ F.Perm F' := by
  have hcov := matching_color_coverage w l E F hc htE htF
  have hcov' := matching_color_coverage w l E' F' hc' htE' htF'
  constructor
  · apply arches_unique hE hE' hn (colorInstruction true ∘ w)
    · intro e he
      simp [colorInstruction,(htE e he).1,(htE e he).2]
    · intro e he
      simp [colorInstruction,(htE' e he).1,(htE' e he).2]
    · exact hcov.1
    · exact hcov'.1
  · apply arches_unique hF hF' hn (colorInstruction false ∘ w)
    · intro e he
      simp [colorInstruction,(htF e he).1,(htF e he).2]
    · intro e he
      simp [colorInstruction,(htF' e he).1,(htF' e he).2]
    · exact hcov.2
    · exact hcov'.2

variable [DecidableEq α]

/-- In particular the reconstructed edge and vertex permutations are
independent of the proof/choice of Dyck pairing. -/
theorem typed_map_unique (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (E F E' F' : List (α×α))
    (hE : Arches l E) (hF : Arches l F) (hE' : Arches l E') (hF' : Arches l F')
    (hc : (endpoints (E++F)).Perm l) (hc' : (endpoints (E'++F')).Perm l)
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false)
    (htE' : ∀ e∈E',w e.1=.burger true ∧ w e.2=.order true)
    (htF' : ∀ e∈F',w e.1=.burger false ∧ w e.2=.order false) :
    turns (E++F)=turns (E'++F') ∧ l.formPerm*turns E=l.formPerm*turns E' := by
  obtain ⟨he,hf⟩ := typed_matchings_unique w l hn E F E' F' hE hF hE' hF' hc hc' htE htF htE' htF'
  have hnod : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr hn
  refine ⟨turns_perm (he.append hf) hnod,?_⟩
  rw [turns_perm he (by rw [endpoints_append] at hnod; exact hnod.of_append_left)]

end Inventory
end FKCRT
end


noncomputable section
open List
namespace FKCRT.MapCycles
variable {α : Type*} [LinearOrder α]

/-- A closed involutive noncrossing colour matching admits exactly the
recursive arch decomposition. No Jordan-curve principle is assumed. -/
theorem arches_of_noncrossing (a : α→α) (ha : Function.Involutive a)
    (P : α→Bool) (hP : ∀ x,P (a x)=P x) (l : List α)
    (hs : l.Pairwise (·<·))
    (hc : ∀ x∈l,P x=true → a x∈l)
    (hf : ∀ x∈l,P x=true → a x≠x)
    (hn : ∀ x∈l,∀ y∈l,P x=true → P y=true → x<y → y<a x → a x<a y → False) :
    ∃ E,Arches l E ∧ (endpoints E).Perm (l.filter P) ∧
      ∀ e∈E,e.2=a e.1 ∧ P e.1=true := by
  cases l with
  | nil => exact ⟨[],.nil,by simp,by simp⟩
  | cons x l =>
    have hs' := List.pairwise_cons.mp hs
    by_cases hx : P x=true
    · have hax : a x∈l := (List.mem_cons.mp (hc x (by simp) hx)).resolve_left (hf x (by simp) hx)
      obtain ⟨L,R,rfl⟩ := List.mem_iff_append.mp hax
      have hL := (List.pairwise_append.mp hs'.2).1
      have hbR := (List.pairwise_append.mp hs'.2).2.1
      have hR := (List.pairwise_cons.mp hbR).2
      have hLR := (List.pairwise_append.mp hs'.2).2.2
      have hxL (y) (hy : y∈L) : x<y := hs'.1 y (List.mem_append_left _ hy)
      have hxR (y) (hy : y∈R) : x<y := hs'.1 y (by simp [hy])
      have hxb : x<a x := hs'.1 (a x) (by simp)
      have hbR' (y) (hy : y∈R) : a x<y := (List.pairwise_cons.mp hbR).1 y hy
      have hLb (y) (hy : y∈L) : y<a x := hLR y hy (a x) (by simp)
      have hcL : ∀ y∈L,P y=true → a y∈L := by
        intro y hy hpy
        have hh := hc y (by simp [hy]) hpy
        simp only [List.mem_cons,List.mem_append] at hh
        rcases hh with h|h|h|h
        · have he : y=a x := (ha y).symm.trans (congrArg a h)
          exact False.elim ((ne_of_lt (hLb y hy)) he)
        · exact h
        · have he : y=x := ha.injective h
          exact False.elim ((ne_of_lt (hxL y hy)) he.symm)
        · exact False.elim (hn x (by simp) y (by simp [hy]) hx hpy
            (hxL y hy) (hLb y hy) (hbR' (a y) h))
      have hcR : ∀ y∈R,P y=true → a y∈R := by
        intro y hy hpy
        have hh := hc y (by simp [hy]) hpy
        simp only [List.mem_cons,List.mem_append] at hh
        rcases hh with h|h|h|h
        · have he : y=a x := (ha y).symm.trans (congrArg a h)
          exact False.elim ((ne_of_lt (hbR' y hy)) he.symm)
        · exact False.elim (hn x (by simp) (a y) (by simp [h]) hx (by rw [hP]; exact hpy)
            (hxL (a y) h) (hLb (a y) h) (by rw [ha]; exact hbR' y hy))
        · have he : y=x := ha.injective h
          exact False.elim ((ne_of_lt (hxR y hy)) he.symm)
        · exact h
      obtain ⟨E,hE,he,hpe⟩ := arches_of_noncrossing a ha P hP L hL hcL
        (fun y hy hpy => hf y (by simp [hy]) hpy)
        (fun y hy z hz => hn y (by simp [hy]) z (by simp [hz]))
      obtain ⟨F,hF,hf',hpf⟩ := arches_of_noncrossing a ha P hP R hR hcR
        (fun y hy hpy => hf y (by simp [hy]) hpy)
        (fun y hy z hz => hn y (by simp [hy]) z (by simp [hz]))
      refine ⟨(x,a x)::(E++F),.pair x (a x) hE hF,?_,?_⟩
      · simp only [endpoints_cons,endpoints_append,List.filter_cons,List.filter_append,hx,hP,
          ite_true]
        exact (((he.append hf').cons (a x)).cons x).trans (List.perm_middle.symm.cons x)
      · intro e he'
        simp only [List.mem_cons,List.mem_append] at he'
        rcases he' with rfl|h|h
        · exact ⟨rfl,hx⟩
        · exact hpe e h
        · exact hpf e h
    · have hc' : ∀ y∈l,P y=true → a y∈l := by
        intro y hy hpy
        apply (List.mem_cons.mp (hc y (by simp [hy]) hpy)).resolve_left
        intro he
        apply hx
        rw [← he,hP]
        exact hpy
      obtain ⟨E,hE,he,hpe⟩ := arches_of_noncrossing a ha P hP l hs'.2 hc'
        (fun y hy hpy => hf y (by simp [hy]) hpy)
        (fun y hy z hz => hn y (by simp [hy]) z (by simp [hz]))
      exact ⟨E,.skip x hE,by simpa [List.filter_cons,hx] using he,hpe⟩
termination_by l.length
decreasing_by
  all_goals
    subst_vars
    simp only [List.length_cons, List.length_append]
    omega

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT.MapCycles
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma orbitList_formPerm (x : α) (l : List α) (hn : (x::l).Nodup) :
    orbitList (x::l).formPerm x=x::l := by
  cases l with
  | nil => simp [orbitList]
  | cons y l =>
    have ht : (x::y::l).formPerm.toList x=x::y::l := by
      simpa using toList_formPerm_nontrivial (x::y::l) (by simp) hn
    have hp : (x::y::l).formPerm x≠x := by
      intro h
      have hh := toList_eq_nil_iff.mpr (notMem_support.mpr h)
      rw [ht] at hh
      cases hh
    simpa only [orbitList,ite_eq_right hp] using ht

end MapCycles
namespace MapCycles
variable {α : Type*} [LinearOrder α]

lemma ordered_four_sublist {l : List α} (hs : l.Pairwise (·<·))
    {x y z w : α} (hx : x∈l) (hy : y∈l) (hz : z∈l) (hw : w∈l)
    (hxy : x<y) (hyz : y<z) (hzw : z<w) : [x,y,z,w]<+l := by
  have hh : [x,y,z,w].Pairwise (·<·) := by simp; exact ⟨⟨hxy,hxy.trans hyz,(hxy.trans hyz).trans hzw⟩,⟨hyz,hyz.trans hzw⟩,hzw⟩
  apply List.sublist_of_subperm_of_pairwise (r := (·≤·))
  · apply List.subperm_of_subset (hh.imp (fun h => ne_of_lt h))
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> assumption
  · exact hh.imp (fun h => le_of_lt h)
  · exact hs.imp (fun h => le_of_lt h)

end MapCycles
open MapCycles
variable {n : ℕ}

/-- The orbit-maximal planar matching has the ordinary increasing-position
noncrossing property, with root/end seam retained exactly. -/
theorem ordered_no_crossing (a : Perm (Dart n)) (ha : Function.Involutive a)
    (l : List (Dart n)) (hs : l.Pairwise (·<·)) (hc : ∀ x,x∈l)
    (A : Finset (Orbit a))
    (hmax : Nat.card (Orbit (partialReversal a ha A*l.formPerm))=Nat.card (Orbit l.formPerm)+A.card)
    (x y : Dart n) (hx : orbit a x∈A) (hy : orbit a y∈A)
    (hxy : x<y) (hyx : y<a x) (haxy : a x<a y) : False := by
  have hn : l.Nodup := hs.imp (fun h => ne_of_lt h)
  have hsub := ordered_four_sublist hs (hc x) (hc y) (hc (a x)) (hc (a y)) hxy hyx haxy
  obtain ⟨U,L,hL,hsub⟩ := cons_sublist_split hsub
  obtain ⟨V,M,hM,hsub⟩ := cons_sublist_split hsub
  obtain ⟨W,N,hN,hsub⟩ := cons_sublist_split hsub
  obtain ⟨X,R,hR,_⟩ := cons_sublist_split hsub
  have he : l=U++x::(V++y::(W++a x::(X++a y::R))) := by rw [hL,hM,hN,hR]
  have hp : l.formPerm=(x::(V++y::(W++a x::(X++a y::(R++U))))).formPerm := by
    rw [he,formPerm_append_comm U _ (he ▸ hn)]
    simp only [List.cons_append,List.append_assoc]
  have hrot : MapCycles.orbitList l.formPerm x=x::(V++y::(W++a x::(X++a y::(R++U)))) := by
    rw [hp,orbitList_formPerm]
    have hh := (List.perm_append_comm (l₁ := U) (l₂ := x::(V++y::(W++a x::(X++a y::R))))).nodup_iff.mp (he ▸ hn)
    simpa only [List.cons_append,List.append_assoc] using hh
  have hne : orbit a x≠orbit a y := by
    intro heq
    have hh : a.SameCycle x y := Quotient.exact heq
    rcases (MapFinite.sameCycle_involution a ha x y).mp hh with hh|hh
    · exact (ne_of_lt hxy) hh.symm
    · exact (ne_of_lt hyx) hh
  exact no_crossing_of_maximal_orbits a l.formPerm ha A hmax x y hx hy hne V W X (R++U) hrot

/-- Every orbit-maximal one-colour matching is an actual stack matching. -/
theorem maximal_matching_arches (a : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ x,a x≠x) (A : Finset (Orbit a))
    (hmax : Nat.card (Orbit (partialReversal a ha A*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+A.card) :
    ∃ E,Arches (List.finRange (2*(n+1))) E ∧
      (endpoints E).Perm ((List.finRange (2*(n+1))).filter (fun x => decide (orbit a x∈A))) ∧
      ∀ e∈E,e.2=a e.1 ∧ orbit a e.1∈A := by
  classical
  obtain ⟨E,hE,hc,hp⟩ := arches_of_noncrossing a ha (fun x => decide (orbit a x∈A))
    (fun x => by rw [orbit_perm]) (List.finRange (2*(n+1))) (List.pairwise_lt_finRange _)
    (fun x hx hpx => List.mem_finRange _) (fun x hx hpx => hf x)
    (by
      intro x hx y hy hpx hpy hxy hyx hax
      exact ordered_no_crossing a ha _ (List.pairwise_lt_finRange _) List.mem_finRange A hmax x y
        (of_decide_eq_true hpx) (of_decide_eq_true hpy) hxy hyx hax)
  exact ⟨E,hE,hc,fun e he => ⟨(hp e he).1,of_decide_eq_true (hp e he).2⟩⟩

end FKCRT
end


noncomputable section
open List
namespace FKCRT.Inventory
open MapCycles
variable {α : Type*}

lemma scanArches_prefix (f : α→Option Bool) {l v S T : List α} {E : List (α×α)}
    (h : scanArches f l S=some (T,E)) (hv : v<+:l) :
    ∃ R F,scanArches f v S=some (R,F) := by
  obtain ⟨z,rfl⟩ := hv
  rw [scanArches_append] at h
  cases hh : scanArches f v S with
  | none => simp [hh] at h
  | some p => exact ⟨p.1,p.2,rfl⟩

lemma scanArches_color_balance (w : α→TypedLetter) (c : Bool)
    {l S T : List α} {E : List (α×α)}
    (h : scanArches (fun x => colorInstruction c (w x)) l S=some (T,E)) :
    T.length+(l.map w).count (.order c)=S.length+(l.map w).count (.burger c) := by
  induction l generalizing S E with
  | nil => simp only [scanArches,Option.some.injEq,Prod.mk.injEq] at h; simp [h.1]
  | cons x l ih =>
    cases hx : w x with
    | burger b =>
      by_cases hb : b=c
      · subst b
        have hh : scanArches (fun x => colorInstruction c (w x)) l (x::S)=some (T,E) := by
          simpa [scanArches,hx,colorInstruction] using h
        have ht := ih hh
        simpa [hx,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
      · have hh : scanArches (fun x => colorInstruction c (w x)) l S=some (T,E) := by
          simpa [scanArches,hx,colorInstruction,hb] using h
        simpa [hx,hb] using ih hh
    | order b =>
      by_cases hb : b=c
      · subst b
        cases S with
        | nil => simp [scanArches,hx,colorInstruction] at h
        | cons y S =>
          simp only [scanArches,hx,colorInstruction,ite_true] at h
          obtain ⟨p,hp,hpe⟩ := Option.map_eq_some_iff.mp h
          have hpT : p.1=T := congrArg Prod.fst hpe
          have hp' : scanArches (fun x => colorInstruction c (w x)) l S=some (T,p.2) := by
            simpa only [← hpT,Prod.eta,colorInstruction] using hp
          have ht := congrArg (fun k : ℕ => k+1) (ih hp')
          simpa [hx,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
      · have hh : scanArches (fun x => colorInstruction c (w x)) l S=some (T,E) := by
          simpa [scanArches,hx,colorInstruction,hb] using h
        simpa [hx,hb] using ih hh

/-- Complete noncrossing matchings give successful typed inventory reduction,
not merely two balanced endpoint counts. -/
theorem typedRun_of_matchings (w : α→TypedLetter) (l : List α) (hn : l.Nodup)
    (E F : List (α×α)) (hE : Arches l E) (hF : Arches l F)
    (hc : (endpoints (E++F)).Perm l)
    (htE : ∀ e∈E,w e.1=.burger true ∧ w e.2=.order true)
    (htF : ∀ e∈F,w e.1=.burger false ∧ w e.2=.order false) :
    stackTypedRun (l.map w) []=some [] := by
  have hcov := matching_color_coverage w l E F hc htE htF
  have hscan (c : Bool) : ∃ G,scanArches (fun x => colorInstruction c (w x)) l []=some ([],G) := by
    cases c with
    | true =>
      obtain ⟨G,hG,_⟩ := hE.scan hn (fun x => colorInstruction true (w x))
        (fun e he => by simp [colorInstruction,(htE e he).1,(htE e he).2]) hcov.1 []
      exact ⟨G,hG⟩
    | false =>
      obtain ⟨G,hG,_⟩ := hF.scan hn (fun x => colorInstruction false (w x))
        (fun e he => by simp [colorInstruction,(htF e he).1,(htF e he).2]) hcov.2 []
      exact ⟨G,hG⟩
  have hex : ∃ t,stackTypedRun (l.map w) []=some t := by
    apply (typedRun_exists_iff _ _).mpr
    intro v hv c
    obtain ⟨u,hu,rfl⟩ := List.prefix_map_iff.mp hv
    obtain ⟨G,hG⟩ := hscan c
    obtain ⟨R,H,hH⟩ := scanArches_prefix _ hG hu
    have hh := scanArches_color_balance w c hH
    simp only [List.length_nil,List.count_nil,zero_add] at hh ⊢
    omega
  obtain ⟨t,ht⟩ := hex
  have hc0 (c : Bool) : t.count c=0 := by
    obtain ⟨G,hG⟩ := hscan c
    have hh := scanArches_color_balance w c hG
    have hb := typedRun_balance ht c
    simp only [List.length_nil,List.count_nil,zero_add] at hh hb
    omega
  have ht0 : t=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro c hc
    have hh := List.count_pos_iff.mpr hc
    rw [hc0] at hh
    omega
  simpa only [ht0] using ht

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT.MapCycles
variable {α : Type*} [LinearOrder α]

lemma Arches.increasing {l : List α} {E : List (α×α)} (h : Arches l E)
    (hs : l.Pairwise (·<·)) : ∀ e∈E,e.1<e.2 := by
  induction h with
  | nil => simp
  | skip x h ih => exact ih (List.pairwise_cons.mp hs).2
  | pair x y hL hR ihL ihR =>
    have hh := List.pairwise_cons.mp hs
    have ha := List.pairwise_append.mp hh.2
    intro e he
    rcases List.mem_cons.mp he with rfl|he
    · exact hh.1 _ (by simp)
    · rcases List.mem_append.mp he with he|he
      · exact ihL ha.1 e he
      · exact ihR (List.pairwise_cons.mp ha.2.1).2 e he

end MapCycles
namespace Inventory
open MapCycles
variable {n : ℕ}

/-- The actual two-colour opening/closing word in canonical rooted tour order. -/
def matchingWord (a : Perm (Dart n)) (A : Finset (Orbit a)) (i : Dart n) : TypedLetter :=
  if i<a i then .burger (decide (orbit a i∈A)) else .order (decide (orbit a i∈A))

/-- Surjectivity of the stack correspondence on canonical two-colour tours,
with the complete literal inverse pairing and rotation. -/
theorem maximal_matching_word (a : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ i,a i≠i) (A : Finset (Orbit a))
    (hE : Nat.card (Orbit (partialReversal a ha A*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+A.card)
    (hF : Nat.card (Orbit (partialReversal a ha Aᶜ*(List.finRange (2*(n+1))).formPerm))=
      Nat.card (Orbit (List.finRange (2*(n+1))).formPerm)+Aᶜ.card) :
    stackTypedRun ((List.finRange (2*(n+1))).map (matchingWord a A)) []=some [] ∧
    ∃ E F,Arches (List.finRange (2*(n+1))) E ∧ Arches (List.finRange (2*(n+1))) F ∧
      (endpoints (E++F)).Perm (List.finRange (2*(n+1))) ∧
      (∀ e∈E,matchingWord a A e.1=.burger true ∧ matchingWord a A e.2=.order true) ∧
      (∀ e∈F,matchingWord a A e.1=.burger false ∧ matchingWord a A e.2=.order false) ∧
      turns (E++F)=a ∧ turns E=partialReversal a ha A := by
  obtain ⟨E,he,hce,hpe⟩ := maximal_matching_arches a ha hf A hE
  obtain ⟨F,hf',hcf,hpf⟩ := maximal_matching_arches a ha hf Aᶜ hF
  have hien := he.increasing (List.pairwise_lt_finRange _)
  have hifn := hf'.increasing (List.pairwise_lt_finRange _)
  have hc : (endpoints (E++F)).Perm (List.finRange (2*(n+1))) := by
    rw [endpoints_append]
    apply (hce.append hcf).trans
    simpa only [Finset.mem_compl,decide_not] using
      List.filter_append_perm (fun x => decide (orbit a x∈A)) (List.finRange (2*(n+1)))
  have htE : ∀ e∈E,matchingWord a A e.1=.burger true ∧ matchingWord a A e.2=.order true := by
    intro e he'
    obtain ⟨hei,hmem⟩ := hpe e he'
    have hlt := hien e he'
    have heii : a e.2=e.1 := by rw [hei,ha]
    have hm2 : orbit a e.2∈A := by rw [hei,orbit_perm]; exact hmem
    simp only [matchingWord,← hei,heii,ite_eq_left hlt,ite_eq_right (not_lt_of_ge hlt.le),
      decide_eq_true hmem,decide_eq_true hm2,and_self]
  have htF : ∀ e∈F,matchingWord a A e.1=.burger false ∧ matchingWord a A e.2=.order false := by
    intro e he'
    obtain ⟨hei,hmem⟩ := hpf e he'
    have hlt := hifn e he'
    have heii : a e.2=e.1 := by rw [hei,ha]
    have hm1 : orbit a e.1∉A := Finset.mem_compl.mp hmem
    have hm2 : orbit a e.2∉A := by rw [hei,orbit_perm]; exact hm1
    simp only [matchingWord,← hei,heii,ite_eq_left hlt,ite_eq_right (not_lt_of_ge hlt.le),
      decide_eq_false hm1,decide_eq_false hm2,and_self]
  have hn : (endpoints (E++F)).Nodup := hc.nodup_iff.mpr (List.nodup_finRange _)
  have ha' : turns (E++F)=a := by
    apply Equiv.ext
    intro i
    obtain ⟨e,he',rfl|rfl⟩ := mem_endpoints.mp (hc.mem_iff.mpr (List.mem_finRange i))
    · rw [(turns_pair hn e he').1]
      rcases List.mem_append.mp he' with he'|he'
      · exact (hpe e he').1
      · exact (hpf e he').1
    · rw [(turns_pair hn e he').2]
      have hh : e.2=a e.1 := by
        rcases List.mem_append.mp he' with he'|he'
        · exact (hpe e he').1
        · exact (hpf e he').1
      rw [hh,ha]
  have hpart : turns E=partialReversal a ha A := by
    apply Equiv.ext
    intro i
    rw [partialReversal_apply]
    have hmem : i∈endpoints E ↔ orbit a i∈A := by
      rw [hce.mem_iff,List.mem_filter]
      simp
    split_ifs with hi
    · rw [turns_sublist_apply hn (List.sublist_append_left _ _) (hmem.mpr hi),ha']
    · exact turns_fixed_of_notMem (fun h => hi (hmem.mp h))
  exact ⟨typedRun_of_matchings _ _ (List.nodup_finRange _) E F he hf' hc htE htF,
    E,F,he,hf',hc,htE,htF,ha',hpart⟩

end Inventory
end FKCRT
end

end OAI
