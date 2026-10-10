import OAI.Probability.FKMaps.MapCycles

namespace OAI

noncomputable section
open Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

/-- Ordered stack matching, with unpaired positions allowed. The skipped
positions will be endpoints of the other colour in the map tour. -/
inductive Arches : List α → List (α × α) → Prop
  | nil : Arches [] []
  | skip (a : α) {l E} : Arches l E → Arches (a :: l) E
  | pair (a b : α) {L R E F} : Arches L E → Arches R F →
      Arches (a :: (L ++ b :: R)) ((a,b) :: (E ++ F))

/-- Left transpositions in traversal order. -/
def turns : List (α × α) → Perm α
  | [] => 1
  | (a,b) :: E => turns E * swap a b

@[simp] lemma turns_nil : turns ([] : List (α × α)) = 1 := rfl
@[simp] lemma turns_cons (e : α × α) (E) :
    turns (e :: E) = turns E * swap e.1 e.2 := by cases e; rfl

lemma turns_append (E F : List (α × α)) :
    turns (E ++ F) = turns F * turns E := by
  induction E with
  | nil => simp
  | cons e E ih => simp only [List.cons_append,turns_cons,ih,mul_assoc]

omit [DecidableEq α] in
lemma Arches.endpoints {l : List α} {E} (h : Arches l E) :
    ∀ e ∈ E, e.1 ∈ l ∧ e.2 ∈ l := by
  induction h with
  | nil => simp
  | skip a h ih =>
    intro e he
    exact ⟨List.mem_cons_of_mem _ (ih e he).1,List.mem_cons_of_mem _ (ih e he).2⟩
  | pair a b hL hR ihL ihR =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      simp
    · rcases List.mem_append.mp he with he | he
      · exact ⟨by simp [(ihL e he).1],by simp [(ihL e he).2]⟩
      · exact ⟨by simp [(ihR e he).1],by simp [(ihR e he).2]⟩

lemma turns_fixed (E : List (α × α)) {x : α}
    (hx : ∀ e ∈ E, x ≠ e.1 ∧ x ≠ e.2) : turns E x = x := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    rw [turns_cons,mul_apply,swap_apply_of_ne_of_ne (hx e List.mem_cons_self).1
      (hx e List.mem_cons_self).2]
    exact ih (fun e he => hx e (List.mem_cons_of_mem _ he))

lemma Arches.turns_fixed {l : List α} {E} (h : Arches l E) {x : α} (hx : x ∉ l) :
    turns E x = x := by
  apply FKCRT.MapCycles.turns_fixed
  intro e he
  exact ⟨fun hh => hx (hh ▸ (h.endpoints e he).1),
    fun hh => hx (hh ▸ (h.endpoints e he).2)⟩

lemma formPerm_append_comm (L R : List α) (hn : (L ++ R).Nodup) :
    (L ++ R).formPerm = (R ++ L).formPerm := by
  have h : (L ++ R).rotate L.length = R ++ L := by simp
  rw [← h,List.formPerm_rotate _ hn]

lemma cut_local_action (p : Perm α) (a b : α) (L R : List α)
    (hn : ((a :: L) ++ (b :: R)).Nodup)
    (hp : ∀ x ∈ (a :: L) ++ (b :: R), p x = ((a :: L) ++ (b :: R)).formPerm x) :
    (∀ x ∈ a :: L, (swap a b * p) x = (a :: L).formPerm x) ∧
    (∀ x ∈ b :: R, (swap a b * p) x = (b :: R).formPerm x) := by
  have hd : List.Disjoint (a :: L) (b :: R) :=
    List.disjoint_iff_ne.mpr (List.nodup_append.mp hn).2.2
  constructor
  · intro x hx
    have hxr : x ∉ b :: R := fun hh => List.disjoint_left.mp hd hx hh
    have hh := congrArg (fun u : Perm α => u x) (swap_mul_formPerm_cut a b L R hn)
    simpa only [mul_apply,hp x (List.mem_append_left _ hx),List.cons_append,
      List.formPerm_apply_of_notMem hxr] using hh
  · intro x hx
    have hxl : (b :: R).formPerm x ∉ a :: L := fun hh =>
      List.disjoint_left.mp hd hh (List.formPerm_apply_mem_of_mem hx)
    have hh := congrArg (fun u : Perm α => u x) (swap_mul_formPerm_cut a b L R hn)
    simpa only [mul_apply,hp x (List.mem_append_right _ hx),List.cons_append,
      List.formPerm_apply_of_notMem hxl] using hh

/-- Stack/noncrossing chords attain the maximum possible cycle count.
The unused initial string is arbitrary, so this also handles skipped darts
and the end/start seam of a rooted tour. -/
theorem Arches.card_orbits_turns [Fintype α] {l : List α} {E}
    (h : Arches l E) (Z : List α) (p : Perm α)
    (hn : (Z ++ l).Nodup)
    (hp : ∀ x ∈ Z ++ l, p x = (Z ++ l).formPerm x) :
    Nat.card (Orbits (turns E * p)) = Nat.card (Orbits p) + E.length := by
  induction h generalizing Z p with
  | nil => simp
  | @skip a l E h ih =>
    have he : Z ++ a :: l = (Z ++ [a]) ++ l := by simp
    exact ih (Z ++ [a]) p (he ▸ hn) (by simpa only [he] using hp)
  | @pair a b L R E F hL hR ihL ihR =>
    let C := (a :: L) ++ (b :: (R ++ Z))
    have hC : C.Nodup := by
      change ((a :: L) ++ (b :: (R ++ Z))).Nodup
      simpa only [List.cons_append,List.append_assoc] using
        (List.nodup_append_comm.mp hn)
    have he : (Z ++ a :: (L ++ b :: R)).formPerm = C.formPerm := by
      rw [formPerm_append_comm _ _ hn]
      simp only [C,List.cons_append,List.append_assoc]
    have hpC (x : α) (hx : x ∈ C) : p x = C.formPerm x := by
      rw [← he]
      apply hp
      simpa only [C,List.mem_append,List.mem_cons,or_assoc,or_comm,or_left_comm] using hx
    have hab : a ≠ b := fun h => hC.notMem (by simp [h])
    have hsame : p.SameCycle a b := sameCycle_of_list p hC hpC (by simp [C]) (by simp [C])
    have hzero := card_orbits_swap_of_sameCycle p hab hsame
    have hcut := cut_local_action p a b L (R ++ Z) hC hpC
    have hnL : ([a] ++ L).Nodup := (List.nodup_append.mp hC).1
    have hE := ihL [a] (swap a b * p) hnL hcut.1
    have hnR : ((Z ++ [b]) ++ R).Nodup := by
      have ht := (List.nodup_append.mp hC).2.1
      have hh : (b :: (R ++ Z)) = (b :: R) ++ Z := by simp
      rw [hh] at ht
      simpa only [List.append_assoc,List.singleton_append] using
        (List.nodup_append_comm.mp ht)
    have hother (x : α) (hx : x ∈ (Z ++ [b]) ++ R) :
        (turns E * (swap a b * p)) x = ((Z ++ [b]) ++ R).formPerm x := by
      have hxR : x ∈ b :: (R ++ Z) := by
        simpa only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,false_or,or_assoc,or_comm,
          or_left_comm] using hx
      have hpx := hcut.2 x hxR
      have hpxR : (swap a b * p) x ∈ b :: (R ++ Z) := by
        rw [hpx]; exact List.formPerm_apply_mem_of_mem hxR
      have hnLR := (List.nodup_append.mp hC).2.2
      have hnot : (swap a b * p) x ∉ L := fun hh =>
        hnLR _ (List.mem_cons_of_mem _ hh) _ hpxR rfl
      rw [mul_apply,hL.turns_fixed hnot,hpx]
      have ht : (Z ++ (b :: R)).Nodup := by simpa using hnR
      have hh := formPerm_append_comm Z (b :: R) ht
      simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        (congrArg (fun u : Perm α => u x) hh).symm
    have hF := ihR (Z ++ [b]) (turns E * (swap a b * p)) hnR hother
    simp only [turns_cons,turns_append,List.length_cons,List.length_append]
    rw [mul_assoc,mul_assoc,hF,hE,hzero]
    omega

end FKCRT.MapCycles
end


noncomputable section
open List
namespace FKCRT.MapCycles
variable {α : Type*}

lemma Arches.append {l r : List α} {E F : List (α×α)}
    (h : Arches l E) (h' : Arches r F) : Arches (l++r) (E++F) := by
  induction h with
  | nil => simpa using h'
  | skip a h ih => simpa using Arches.skip a ih
  | pair a b hL hR ihL ihR =>
    simpa only [List.cons_append,List.append_assoc] using Arches.pair a b hL ihR

lemma Arches.empty (l : List α) : Arches l [] := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .skip a ih

lemma cons_sublist_split {a : α} {l r : List α} (h : a::l<+r) :
    ∃ s t,r=s++a::t ∧ l<+t := by
  induction r with
  | nil => simp at h
  | cons b r ih =>
    cases h with
    | cons _ h =>
      obtain ⟨s,t,rfl,ht⟩ := ih h
      exact ⟨b::s,t,rfl,ht⟩
    | cons_cons _ h => exact ⟨[],r,rfl,h⟩

lemma Arches.mono {l r : List α} {E : List (α×α)} (h : Arches l E)
    (hlr : l<+r) : Arches r E := by
  induction h generalizing r with
  | nil => exact Arches.empty r
  | skip a h ih => exact ih (List.sublist_of_cons_sublist hlr)
  | pair a b hL hR ihL ihR =>
    obtain ⟨S,T,rfl,hT⟩ := cons_sublist_split hlr
    obtain ⟨U,V,rfl,hU,hV⟩ := List.append_sublist_iff.mp hT
    obtain ⟨Q,R,rfl,hR'⟩ := cons_sublist_split hV
    have hu := (ihL hU).append (Arches.empty Q)
    have hp := Arches.pair a b (by simpa using hu) (ihR hR')
    have hf := (Arches.empty S).append hp
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using hf

/-- Flatten the pair endpoints without imposing an artificial pair order. -/
def endpoints (E : List (α×α)) : List α := E.flatMap (fun e => [e.1,e.2])

@[simp] lemma endpoints_nil : endpoints ([] : List (α×α))=[] := rfl
@[simp] lemma endpoints_cons (e : α×α) (E : List (α×α)) :
    endpoints (e::E)=e.1::e.2::endpoints E := rfl
lemma endpoints_append (E F : List (α×α)) : endpoints (E++F)=endpoints E++endpoints F := by
  simp [endpoints]

/-- Every Dyck path, on an arbitrary ordered list of positions, has a complete
noncrossing arch pairing. This is a constructive existence statement, not a
planarity assumption on a map. -/
theorem dyck_arches (p : DyckWord) (l : List α) (f : α→DyckStep)
    (hl : l.map f=p.toList) :
    ∃ E : List (α×α), Arches l E ∧ (endpoints E).Perm l ∧
      ∀ e∈E,f e.1=.U ∧ f e.2=.D := by
  induction hp : p.semilength using Nat.strong_induction_on generalizing p l with
  | h n ih =>
    by_cases hz : p=0
    · subst p
      have hm : l.map f=[] := hl
      have hn : l=[] := List.map_eq_nil_iff.mp hm
      subst l
      exact ⟨[],.nil,.refl _,by simp⟩
    · have hdec := p.nest_insidePart_add_outsidePart hz
      have he : p.toList = DyckStep.U::(p.insidePart.toList++DyckStep.D::p.outsidePart.toList) := by
        have hh := (congrArg DyckWord.toList hdec).symm
        change p.toList = ([DyckStep.U]++p.insidePart.toList++[DyckStep.D])++p.outsidePart.toList at hh
        simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hh
      cases l with
      | nil => rw [he] at hl; simp at hl
      | cons a l =>
        rw [he,List.map_cons,List.cons.injEq] at hl
        obtain ⟨ha,hl⟩ := hl
        have hlen : p.insidePart.toList.length<l.length := by
          have hc := congrArg List.length hl
          simp only [List.length_map,List.length_append,List.length_cons] at hc
          omega
        let j := p.insidePart.toList.length
        let L := l.take j
        let b := l[j]
        let R := l.drop (j+1)
        have hl' : l=L++b::R := by
          dsimp [L,b,R,j]
          rw [← List.drop_eq_getElem_cons hlen,List.take_append_drop]
        have hL : L.map f=p.insidePart.toList := by
          dsimp [L,j]
          rw [List.map_take,hl,List.take_append_of_le_length (by rfl)]
          simp
        have hBR : (b::R).map f=DyckStep.D::p.outsidePart.toList := by
          rw [hl',List.map_append,hL] at hl
          exact List.append_cancel_left hl
        simp only [List.map_cons,List.cons.injEq] at hBR
        obtain ⟨hb,hR⟩ := hBR
        obtain ⟨E,hE,hEp,hEf⟩ := ih p.insidePart.semilength
          (by rw [← hp]; exact p.semilength_insidePart_lt hz) _ _ hL rfl
        obtain ⟨F,hF,hFp,hFf⟩ := ih p.outsidePart.semilength
          (by rw [← hp]; exact p.semilength_outsidePart_lt hz) _ _ hR rfl
        refine ⟨(a,b)::(E++F),?_,?_,?_⟩
        · rw [hl']; exact Arches.pair a b hE hF
        · rw [endpoints_cons,endpoints_append,hl']
          have hh := hEp.append hFp
          exact (hh.cons b |>.cons a).trans (List.Perm.cons a (List.perm_middle.symm))
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact ⟨ha,hb⟩
          · rcases List.mem_append.mp he with he | he
            · exact hEf e he
            · exact hFf e he

end FKCRT.MapCycles
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma mem_endpoints {x : α} {E : List (α×α)} :
    x∈endpoints E ↔ ∃ e∈E,x=e.1 ∨ x=e.2 := by
  simp [endpoints,List.mem_flatMap]

lemma turns_fixed_of_notMem {E : List (α×α)} {x : α} (h : x∉endpoints E) :
    turns E x=x := by
  apply turns_fixed
  intro e he
  exact ⟨fun hh => h (mem_endpoints.mpr ⟨e,he,Or.inl hh⟩),
    fun hh => h (mem_endpoints.mpr ⟨e,he,Or.inr hh⟩)⟩

lemma turns_pair {E : List (α×α)} (hn : (endpoints E).Nodup) :
    ∀ e∈E,turns E e.1=e.2 ∧ turns E e.2=e.1 := by
  induction E with
  | nil => simp
  | cons e E ih =>
    obtain ⟨a,b⟩ := e
    simp only [endpoints_cons,List.nodup_cons] at hn
    have ha : a∉endpoints E := fun h => hn.1 (List.mem_cons_of_mem _ h)
    have hb : b∉endpoints E := hn.2.1
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      constructor
      · rw [turns_cons,mul_apply,swap_apply_left,turns_fixed_of_notMem hb]
      · rw [turns_cons,mul_apply,swap_apply_right,turns_fixed_of_notMem ha]
    · have h1 := mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩
      have h2 := mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩
      have h1a : e.1≠a := fun hh => ha (hh ▸ h1)
      have h1b : e.1≠b := fun hh => hb (hh ▸ h1)
      have h2a : e.2≠a := fun hh => ha (hh ▸ h2)
      have h2b : e.2≠b := fun hh => hb (hh ▸ h2)
      simpa only [turns_cons,mul_apply,swap_apply_of_ne_of_ne h1a h1b,
        swap_apply_of_ne_of_ne h2a h2b] using ih hn.2.2 e he

omit [DecidableEq α] in
lemma endpoints_pair_ne {E : List (α×α)} (hn : (endpoints E).Nodup)
    {e : α×α} (he : e∈E) : e.1≠e.2 := by
  have hp : [e.1,e.2]<+endpoints E := by
    obtain ⟨L,R,rfl⟩ := List.mem_iff_append.mp he
    simp only [endpoints_append,endpoints_cons]
    exact (show [e.1,e.2] <+ [e.1,e.2]++endpoints R from List.sublist_append_left _ _).trans
      (show e.1::e.2::endpoints R <+ endpoints L++e.1::e.2::endpoints R from List.sublist_append_right _ _)
  have hh := hn.sublist hp
  simpa using hh

lemma turns_involutive {E : List (α×α)} (hn : (endpoints E).Nodup) :
    Function.Involutive (turns E) := by
  intro x
  by_cases hx : x∈endpoints E
  · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
    · rw [(turns_pair hn e he).1,(turns_pair hn e he).2]
    · rw [(turns_pair hn e he).2,(turns_pair hn e he).1]
  · rw [turns_fixed_of_notMem hx,turns_fixed_of_notMem hx]

lemma turns_self {E : List (α×α)} (hn : (endpoints E).Nodup) : turns E*turns E=1 := by
  apply Equiv.ext
  exact turns_involutive hn

lemma turns_eq_self_iff {E : List (α×α)} (hn : (endpoints E).Nodup) (x : α) :
    turns E x=x ↔ x∉endpoints E := by
  constructor
  · intro h hx
    obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
    · exact endpoints_pair_ne hn he (h.symm.trans (turns_pair hn e he).1)
    · exact endpoints_pair_ne hn he ((turns_pair hn e he).2.symm.trans h)
  · exact turns_fixed_of_notMem

lemma turns_mem_iff {E : List (α×α)} (hn : (endpoints E).Nodup) (x : α) :
    turns E x∈endpoints E ↔ x∈endpoints E := by
  by_cases hx : x∈endpoints E
  · simp only [hx,iff_true]
    obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hx
    · rw [(turns_pair hn e he).1]; exact mem_endpoints.mpr ⟨e,he,Or.inr rfl⟩
    · rw [(turns_pair hn e he).2]; exact mem_endpoints.mpr ⟨e,he,Or.inl rfl⟩
  · simp [turns_fixed_of_notMem hx,hx]

lemma turns_sublist_apply {E F : List (α×α)} (hn : (endpoints F).Nodup)
    (hEF : E<+F) {x : α} (hx : x∈endpoints E) : turns E x=turns F x := by
  have hs : (endpoints E)<+(endpoints F) := hEF.flatMap _
  have he := hn.sublist hs
  obtain ⟨e,he',rfl|rfl⟩ := mem_endpoints.mp hx
  · rw [(turns_pair he e he').1,(turns_pair hn e (hEF.subset he')).1]
  · rw [(turns_pair he e he').2,(turns_pair hn e (hEF.subset he')).2]

end FKCRT.MapCycles
end

end OAI
