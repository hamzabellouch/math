import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.BinarySyntax

namespace OAI

namespace LargeIndependentSets.BinarySyntax

inductive Mark where
  | first (r : Fin 3)
  | empty
  deriving DecidableEq

def event : Phase → Bool → Option Mark
  | .sign r true, _ => some (.first r)
  | .widthStart, false => some .empty
  | _, _ => none

def shift (k : ℕ) (xs : List (ℕ × Mark)) : List (ℕ × Mark) :=
  xs.map (fun x => (k+x.1,x.2))

@[simp] lemma shift_nil (k : ℕ) : shift k []=[] := rfl
@[simp] lemma shift_cons (k : ℕ) (p : ℕ) (e : Mark) (xs : List (ℕ × Mark)) :
    shift k ((p,e)::xs)=(k+p,e)::shift k xs := rfl
@[simp] lemma shift_append (k : ℕ) (a b : List (ℕ × Mark)) :
    shift k (a++b)=shift k a++shift k b := List.map_append
@[simp] lemma shift_shift (j k : ℕ) (xs : List (ℕ × Mark)) :
    shift j (shift k xs)=shift (j+k) xs := by simp [shift,List.map_map,Function.comp_def,Nat.add_assoc]
@[simp] lemma shift_zero (xs : List (ℕ × Mark)) : shift 0 xs=xs := by simp [shift]

def events (q : Phase) : List Bool → List (ℕ × Mark)
  | [] => []
  | b::s => ((event q b).toList.map (fun e => (0,e))) ++ shift 1 (events (transition q b) s)

lemma events_append (q : Phase) (a b : List Bool) :
    events q (a++b)=events q a++shift a.length (events (run q a) b) := by
  induction a generalizing q with
  | nil => simp [events]
  | cons x a ih =>
    simp only [List.cons_append,events,ih,shift_append,shift_shift,List.length_cons,run_cons,
      List.append_assoc,Nat.add_comm 1]

lemma events_header (s : List Bool) : events .headerMark (frame s)=[] := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [frame,events,transition,event,ih]

lemma events_name (r : Fin 3) (s : List Bool) : events (.mark r) (frame s)=[] := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [frame,events,transition,event,ih]

lemma events_literal (r : Fin 3) (first : Bool) (l : Literal) :
    events (.sign r first) (literalBits l)=if first then [(0,.first r)] else [] := by
  cases first <;> simp [literalBits,nameBits,events,event,transition,events_name]

def clauseMark (C : List Literal) : ℕ × Mark :=
  if C=[] then (0,.empty) else ((nameBits C.length).length,.first ⟨(C.length-1)%3,Nat.mod_lt _ (by decide)⟩)

lemma events_clause (C : List Literal) (hw : C.length ≤ 3) :
    events .widthStart (clauseBits C)=[clauseMark C] := by
  cases C with
  | nil => rfl
  | cons a C =>
    cases C with
    | nil =>
      simp only [clauseMark,clauseBits,List.cons_ne_nil,ite_false,List.length_cons,List.length_nil,
        List.flatMap_cons,List.flatMap_nil]
      change events .widthStart ([true,true,false]++(literalBits a++[])) = [(3,.first 0)]
      rw [events_append,events_append]
      simp [events,event,transition,run,events_literal]
    | cons b C =>
      cases C with
      | nil =>
        simp only [clauseMark,clauseBits,List.cons_ne_nil,ite_false,List.length_cons,List.length_nil,
          List.flatMap_cons,List.flatMap_nil]
        change events .widthStart ([true,false,true,true,false]++(literalBits a++(literalBits b++[]))) = [(5,.first 1)]
        rw [events_append]
        change [] ++ shift 5 (events (.sign 1 true) (literalBits a++(literalBits b++[]))) = _
        rw [events_append,events_append,run_literal]
        simp [events_literal,events,after]
      | cons c C =>
        have hc : C=[] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hw; omega
        subst C
        simp only [clauseMark,clauseBits,List.cons_ne_nil,ite_false,List.length_cons,List.length_nil,
          List.flatMap_cons,List.flatMap_nil]
        change events .widthStart ([true,true,true,true,false]++(literalBits a++(literalBits b++(literalBits c++[])))) = [(5,.first 2)]
        rw [events_append]
        change [] ++ shift 5 (events (.sign 2 true) (literalBits a++(literalBits b++(literalBits c++[])))) = _
        rw [events_append,run_literal]
        change shift 5 (events (.sign 2 true) (literalBits a) ++
          shift (literalBits a).length (events (.sign 1 false) (literalBits b++(literalBits c++[])))) = _
        rw [events_append,events_append,run_literal]
        simp [events_literal,events,after]

lemma mem_shift (k p : ℕ) (e : Mark) (xs : List (ℕ × Mark)) :
    (p,e) ∈ shift k xs ↔ ∃ j, (j,e) ∈ xs ∧ p=k+j := by
  simp only [shift,List.mem_map,Prod.exists,Prod.mk.injEq]
  constructor
  · rintro ⟨j,d,h,he,hd⟩; subst d; exact ⟨j,h,he.symm⟩
  · rintro ⟨j,h,rfl⟩; exact ⟨j,e,h,rfl,rfl⟩

lemma events_complete (q : Phase) (s : List Bool) (p : ℕ) (hp : p < s.length) (e : Mark) :
    (p,e) ∈ events q s ↔ event (run q (s.take p)) s[p]=some e := by
  induction s generalizing q p with
  | nil => simp at hp
  | cons b s ih =>
    cases p with
    | zero =>
      simp only [events,List.mem_append,List.mem_map,Option.mem_toList,Prod.mk.injEq,
        true_and,mem_shift,List.take_zero,run_nil,List.getElem_cons_zero]
      constructor
      · rintro (⟨e',he',rfl⟩|⟨j,hj,he⟩)
        · exact he'
        · omega
      · intro h; exact Or.inl ⟨e,h,rfl⟩
    | succ p =>
      have hp' : p < s.length := by simpa using hp
      simp only [events,List.mem_append,List.mem_map,Option.mem_toList,Prod.mk.injEq,
        show ¬(0=p+1) by omega,false_and,and_false,exists_false, false_or,mem_shift,
        List.take_succ_cons,run_cons,List.getElem_cons_succ]
      rw [← ih (transition q b) p hp']
      constructor
      · rintro ⟨j,hj,he⟩
        have : j=p := by omega
        subst j
        exact hj
      · intro h; exact ⟨p,h,by omega⟩

lemma event_clause_location (Cs : List (List Literal)) (hw : ∀ C ∈ Cs, C.length ≤ 3)
    (p : ℕ) (e : Mark) (he : (p,e) ∈ events .widthStart (Cs.flatMap clauseBits)) :
    ∃ pre C post, Cs=pre++C::post ∧
      p=(pre.flatMap clauseBits).length+(clauseMark C).1 ∧ e=(clauseMark C).2 := by
  induction Cs generalizing p with
  | nil => simp [events] at he
  | cons C Cs ih =>
    rw [List.flatMap_cons,events_append,events_clause C (hw C (by simp)),
      run_clause C (hw C (by simp))] at he
    rcases List.mem_append.mp he with h | h
    · have hh : (p,e)=clauseMark C := List.mem_singleton.mp h
      refine ⟨[],C,Cs,rfl,?_,?_⟩
      · simpa using congrArg Prod.fst hh
      · exact congrArg Prod.snd hh
    · obtain ⟨j,hj,hp⟩ := (mem_shift _ _ _ _).mp h
      obtain ⟨pre,D,post,hs,hj',he'⟩ := ih (fun D hD => hw D (by simp [hD])) j hj
      refine ⟨C::pre,D,post,by simp [hs],?_,he'⟩
      simp [hp,hj',List.flatMap_cons,Nat.add_assoc]

lemma events_bound (q : Phase) (s : List Bool) (p : ℕ) (e : Mark)
    (hp : (p,e) ∈ events q s) : p < s.length := by
  induction s generalizing q p with
  | nil => simp [events] at hp
  | cons b s ih =>
    rw [events,List.mem_append] at hp
    rcases hp with h | h
    · obtain ⟨e',_he,he'⟩ := List.mem_map.mp h
      have : p=0 := (congrArg Prod.fst he').symm
      simp [this]
    · obtain ⟨j,hj,hp⟩ := (mem_shift _ _ _ _).mp h
      have := ih (transition q b) j hj
      simp only [List.length_cons]
      omega

lemma clause_event_location (pre : List (List Literal)) (C : List Literal) (post : List (List Literal))
    (hw : ∀ D ∈ pre++C::post, D.length ≤ 3) :
    ((pre.flatMap clauseBits).length+(clauseMark C).1,(clauseMark C).2) ∈
      events .widthStart ((pre++C::post).flatMap clauseBits) := by
  rw [List.flatMap_append,events_append,run_clauses pre (fun D hD => hw D (by simp [hD]))]
  apply List.mem_append_right
  apply (mem_shift _ _ _ _).mpr
  refine ⟨(clauseMark C).1,?_,rfl⟩
  rw [List.flatMap_cons,events_append,events_clause C (hw C (by simp))]
  apply List.mem_append_left
  simp

lemma event_formula_location (F : Formula) (p : ℕ) (e : Mark)
    (he : (p,e) ∈ events .headerMark (formulaBits F)) :
    ∃ pre C post, F.clauses=pre++C::post ∧
      p=(nameBits F.clauses.length).length+(pre.flatMap clauseBits).length+(clauseMark C).1 ∧
      e=(clauseMark C).2 := by
  rw [formulaBits,events_append] at he
  simp only [nameBits,events_header,run_header,List.nil_append] at he
  obtain ⟨j,hj,hp⟩ := (mem_shift _ _ _ _).mp he
  obtain ⟨pre,C,post,hs,hj',he'⟩ := event_clause_location F.clauses F.width j e hj
  exact ⟨pre,C,post,hs,by dsimp [nameBits]; omega,he'⟩

lemma formula_clause_event (F : Formula) (pre : List (List Literal)) (C : List Literal)
    (post : List (List Literal)) (hF : F.clauses=pre++C::post) :
    ((nameBits F.clauses.length).length+(pre.flatMap clauseBits).length+(clauseMark C).1,
      (clauseMark C).2) ∈ events .headerMark (formulaBits F) := by
  rw [formulaBits,events_append]
  simp only [nameBits,events_header,run_header,List.nil_append]
  apply (mem_shift _ _ _ _).mpr
  refine ⟨(pre.flatMap clauseBits).length+(clauseMark C).1,?_,by omega⟩
  rw [hF]
  exact clause_event_location pre C post (fun D hD => F.width D (hF ▸ hD))

end LargeIndependentSets.BinarySyntax

end OAI
