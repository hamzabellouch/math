import Mathlib

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames
namespace PartialFold
variable {P A B : Type*} (f : P × A × B → Part B)

def left (p : P) : List A → B → Part B
  | [], b => Part.some b
  | a::w, b => (f (p,a,b)).bind (left p w)

def right (p : P) : List A → B → Part B
  | [], b => Part.some b
  | a::w, b => (right p w b).bind (fun c => f (p,a,c))

theorem left_append (p : P) (u v : List A) (b : B) :
    left f p (u++v) b = (left f p u b).bind (left f p v) := by
  induction u generalizing b with
  | nil => simp [left]
  | cons a u ih =>
    simp only [List.cons_append,left,Part.bind_assoc]
    congr 1
    funext c
    exact ih c

theorem right_eq_left_reverse (p : P) (w : List A) (b : B) :
    right f p w b = left f p w.reverse b := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [right,List.reverse_cons,left_append,← ih,left]
    simp only [Part.bind_some_right]

def loop : P × List A × B → Part (B ⊕ (P × List A × B))
  | (_,[],b) => Part.some (.inl b)
  | (p,a::w,b) => (f (p,a,b)).map (fun c => .inr (p,w,c))

theorem fix_loop (p : P) (w : List A) (b : B) :
    PFun.fix (loop f) (p,w,b) = left f p w b := by
  induction w generalizing b with
  | nil =>
    apply Part.ext
    intro out
    erw [PFun.mem_fix_iff]
    simp only [loop,Part.mem_some_iff,Sum.inl.injEq,Sum.inr_ne_inl,exists_false,
      false_and,or_false,left]
  | cons a w ih =>
    apply Part.ext
    intro out
    erw [PFun.mem_fix_iff]
    simp only [loop,Part.mem_map_iff,Sum.inr_ne_inl,exists_false,and_false,false_or]
    constructor
    · rintro ⟨⟨p',w',c⟩,⟨c',hc,he⟩,ho⟩
      have he' : (p,w,c') = (p',w',c) := Sum.inr.inj he
      obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj he' |>.imp_right Prod.mk.inj
      rw [ih] at ho
      exact Part.mem_bind_iff.mpr ⟨c',hc,ho⟩
    · intro ho
      obtain ⟨c,hc,ho⟩ := Part.mem_bind_iff.mp ho
      exact ⟨(p,w,c),⟨c,hc,rfl⟩,by rw [ih]; exact ho⟩

variable [Primcodable P] [Primcodable A] [Primcodable B]
variable (hf : Partrec f)

include hf in
theorem partrec_loop : Partrec (loop f) := by
  let S := P × List A × B
  have hh : Computable (fun s : S => s.2.1.head?) :=
    Primrec.list_head?.to_comp.comp (Computable.fst.comp Computable.snd)
  have he : Partrec₂ (fun (s : S) (a : A) =>
      (f (s.1,a,s.2.2)).map (fun c => (Sum.inr (s.1,s.2.1.tail,c) : B ⊕ S))) := by
    have hc : Computable (fun x : S × A => (x.1.1,x.2,x.1.2.2)) :=
      (Computable.fst.comp Computable.fst).pair
        (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    apply (hf.comp hc).map
    exact (Computable.sumInr.comp
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Primrec.list_tail.to_comp.comp
          (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))).pair
          Computable.snd))).to₂
  exact (Partrec.optionCasesOn_right hh
    (Computable.sumInl.comp (Computable.snd.comp Computable.snd)) he).of_eq
    (by intro ⟨p,w,b⟩; cases w <;> rfl)

include hf in
theorem partrec_left : Partrec (fun x : P × List A × B => left f x.1 x.2.1 x.2.2) :=
  (Partrec.fix (partrec_loop f hf)).of_eq (fun ⟨p,w,b⟩ => fix_loop f p w b)

include hf in
theorem partrec_right : Partrec (fun x : P × List A × B => right f x.1 x.2.1 x.2.2) := by
  have hc : Computable (fun x : P × List A × B => (x.1,x.2.1.reverse,x.2.2)) :=
    Computable.fst.pair ((Computable.list_reverse.comp (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd))
  exact ((partrec_left f hf).comp hc).of_eq (fun ⟨p,w,b⟩ => (right_eq_left_reverse f p w b).symm)

end PartialFold
end SimpleFInftyOvergroups.EffectiveNames

end OAI
