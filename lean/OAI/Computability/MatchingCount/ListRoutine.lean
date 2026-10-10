import OAI.Computability.MatchingCount.PolyCoding

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial
namespace Routine
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
  {f : α×List α → β}

noncomputable def listCases (b : β)
    (p : Routine (fun z : α×List α => pairBits (ea z.1) (listCode ea z.2)) eb f) :
    Routine (listCode ea) eb (fun l => match l with | [] => b | a::l => f (a,l)) where
  scratch := p.scratch
  block := Block.cases 0 (Block.emit 0 (eb b)) p.block p.block
  time := p.time+C ((eb b).length+2)
  correct l := by
    let s : Store (p.scratch+1) := Function.update (fun _ => []) 0 (listCode ea l)
    cases l with
    | nil =>
      have he := Block.emit_runs (0:Fin (p.scratch+1)) (eb b) s
      have hh := Block.cases_runs_empty (0:Fin (p.scratch+1)) (Block.emit 0 (eb b))
        p.block p.block (by simp [s,listCode]) he
      refine ⟨(eb b).length+1+1,?_,?_⟩
      · simp only [eval_add,eval_C]
        omega
      · simpa [s,listCode,Function.update_idem] using hh
    | cons a l =>
      obtain ⟨t,ht,hp⟩ := p.correct (a,l)
      change p.block.Runs s (Function.update (fun _ => []) 0 (eb (f (a,l)))) t at hp
      refine ⟨t+1,?_,?_⟩
      · simp only [eval_add,eval_C,listCode] at *
        omega
      · cases ha : ea a with
        | nil => exact Block.cases_runs_true _ _ _ _ (by simp [listCode,ha,pairBits]) hp
        | cons x xs => exact Block.cases_runs_false _ _ _ _ (by simp [listCode,ha,pairBits]) hp
end Routine
namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem listCases (b : β) (f : α×List α → β) (hf : Poly f) :
    Poly (fun l => match l with | [] => b | a::l => f (a,l)) :=
  ⟨Routine.listCases encode encode b hf.routine⟩

@[fun_prop] theorem listCons : Poly (fun z : α×List α => z.1::z.2) := by
  refine ⟨(Routine.identity (encode : α×List α → List Bool)).reindex encode encode
    (fun z : α×List α => z.1::z.2) id (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem listTail : Poly (List.tail : List α → List α) := by
  exact listCases [] Prod.snd (by fun_prop)

@[fun_prop] theorem listHeadD (a : α) : Poly (fun l : List α => l.headD a) := by
  exact (listCases a Prod.fst (by fun_prop)).congr (fun l => by cases l <;> rfl)

@[fun_prop] theorem listIsEmpty : Poly (List.isEmpty : List α → Bool) := by
  exact listCases true (fun _ : α×List α => false) (by fun_prop)

@[fun_prop] theorem listAppend : Poly (fun z : List α×List α => z.1++z.2) := by
  refine ⟨Routine.append.reindex encode encode (fun z : List α×List α => z.1++z.2)
    (fun z => (encode z.1,encode z.2)) (fun _ => rfl) ?_⟩
  intro z
  exact (code_append z.1 z.2).symm

end Poly
end BinaryMatching.StackCode
end

end OAI
