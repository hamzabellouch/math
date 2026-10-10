import OAI.Computability.MatchingCount.RawSize

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

structure Bits where
  data : List Bool
  deriving Inhabited
instance : Coding Bits := ⟨Bits.data⟩
@[simp] lemma encode_Bits (b : Bits) : encode b=b.data := rfl

namespace Routine
noncomputable def headBool : Routine (id : List Bool → List Bool) (fun b : Bool => [b])
    (fun l => l.headD false) where
  scratch := 0
  block := Block.cases 0 (Block.push 0 false)
    ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
  time := 2*X+3
  correct l := by
    let s : Store 1 := Function.update (fun _ => []) 0 l
    have hfalse := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) false (Function.update s 0 []))
    have htrue := Block.seq_runs _ _ (Block.clear_runs (0:Fin 1) s)
      (Block.push_runs (0:Fin 1) true (Function.update s 0 []))
    cases l with
    | nil =>
      have hh := Block.cases_runs_empty (0:Fin 1) (Block.push 0 false)
        ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
        (by simp [s]) (Block.push_runs (0:Fin 1) false s)
      exact ⟨2,by simp,by simpa [s,Function.update_idem] using hh⟩
    | cons b l =>
      cases b with
      | false =>
        have hh := Block.cases_runs_false (0:Fin 1) (Block.push 0 false)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
          (by simp [s]) hfalse
        exact ⟨2*(l.length+1)+3,by simp,by simpa [s,Function.update_idem,Nat.add_assoc] using hh⟩
      | true =>
        have hh := Block.cases_runs_true (0:Fin 1) (Block.push 0 false)
          ((Block.clear 0).seq (Block.push 0 false)) ((Block.clear 0).seq (Block.push 0 true))
          (by simp [s]) htrue
        exact ⟨2*(l.length+1)+3,by simp,by simpa [s,Function.update_idem,Nat.add_assoc] using hh⟩
end Routine

namespace Poly
@[fun_prop] theorem bitsTail : Poly (fun b : Bits => Bits.mk b.data.tail) :=
  ⟨Routine.tail.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsEmpty : Poly (fun b : Bits => b.data.isEmpty) :=
  ⟨Routine.isEmpty.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsHead : Poly (fun b : Bits => b.data.headD false) :=
  ⟨Routine.headBool.reindex encode encode _ Bits.data (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsLength : Poly (fun b : Bits => b.data.length) := Poly.codeLength
@[fun_prop] theorem bitsAppend : Poly (fun z : Bits×Bits => Bits.mk (z.1.data++z.2.data)) :=
  ⟨Routine.append.reindex encode encode _ (fun z : Bits×Bits => (z.1.data,z.2.data)) (fun _ => rfl) (fun _ => rfl)⟩
@[fun_prop] theorem bitsSingleton : Poly (fun b : Bool => Bits.mk [b]) :=
  ⟨(Routine.identity (fun b : Bool => [b])).reindex encode encode _ id (fun _ => rfl) (fun _ => rfl)⟩
end Poly

def encodeBitsStep (z : Bits×List Bool) : Bits×List Bool :=
  if z.1.data.isEmpty then z else (⟨z.1.data.tail⟩,z.2++[z.1.data.headD false])
lemma encodeBitsStep_iterate (j : ℕ) (b : Bits) (acc : List Bool) :
    encodeBitsStep^[j] (b,acc)=(⟨b.data.drop j⟩,acc++b.data.take j) := by
  induction j generalizing b acc with
  | zero => simp
  | succ j ih =>
    cases b with | mk l =>
    cases l with
    | nil => simp [Function.iterate_succ_apply,encodeBitsStep,ih]
    | cons a l => simp [Function.iterate_succ_apply,encodeBitsStep,ih,List.append_assoc]

namespace Poly
@[fun_prop] theorem bitsDecode : Poly (fun b : Bits => b.data) := by
  have ht : Poly (fun z : Bits×List Bool => Bits.mk z.1.data.tail) :=
    Poly.comp _ Prod.fst bitsTail (by fun_prop)
  have hh : Poly (fun z : Bits×List Bool => z.1.data.headD false) :=
    Poly.comp _ Prod.fst bitsHead (by fun_prop)
  have hs : Poly encodeBitsStep := by
    exact Poly.cond _ _ _ (Poly.comp _ Prod.fst bitsEmpty (by fun_prop))
      (Poly.pair _ _ ht (by fun_prop)) Poly.identity
  have hi := Poly.boundedIterate encodeBitsStep hs (5*X+1) (by
    intro z j hj
    rw [show z.2=(z.2.1,z.2.2) from rfl,encodeBitsStep_iterate]
    simp only [code_pair_length,encode_Bits,code_append,List.length_append,cut_code_length,
      List.length_drop,List.length_take,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,code_nat_length]
    omega)
  have h := Poly.second _ (Poly.comp _ (fun b : Bits => (b.data.length,(b,([]:List Bool)))) hi (by fun_prop))
  exact h.congr (fun b => by rw [encodeBitsStep_iterate]; simp)

private lemma bits_fold (l acc : List Bool) :
    l.foldl (fun b a => Bits.mk (b.data++[a])) (Bits.mk acc)=Bits.mk (acc++l) := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih => simp [ih,List.append_assoc]

@[fun_prop] theorem bitsEncode : Poly (fun l : List Bool => Bits.mk l) := by
  have hf : Poly (fun z : Bits×Bool => Bits.mk (z.1.data++[z.2])) := by
    exact Poly.comp _ (fun z : Bits×Bool => (z.1,Bits.mk [z.2])) bitsAppend (Poly.pair _ _ (by fun_prop) (Poly.comp _ Prod.snd bitsSingleton (by fun_prop)))
  have hfold := Poly.listFold false _ hf X (by
    intro z k
    rw [show z.2=Bits.mk z.2.data from rfl,bits_fold]
    have hl := list_length_le_code z.1
    simp only [encode_Bits,List.length_append,List.length_take,eval_X,code_pair_length]
    omega)
  have h := Poly.comp _ (fun l : List Bool => (l,Bits.mk [])) hfold (by fun_prop)
  exact h.congr (fun l => by rw [bits_fold]; rfl)
end Poly
end BinaryMatching.StackCode
end

end OAI
