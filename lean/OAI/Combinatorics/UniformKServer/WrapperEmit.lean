import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperWords
import OAI.Combinatorics.UniformKServer.WrapperInterpreter

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem emit_step (i : BitTape) (a : Bool) (m : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .emit i (digit a::m) [] [] out) coin=
      wordState .emit i m [] [] (a::out) := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,
    Option.some.injEq,digit_ne_sep,↓reduceIte,pop,BitTape.shift,digit_eq_digit]
  apply wordState_ext <;> try rfl
  · intro k;cases k with
    | base k=>cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · cases a <;> rfl

 theorem emit_end (i : BitTape) (m : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .emit i (sep::m) [] [] out) coin=
      wordState .sample i m [] [] out true := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem emit_run (i : BitTape) (w : List Bool) (m : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState .emit i (w.map digit++sep::m) [] [] out) (w.length+1)
      (wordState .sample i m [] [] (w.reverse++out) true) := by
  induction w generalizing out with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.map_nil,List.nil_append,List.reverse_nil] using
      uniform_step _ _ _ (emit_end C A i m out)
  | cons a w ih=>
    have hs:=uniform_step _ _ _ (emit_step C A i a (w.map digit++sep::m) out)
    convert hs.trans (ih (a::out)) using 1 <;>
      simp only [List.length_cons,List.map_cons,List.reverse_cons,List.cons_append,List.append_assoc,
        List.nil_append]; omega

 theorem first_finish (u r a T : ℕ) (h : LiteralBound.finishes T u r a=true) :
    ∃t≤T,LiteralBound.finishes t u r a=true ∧
      ∀j<t,(StackCompiler.run LiteralBound.program (LiteralBound.Init u r a)
        (List.replicate j false)).yielded=false := by
  have he : ∃t,LiteralBound.finishes t u r a=true:=⟨T,h⟩
  refine ⟨Nat.find he,Nat.find_min' he h,Nat.find_spec he,?_⟩
  intro j hj
  have hn:=Nat.find_min he hj
  rw [LiteralBound.finishes_run] at hn
  cases hh:(StackCompiler.run LiteralBound.program (LiteralBound.Init u r a)
    (List.replicate j false)).yielded <;> simp_all

 theorem active_correct (u r a t : ℕ) (ht : LiteralBound.finishes t u r a=true)
    (hp : ∀j<t,(StackCompiler.run LiteralBound.program (LiteralBound.Init u r a)
      (List.replicate j false)).yielded=false) (i : BitTape) :
    UniformRun (processor C LiteralBound.program)
      (wordState (.active LiteralBound.program.start) i ((trList [u,r,a]).map FlatTM2.letters) [] []) t
      (wordState .emit i
        ((trList [RawProgram.chosen (RawProgram.unpack u) r a,
          2^RawProgram.randomCount (RawProgram.unpack u),
          Encodable.encode (RawProgram.next (RawProgram.unpack u) r a)]).map FlatTM2.letters) [] []) := by
  have hrun:=active_run C LiteralBound.program (StackPrimitive.literal_deterministic _)
    (LiteralBound.Init u r a) t hp i
  rw [literal_input] at hrun
  rw [literal_output (by rwa [←LiteralBound.finishes_run]) (LiteralBound.correct_at ht)] at hrun
  exact hrun

 theorem active_response (u r a T : ℕ) (h : LiteralBound.finishes T u r a=true) (i : BitTape) :
    ∃t≤T+(RawProgram.chosen (RawProgram.unpack u) r a).bits.length+1,
      UniformRun (processor C LiteralBound.program)
        (wordState (.active LiteralBound.program.start) i ((trList [u,r,a]).map FlatTM2.letters) [] []) t
        (wordState .sample i
          ((trList [2^RawProgram.randomCount (RawProgram.unpack u),
            Encodable.encode (RawProgram.next (RawProgram.unpack u) r a)]).map FlatTM2.letters)
          [] [] (RawProgram.chosen (RawProgram.unpack u) r a).bits.reverse true) := by
  obtain ⟨t,hT,ht,hp⟩:=first_finish u r a T h
  have hrun:=active_correct C u r a t ht hp i
  rw [encodedList (RawProgram.chosen (RawProgram.unpack u) r a)] at hrun
  have hem:=emit_run C LiteralBound.program i (RawProgram.chosen (RawProgram.unpack u) r a).bits
    ((trList [2^RawProgram.randomCount (RawProgram.unpack u),
      Encodable.encode (RawProgram.next (RawProgram.unpack u) r a)]).map FlatTM2.letters) []
  simp only [List.append_nil] at hem
  exact ⟨t+((RawProgram.chosen (RawProgram.unpack u) r a).bits.length+1),by omega,hrun.trans hem⟩

end UniformKServer.UniformWrapper

end

end OAI
