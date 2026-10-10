import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperTransfer

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem initial_word (w : List Bool) :
    TypedStack.initial (processor C A) w=wordState .bootCons (tape [] w) [] [] [] := by
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem boot_run (w : List Bool) :
    UniformRun (processor C A) (TypedStack.initial (processor C A) w) (2*w.length+4)
      (wordState (.construct C.start) (tape (w.reverse.map some) [])
        (w.map digit++[digit true,sep]) [] [] [] true) := by
  rw [initial_word]
  have h₁:=uniform_step _ _ _ (step_bootCons C A (tape [] w))
  have h₂:=uniform_step _ _ _ (step_bootOne C A (tape [] w))
  have h₃:=read_run C A .bootRead .bootDrain (fun _ _ _=>rfl) [] w [digit true,sep] [] [] []
  have h₄:=buf_run C A .bootDrain (.construct C.start) true (fun _ _ _=>rfl)
    (tape (w.reverse.map some) []) (w.map digit).reverse [digit true,sep] [] []
  simp only [List.append_nil] at h₃
  simp only [List.reverse_reverse,List.length_reverse,List.length_map] at h₄
  have hh:=((h₁.trans h₂).trans h₃).trans h₄
  convert hh using 1
  omega

 theorem boot_word (w : List Bool) :
    (trList [RawBinary.value (w++[true])]).map FlatTM2.letters=
      w.map digit++[digit true,sep] := by
  simp only [trList,RawBits.trNat_bits,RawBits.bits_value,List.map_append,List.map_map,
    List.map_cons,List.map_nil]
  simp only [List.append_assoc,List.singleton_append]
  rfl

end UniformKServer.UniformWrapper

end

end OAI
