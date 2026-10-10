import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperTransfer
import OAI.Combinatorics.UniformKServer.WrapperWords

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem prepare (u : ℕ) (w bs : List Bool) :
    UniformRun (processor C A)
      (wordState .sample (BitTape.ofWord w)
        (digit true::sep::(u.bits.map digit++[sep])) [] (bs.map digit).reverse)
      (2*u.bits.length+2*w.length+bs.length+12)
      (wordState (.active A.start) (tape (w.reverse.map some) [])
        ((trList [u,RawBinary.value (w++[true]),RawBinary.value (bs++[true])]).map FlatTM2.letters) [] []) := by
  let i:=BitTape.ofWord w
  let j:=tape (w.reverse.map some) []
  let p:=(u.bits.map digit).reverse
  let b:=(bs.map digit).reverse
  have h₀:=uniform_step _ _ _ (sample_end C A i (sep::(u.bits.map digit++[sep])) [] b [])
  have h₁:=uniform_step _ _ _ (pop_main C A .sampleSep .savePayload false (by intros;rfl)
    i sep (u.bits.map digit++[sep]) [] b [])
  have h₂:=save_run C A i u.bits [] b []
  simp only [List.append_nil] at h₂
  have h₃:=uniform_step _ _ _ (push_main C A .randomCons .randomOne sep (by intros;rfl) i [] p b [])
  have h₄:=uniform_step _ _ _ (push_main C A .randomOne .randomDrain (digit true) (by intros;rfl)
    i [sep] p b [])
  have h₅:=buf_run C A .randomDrain .requestCons false (by intros;rfl) i b [digit true,sep] p []
  simp only [b,List.reverse_reverse,List.length_reverse,List.length_map] at h₅
  have h₆:=uniform_step _ _ _ (push_main C A .requestCons .requestRead sep (by intros;rfl)
    i (bs.map digit++[digit true,sep]) p [] [])
  have h₇:=read_run C A .requestRead .requestOne (by intros;rfl) [] w
    (sep::(bs.map digit++[digit true,sep])) p [] []
  simp only [List.append_nil,←ofWord_tape] at h₇
  have h₈:=uniform_step _ _ _ (push_main C A .requestOne .requestDrain (digit true) (by intros;rfl)
    j (sep::(bs.map digit++[digit true,sep])) p (w.map digit).reverse [])
  have h₉:=buf_run C A .requestDrain .payloadCons false (by intros;rfl) j (w.map digit).reverse
    (digit true::sep::(bs.map digit++[digit true,sep])) p []
  simp only [List.reverse_reverse,List.length_reverse,List.length_map] at h₉
  have h₁₀:=uniform_step _ _ _ (push_main C A .payloadCons .payloadDrain sep (by intros;rfl) j
    (w.map digit++digit true::sep::(bs.map digit++[digit true,sep])) p [] [])
  have h₁₁:=pay_run C A .payloadDrain (.active A.start) (by intros;rfl) j p
    (sep::(w.map digit++digit true::sep::(bs.map digit++[digit true,sep]))) [] []
  simp only [p,List.reverse_reverse,List.length_reverse,List.length_map] at h₁₁
  have h:=(((((((((((h₀.trans h₁).trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈).trans h₉).trans h₁₀).trans h₁₁)
  convert h using 1
  · omega
  · simp only [trList,List.map_append,List.map_cons,encodedNat,RawBits.bits_value,
      List.append_assoc,List.cons_append,List.nil_append,List.map_nil,j]

end UniformKServer.UniformWrapper

end

end OAI
