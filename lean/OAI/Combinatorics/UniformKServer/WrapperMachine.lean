import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperBoot
import OAI.Combinatorics.UniformKServer.StackCoins
import OAI.Combinatorics.UniformKServer.WrapperPrefix

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open scoped Classical
variable {Q K : Type*} [Fintype Q] [Fintype K] {g : ℕ}

def frame (s : State Q K g) (i : BitTape) (out : List Bool) : State Q K g :=
  {s with input:=i,outputRev:=out,yielded:=true}

def CoreRep (P : Processor Q K g) (s : State Q K g)
    (z : MachineState (StackCompiler.machine (compile P))) : Prop :=
  ∃i out,StackCompiler.Matches (compile P) (encode (frame s i out)) z

 theorem CoreRep.yielded {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))} (h : CoreRep P s z) : z.yielded=true := by
  obtain ⟨i,out,h⟩:=h
  exact h.yielded

 theorem matches_core {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))}
    (h : StackCompiler.Matches (compile P) (encode s) z) (hy : s.yielded=true) : CoreRep P s z := by
  refine ⟨s.input,s.outputRev,?_⟩
  have he : frame s s.input s.outputRev=s := by cases s;simp_all only [frame]
  rw [he]
  exact h

 theorem CoreRep.install {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))} (h : CoreRep P s z) (w : List Bool) :
    StackCompiler.Matches (compile P) (encode (install s w))
      ((StackCompiler.machine (compile P)).install z w) := by
  obtain ⟨i,out,h⟩:=h
  have hh:=StackCompiler.matches_install _ _ _ h w
  exact hh

 theorem matches_coins {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))}
    (h : StackCompiler.Matches (compile P) (encode s) z) (bs : List Bool) (he : Even bs.length) :
    StackCompiler.Matches (compile P) (encode (run P s (StackCompiler.alternate bs)))
      ((StackCompiler.machine (compile P)).run z bs) := by
  rw [encode_run]
  exact StackCompiler.matches_alternate _ _ _ h bs he

 theorem CoreRep.slow {P : Processor Q K g} {s t : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))} (h : CoreRep P s z) (w bs : List Bool)
    (he : Even bs.length) (hb : 2≤bs.length) (hs : SlowLink P s t) :
    CoreRep P t ((StackCompiler.machine (compile P)).run ((StackCompiler.machine (compile P)).install z w) bs) ∧
      ((StackCompiler.machine (compile P)).run ((StackCompiler.machine (compile P)).install z w) bs).outputRev=[] := by
  have hh:=matches_coins (h.install w) bs he
  rw [hs.run w _ (by rw [StackCompiler.alternate_length];omega)] at hh
  refine ⟨?_,?_⟩
  · obtain ⟨hy,ho,hl⟩:=hs
    have hc:=matches_core hh hy
    exact hc
  · exact hh.output.trans hs.2.1

end UniformKServer.TypedStack

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical

 theorem request_even (L t : ℕ) : Even (requestBudget 64 1 L t) := by
  refine ⟨32*(L+Nat.clog 2 (t+1)+1),?_⟩
  simp only [requestBudget,polynomialBudget,pow_one]
  omega
 theorem request_half (L t : ℕ) (bs : List Bool) (h : bs.length=requestBudget 64 1 L t) :
    (StackCompiler.alternate bs).length=32*(L+Nat.clog 2 (t+1)+1) := by
  rw [StackCompiler.alternate_length,h]
  simp only [requestBudget,polynomialBudget,pow_one]
  omega
 theorem request_ge (L t : ℕ) : 2≤requestBudget 64 1 L t := by
  simp only [requestBudget,polynomialBudget,pow_one];omega
 theorem process_bound (L t T d : ℕ) (hd : 2^T≤d) (ht : d≤t) :
    16*(T+1)≤32*(L+Nat.clog 2 (t+2)+1) := by
  have hp : (2:ℕ)^T<t+2:=by omega
  have hc : T≤Nat.clog 2 (t+2) := by
    exact Nat.le_of_lt ((Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).mpr hp)
  omega

 theorem bitValue_eq (w : List Bool) : bitValue w=RawBinary.value w := by
  induction w with
  | nil=>rfl
  | cons b w ih=>
    simp only [bitValue,RawBinary.value_cons,Nat.bit_val,ih]
    cases b <;> simp [Bool.toNat,Nat.add_comm]

 theorem matched_output {qc qa : ℕ} (P : TypedStack.Processor (Control qc qa) Key g)
    (s : State qc qa) (z : MachineState (StackCompiler.machine (compile P))) (j : ℕ)
    (h : StackCompiler.Matches (compile P) (encode s) z) (ho : s.outputRev=j.bits.reverse) :
    outputValue z=j := by
  rw [outputValue,h.output]
  change bitValue s.outputRev.reverse=j
  rw [ho,List.reverse_reverse,bitValue_eq,RawBinary.value_bits]

 theorem boot_core (mult : ℕ) {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) :
    CoreRep (uniform mult)
      (wordState (.construct (literalC mult).start) BitTape.blank
        ((trList [RawBinary.value (instanceCode d s++[true])]).map FlatTM2.letters) [] [] [] true)
      (boot (machine mult) 64 1 d s) := by
  let P:=uniform mult
  let w:=instanceCode d s
  have hm:=StackCompiler.matches_capped (compile P) (StackCompiler.initial (compile P) w)
    ((StackCompiler.machine (compile P)).initial w) (StackCompiler.matches_initial _ _) (32*(w.length+1))
  rw [←encode_initial,←encode_run] at hm
  have hb:=boot_run (literalC mult) literalA w
  have he:=hb.mono rfl (show 2*w.length+4≤32*(w.length+1) by omega)
    (List.replicate (32*(w.length+1)) false) (by simp)
  change TypedStack.run P (TypedStack.initial P w) (List.replicate (32*(w.length+1)) false)=_ at he
  rw [he] at hm
  have hc:=matches_core hm rfl
  obtain ⟨i,o,hc⟩:=hc
  refine ⟨i,o,?_⟩
  have hb' : 2*(32*(w.length+1))=polynomialBudget 64 1 w.length := by
    simp [polynomialBudget];omega
  rw [hb'] at hc
  simpa only [boot_word,w,boot,P,machine,frame,wordState] using hc

end UniformKServer.UniformWrapper

end

end OAI
