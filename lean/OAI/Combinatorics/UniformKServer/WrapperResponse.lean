import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperPrepare
import OAI.Combinatorics.UniformKServer.WrapperEmit

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)

 theorem value_lt (w : List Bool) : RawBinary.value w<2^w.length := by
  induction w with
  | nil=>simp [RawBinary.value]
  | cons b w ih=>
    rw [RawBinary.value_cons,Nat.bit_val,List.length_cons,pow_succ]
    cases b <;> simp only [Bool.toNat,Bool.cond_false,Bool.cond_true] <;> omega

def ready (b u : ℕ) (i : BitTape) (out : List Bool:=[]) (y : Bool:=false) :
    State qc (Fintype.card (FlatTM2.Local tr (LiteralPartrec.supp LiteralVector.activeCode))) :=
  wordState .sample i ((trList [2^b,u]).map FlatTM2.letters) [] [] out y

 theorem sample_ready (b u : ℕ) (w bs : List Bool) (hb : bs.length=b) :
    TypedStack.run (processor C LiteralBound.program) (ready b u (BitTape.ofWord w)) bs=
      wordState .sample (BitTape.ofWord w)
        (digit true::sep::(u.bits.map digit++[sep])) [] (bs.map digit).reverse := by
  unfold ready
  rw [encodedList,encodedList,pow_bits,List.map_append,List.map_replicate,List.map_singleton]
  simp only [List.append_assoc,List.singleton_append,trList,List.map_nil]
  rw [←hb,sample_run]
  simp only [List.append_nil]

 theorem response_fixed (b u r a T : ℕ) (w bs : List Bool)
    (hb : bs.length=b) (hr : r=RawBinary.value (w++[true]))
    (ha : a=RawBinary.value (bs++[true])) (hc : RawProgram.randomCount (RawProgram.unpack u)=b)
    (hf : LiteralBound.finishes T u r a=true) :
    ∃t≤2*u.bits.length+2*w.length+b+12+T+(RawProgram.chosen (RawProgram.unpack u) r a).bits.length+1,
      UniformRun (processor C LiteralBound.program)
        (TypedStack.run (processor C LiteralBound.program) (ready b u (BitTape.ofWord w)) bs) t
        (ready b (Encodable.encode (RawProgram.next (RawProgram.unpack u) r a))
          (tape (w.reverse.map some) []) (RawProgram.chosen (RawProgram.unpack u) r a).bits.reverse true) := by
  obtain ⟨t,ht,hs⟩:=active_response C u r a T hf (tape (w.reverse.map some) [])
  have hp:=prepare C LiteralBound.program u w bs
  rw [←hr,←ha,hb] at hp
  rw [hc] at hs
  refine ⟨(2*u.bits.length+2*w.length+b+12)+t,by omega,?_⟩
  rw [sample_ready C b u w bs hb]
  exact hp.trans hs

 theorem response (b u r T : ℕ) (bs : List Bool)
    (hlen : 16*(T+1)≤bs.length) (hb : b+1≤T)
    (hu : u.bits.length+1≤T) (hw : (natCode (r+1)).length+1≤T)
    (hc : RawProgram.randomCount (RawProgram.unpack u)=b)
    (hf : ∀a<2^(b+1), (RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r) a).bits.length≤T ∧
      LiteralBound.finishes T u (RawFinite.requestToken r) a=true) :
    TypedStack.run (processor C LiteralBound.program) (ready b u (BitTape.ofWord (natCode (r+1)))) bs=
      ready b (Encodable.encode (RawProgram.next (RawProgram.unpack u) (RawFinite.requestToken r)
        (RawBinary.value (bs.take b++[true]))))
        (tape ((natCode (r+1)).reverse.map some) [])
        (RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r)
          (RawBinary.value (bs.take b++[true]))).bits.reverse true := by
  have htake : (bs.take b).length=b:=by simp only [List.length_take];omega
  have ha : RawBinary.value (bs.take b++[true])<2^(b+1):=by
    simpa only [List.length_append,List.length_singleton,htake] using value_lt (bs.take b++[true])
  obtain ⟨t,ht,hs⟩:=response_fixed C b u (RawFinite.requestToken r)
    (RawBinary.value (bs.take b++[true])) T (natCode (r+1)) (bs.take b) htake rfl rfl hc (hf _ ha).2
  have hbnd : t≤(bs.drop b).length:=by
    have hj:=(hf _ ha).1
    simp only [List.length_drop]
    omega
  conv_lhs => rw [←List.take_append_drop b bs,TypedStack.run_append]
  exact hs.mono rfl hbnd _ rfl

end UniformKServer.UniformWrapper

end

end OAI
