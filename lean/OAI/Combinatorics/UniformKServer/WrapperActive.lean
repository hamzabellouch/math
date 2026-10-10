import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperResponse
import OAI.Combinatorics.UniformKServer.WrapperMachine

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical

 theorem physical_active (mult L t n k : ℕ) (v : RawCertificate.Certificate)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (u : ℕ) (hu : u∈c.1)
    (hrc : RawProgram.randomCount (RawProgram.unpack u)=RuntimeCertificate.B k v)
    (z : MachineState (machine mult))
    (hz : CoreRep (uniform mult) (ready (RuntimeCertificate.B k v) u BitTape.blank [] true) z)
    (ht : 16*(c.2+1)≤32*(L+Nat.clog 2 (t+2)+1))
    (r : Fin n) (coins : Fin (requestBudget 64 1 L (t+1))→Bool) :
    let a:=RawBinary.value ((StackCompiler.alternate (List.ofFn coins)).take (RuntimeCertificate.B k v)++[true])
    let u':=Encodable.encode (RawProgram.next (RawProgram.unpack u) (RawFinite.requestToken r.val) a)
    let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
    CoreRep (uniform mult) (ready (RuntimeCertificate.B k v) u' BitTape.blank [] true) z' ∧
      u'∈c.1 ∧ outputValue z'=RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r.val) a ∧
      outputValue z'<k := by
  dsimp only
  let bs:=StackCompiler.alternate (List.ofFn coins)
  let b:=RuntimeCertificate.B k v
  let a:=RawBinary.value (bs.take b++[true])
  have hv:=(RuntimeCertificate.verify_iff n k v c).mp hc
  have hn:=hv.2.2 u hu
  have hs:=(hn.2 r.val r.isLt)
  have hb : bs.length=32*(L+Nat.clog 2 (t+2)+1) := by
    exact request_half L (t+1) (List.ofFn coins) (by simp only [List.length_ofFn])
  have hlen : 16*(c.2+1)≤bs.length := by omega
  have ha : a<2^(b+1) := by
    have htlen : (bs.take b).length=b:=by simp only [List.length_take];dsimp [b] at *;omega
    simpa only [List.length_append,List.length_singleton,htlen] using value_lt (bs.take b++[true])
  have hf:=hs.2 a ha
  have hm:=matches_coins (hz.install (natCode (r.val+1))) (List.ofFn coins)
    (by rw [List.length_ofFn];exact request_even L (t+1))
  have he:=response (literalC mult) b u r.val c.2 bs hlen hv.2.1 hn.1 hs.1 hrc
    (fun a ha=>(hs.2 a ha).2.2)
  change TypedStack.run (uniform mult)
    (install (ready b u BitTape.blank [] true) (natCode (r.val+1))) bs=_ at he
  rw [he] at hm
  have hmout := hm.output
  have ho : outputValue (requestStep (machine mult) 64 1 L (t+1) z r coins)=
      RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r.val) a := by
    simp only [machine,requestStep] at ⊢
    rw [outputValue,hmout]
    simp only [TypedStack.encode,ready,wordState]
    rw [List.reverse_reverse,bitValue_eq,RawBinary.value_bits]
  refine ⟨?_,hf.2.1,ho,ho.trans_lt hf.1⟩
  refine ⟨tape ((natCode (r.val+1)).reverse.map some) [],
    (RawProgram.chosen (RawProgram.unpack u) (RawFinite.requestToken r.val) a).bits.reverse,?_⟩
  simpa only [machine,requestStep,frame,ready,wordState] using hm

end UniformKServer.UniformWrapper

end

end OAI
