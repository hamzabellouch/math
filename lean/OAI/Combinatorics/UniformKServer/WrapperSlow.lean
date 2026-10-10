import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperMachine

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

 theorem slow_request {n k : ℕ} (mult L t : ℕ) (hk : 0<k)
    (a b : State _ _)
    (h : SlowLink (uniform mult) a b) (z : MachineState (machine mult))
    (hz : CoreRep (uniform mult) a z) (r : Fin n)
    (coins : Fin (requestBudget 64 1 L (t+1))→Bool) :
    let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
    CoreRep (uniform mult) b z' ∧ selectedLabel hk z'=⟨0,hk⟩ ∧
      z'.yielded=true ∧ outputValue z'<k := by
  dsimp only
  have hh:=hz.slow (natCode (r.val+1)) (List.ofFn coins)
    (by simpa only [List.length_ofFn] using request_even L (t+1))
    (by simpa only [List.length_ofFn] using request_ge L (t+1)) h
  have ho : outputValue (requestStep (machine mult) 64 1 L (t+1) z r coins)=0 := by
    have hout : (requestStep (machine mult) 64 1 L (t+1) z r coins).outputRev=[] := hh.2
    simp only [outputValue,hout,List.reverse_nil,bitValue]
  refine ⟨hh.1,?_,hh.1.yielded,by omega⟩
  apply Fin.ext
  simp only [selectedLabel,ho,Nat.zero_mod]

end UniformKServer.UniformWrapper

end

end OAI
