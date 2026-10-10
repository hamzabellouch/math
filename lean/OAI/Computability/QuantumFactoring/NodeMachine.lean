import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalDataLog
import OAI.Computability.QuantumFactoring.RetrospectiveStatistics
import OAI.Computability.QuantumFactoring.RetainedListRate
import OAI.Computability.QuantumFactoring.RetainedFavorableCount

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def listRateVars (t : ℕ) (m : BooleanNetwork (M.width t) n) :
    Fin 2→BooleanNetwork (M.width t) n :=
  fun i=>if i=0 then m else M.retainedFavorableCount t m

lemma retainedListRate_exact {N P d : ℕ} (hn : 2 ≤ n) (t K : ℕ)
    (m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (ho : Odd d)
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (Completion.Expressions.listRate n K).eval
      (fun i=>(bitsValue ((M.listRateVars t m i).eval (M.encoded x t r))).toNat)=
      dataListSuccess (trueData P) d n K := by
  have hv : (fun i=>(bitsValue ((M.listRateVars t m i).eval (M.encoded x t r))).toNat)=
      (fun i : Fin 2=>if i=0 then d else dataFavorable (trueData P) d n) := by
    funext i
    dsimp only [listRateVars]
    split_ifs
    · exact hm
    · exact M.retainedFavorableCount_exact hn t m x r hc hP hP0 hd hdiv ho hm
  rw [hv,Completion.Expressions.listRate_value]
  · rfl
  · rw [←hm]
    exact (bitsValue (m.eval (M.encoded x t r))).isLt.le
end NodeMachine
end ExactQuantumFactoring


end

end OAI
