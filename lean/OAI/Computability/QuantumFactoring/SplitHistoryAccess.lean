import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalMachine

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

def previousNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (M.width t) :=
  (select (firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork)).comp
    (select (firstRegister (M.width t) (FixedSplit.width n) M.initWork))
def lastSplitNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (FixedSplit.width n) :=
  (select (firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork)).comp
    (select (targetRegister (M.width t) (FixedSplit.width n) M.initWork))

lemma previousNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : FixedSplit.Raw n) :
    (M.previousNet t).eval (M.encoded x (t+1) (h,r))=M.encoded x t h := by
  rw [previousNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (FixedSplit.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork) ∘
      firstRegister (M.width t) (FixedSplit.width n) M.initWork=_
  rw [packed_first,packed_first]
lemma lastSplitNet_encoded (x : Basis c) (t : ℕ) (h : Trace n t) (r : FixedSplit.Raw n) :
    (M.lastSplitNet t).eval (M.encoded x (t+1) (h,r))=
      FixedSplit.encoding (M.query.eval (M.config x t h)) r := by
  rw [lastSplitNet,eval_comp]
  change (packed M.updateWork (packed M.initWork (M.encoded x t h)
    (FixedSplit.encoding (M.query.eval (M.config x t h)) r)) (M.config x (t+1) (h,r)) ∘
    firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork) ∘
      targetRegister (M.width t) (FixedSplit.width n) M.initWork=_
  rw [packed_first,packed_targetRegister]
end SplitMachine
end ExactQuantumFactoring


end

end OAI
