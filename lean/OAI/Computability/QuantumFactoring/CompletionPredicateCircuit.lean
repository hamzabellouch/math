import Mathlib
import OAI.Computability.QuantumFactoring.RetrospectiveLists
import OAI.Computability.QuantumFactoring.CompletionFilterCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion

/-- A deferred guess predicate, rather than a circuit that constructs the
canonical CRT string.  Both branches use the same retained completion coin. -/
def predicateFilter {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) : BooleanNetwork k 1 :=
  let rare:=zeroWord branch
  let ordinaryKeep:=retentionNet (coinBits W t d) (Expressions.coefficient W t s z) coin vars
  let guessKeep:=retentionNet (coinBits W t d) (Expressions.guess W t s z) coin vars
  ((rare.bnot).band (good.band ordinaryKeep)).bor
    (rare.band (guessGood.band guessKeep))

lemma predicateFilter_value {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) (x : Basis k) :
    (predicateFilter (W:=W) d s z vars branch coin good guessGood).eval x 0=true ↔
      ((bitsValue (branch.eval x)).toNat≠0 ∧ (good.eval x 0=true ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (coeff W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) ∨
      ((bitsValue (branch.eval x)).toNat=0 ∧ (guessGood.eval x 0=true ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (guessRetention W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) := by
  simp only [predicateFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    bnot_value,zeroWord_value,retentionNet_value,Expressions.coefficient_value,
    Expressions.guess_value]

/-- Exact same-history predicate semantics: this theorem does not supply or
assume an algorithm for either of the two input Boolean tests. -/
theorem predicateFilter_test {α v : Type*} {k b W t d : ℕ}
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) (x : Basis k)
    (P : α→Prop) (Q : Basis W→Prop) (r : Raw α W t d) (S Z : ℚ)
    (hbranch : branch.eval x=r.1)
    (hcoin : coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=(bitsValue r.2.2.2).toNat)
    (hgood : good.eval x 0=true ↔ P r.2.1)
    (hguess : guessGood.eval x 0=true ↔ Q r.2.2.1)
    (hs : s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=S)
    (hz : z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=Z) :
    (predicateFilter (W:=W) d s z vars branch coin good guessGood).eval x 0=true ↔
      test P Q S Z r := by
  rw [predicateFilter_value,hbranch,hcoin,hgood,hguess,hs,hz]
  rfl
end Completion
end ExactQuantumFactoring


end

end OAI
