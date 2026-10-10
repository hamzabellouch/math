import Mathlib
import OAI.Computability.QuantumFactoring.DyadicCompletion
import OAI.Computability.QuantumFactoring.RetentionCircuit

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
namespace Expressions
variable {v : Type*}

def ordinaryMass (t : ℕ) (s : RatExpr v) : RatExpr v :=
  (RatExpr.const (1-1/(2:ℚ)^t)).mul s

def coefficient (W t : ℕ) (s z : RatExpr v) : RatExpr v :=
  (RatExpr.ofInt (((RatExpr.const ((2:ℚ)^(W+t+2))).mul
    (z.div (ordinaryMass t s))).floor)).div (RatExpr.const ((2:ℚ)^(W+t+2)))

def guess (W t : ℕ) (s z : RatExpr v) : RatExpr v :=
  ((z.sub ((coefficient W t s z).mul (ordinaryMass t s))).mul
    (RatExpr.const ((2:ℚ)^W))).div (RatExpr.const (1/(2:ℚ)^t))

lemma ordinaryMass_value (x : v→ℕ) (t : ℕ) (s : RatExpr v) :
    (ordinaryMass t s).eval x=(1-1/(2:ℚ)^t)*s.eval x := by
  simp only [ordinaryMass,RatExpr.eval_mul,RatExpr.eval_const]
lemma coefficient_value (x : v→ℕ) (W t : ℕ) (s z : RatExpr v) :
    (coefficient W t s z).eval x=coeff W t (s.eval x) (z.eval x) := by
  simp only [coefficient,RatExpr.eval_div,RatExpr.eval_ofInt,RatExpr.eval_floor,
    RatExpr.eval_mul,RatExpr.eval_const,ordinaryMass_value,coeff,Exactness.completionCoeff]
lemma guess_value (x : v→ℕ) (W t : ℕ) (s z : RatExpr v) :
    (guess W t s z).eval x=guessRetention W t (s.eval x) (z.eval x) := by
  simp only [guess,RatExpr.eval_div,RatExpr.eval_mul,RatExpr.eval_sub,
    RatExpr.eval_const,coefficient_value,ordinaryMass_value,
    guessRetention,Exactness.completionRemainder,coeff]

end Expressions

/-- Literal deferred completion filter on retained registers. The input s and
canonical-output circuits are to be computed from the verified full log; this
compiler does not smuggle those quantities into the preparation. -/
def filterNet {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (guess canonical : BooleanNetwork k W)
    (coin : NatExpr v) (good : BooleanNetwork k 1) : BooleanNetwork k 1 :=
  let rare:=zeroWord branch
  let ordinaryKeep:=retentionNet (coinBits W t d) (Expressions.coefficient W t s z) coin vars
  let guessKeep:=retentionNet (coinBits W t d) (Expressions.guess W t s z) coin vars
  ((rare.bnot).band (good.band ordinaryKeep)).bor
    (rare.band ((equalOn guess canonical).band guessKeep))

lemma filterNet_value {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (guess canonical : BooleanNetwork k W)
    (coin : NatExpr v) (good : BooleanNetwork k 1) (x : Basis k) :
    (filterNet d s z vars branch guess canonical coin good).eval x 0=true ↔
      ((bitsValue (branch.eval x)).toNat≠0 ∧ (good.eval x 0=true ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (coeff W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) ∨
      ((bitsValue (branch.eval x)).toNat=0 ∧ (guess.eval x=canonical.eval x ∧
        coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)<
          (Int.floor (guessRetention W t (s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))
            (z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat))*(2:ℚ)^(coinBits W t d))).toNat)) := by
  have he : (bitsValue (guess.eval x)).toNat=(bitsValue (canonical.eval x)).toNat ↔
      guess.eval x=canonical.eval x := by
    constructor
    · intro h
      exact (bitsEquiv W).injective (BitVec.eq_of_toNat_eq h)
    · intro h; rw [h]
  simp only [filterNet,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    bnot_value,zeroWord_value,retentionNet_value,Expressions.coefficient_value,
    equalOn_value,Expressions.guess_value,he]


/-- On the very same retained record, the gate flag is exactly the §6 event. -/
theorem filterNet_passed {α v : Type*} {k b W t d : ℕ}
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (guess canonical : BooleanNetwork k W)
    (coin : NatExpr v) (good : BooleanNetwork k 1) (P : α→Prop)
    (x : Basis k) (r : Raw α W t d) (y₀ : Basis W) (S Z : ℚ)
    (hbranch : branch.eval x=r.1) (hguess : guess.eval x=r.2.2.1)
    (hcanonical : canonical.eval x=y₀)
    (hcoin : coin.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=(bitsValue r.2.2.2).toNat)
    (hgood : good.eval x 0=true ↔ P r.2.1)
    (hs : s.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=S)
    (hz : z.eval (fun i=>(bitsValue ((vars i).eval x)).toNat)=Z) :
    (filterNet d s z vars branch guess canonical coin good).eval x 0=true ↔ passed P y₀ S Z r := by
  rw [filterNet_value,hbranch,hguess,hcanonical,hcoin,hgood,hs,hz]
  rfl
end Completion
end ExactQuantumFactoring


end

end OAI
