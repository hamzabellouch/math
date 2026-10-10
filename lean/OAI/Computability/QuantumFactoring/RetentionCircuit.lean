import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionPredicates
import OAI.Computability.QuantumFactoring.ThresholdRetention
import OAI.Computability.QuantumFactoring.TrialRetentionBounds
import OAI.Computability.QuantumFactoring.ExpressionSharing

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}
lemma isOne_shared_count {k b c : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b)
    (hc : ∀ i, (vars i).net.count ≤ c) :
    (e.isOne vars).net.count ≤
      e.sharedCost*(operationBound (e.templateWidth b)+c+e.templateWidth b)+
        100*(e.templateWidth b)+21 := by
  have he := e.template_shared_count vars hc
  have hh := equalOn_count (e.template vars) (wordConstant (n:=k) (BitVec.ofNat (e.templateWidth b) 1))
  simp only [wordConstant_count] at hh
  exact hh.trans (by omega)
end NatExpr

/-- Compile the dyadic threshold to a finite Boolean network. All arithmetic,
including signed rational division and floor, is reduced to bounded word gates. -/
def retentionNet {v : Type*} {k b : ℕ} (T : ℕ) (p : RatExpr v) (coin : NatExpr v)
    (vars : v → BooleanNetwork k b) : BooleanNetwork k 1 :=
  (thresholdExpr T p coin).isOne vars
lemma retentionNet_value {v : Type*} {k b : ℕ} (T : ℕ) (p : RatExpr v) (coin : NatExpr v)
    (vars : v → BooleanNetwork k b) (x : Basis k) :
    (retentionNet T p coin vars).eval x 0=true ↔
      coin.eval (fun i => (bitsValue ((vars i).eval x)).toNat)<
        (Int.floor (p.eval (fun i => (bitsValue ((vars i).eval x)).toNat)*(2:ℚ)^T)).toNat := by
  rw [retentionNet,NatExpr.isOne_eval,thresholdExpr_eval]
lemma retentionNet_count {v : Type*} {k b c : ℕ} (T : ℕ) (p : RatExpr v) (coin : NatExpr v)
    (vars : v → BooleanNetwork k b) (hc : ∀ i, (vars i).net.count ≤ c) :
    (retentionNet T p coin vars).net.count ≤
      (thresholdExpr T p coin).sharedCost*
        (NatExpr.operationBound ((thresholdExpr T p coin).templateWidth b)+c+
          (thresholdExpr T p coin).templateWidth b)+
        100*((thresholdExpr T p coin).templateWidth b)+21 :=
  NatExpr.isOne_shared_count _ _ hc

namespace OrderTrial.Expressions
variable {v : Type*}

def firstE (n : ℕ) (d j : NatExpr v) : RatExpr v :=
  coefficientE n (.const ((2^n)^16)) (.const (2^n)) d j
def secondE (n : ℕ) (d j t : NatExpr v) : RatExpr v :=
  discrepancyE n (.const ((2^n)^16)) (.const (2^n)) d j t
def lastE (n : ℕ) (d j : NatExpr v) : RatExpr v :=
  thirdRetentionE n (.const ((2^n)^16)) (.const (2^n)) d j

lemma firstE_value (x : v→ℕ) (n : ℕ) (d j : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (firstE n d j).eval x=firstRetention n (d.eval x) (j.eval x) := by
  exact coefficientE_correct x n _ _ d j hd hpos
lemma secondE_value (x : v→ℕ) (n : ℕ) (d j t : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) (ht : t.eval x<d.eval x) :
    (secondE n d j t).eval x=discrepancyRetention n (d.eval x) (j.eval x) (t.eval x) := by
  have hQ : d.eval x≤((2^n)^16) := hd.trans
    (Nat.le_self_pow (by decide : 16≠0) (2^n))
  have h := discrepancyE_correct x n (.const ((2^n)^16)) (.const (2^n)) d j t hd hpos ht hQ
  simpa only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat,secondE,discrepancyRetention] using h
lemma lastE_value (x : v→ℕ) (n : ℕ) (d j : NatExpr v)
    (hd : d.eval x≤2^n) (hpos : 0<d.eval x) :
    (lastE n d j).eval x=remainderRetention n (d.eval x) (j.eval x) := by
  have h := thirdRetentionE_correct x n (.const ((2^n)^16)) (.const (2^n)) d j hd hpos
  simpa only [NatExpr.eval,Nat.cast_pow,Nat.cast_ofNat,lastE,remainderRetention] using h

/-- The three actual source retentions. Each net is total also at malformed
labels; the separately compiled label guard suppresses those outputs. -/
def modeRetentionNet {k b : ℕ} (n : ℕ) (mode : Fin 3) (d j t coin : NatExpr v)
    (vars : v → BooleanNetwork k b) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n)
    (if mode=0 then firstE n d j else if mode=1 then secondE n d j t else lastE n d j) coin vars

lemma modeRetentionNet_value {k b : ℕ} (n : ℕ) (mode : Fin 3) (d j t coin : NatExpr v)
    (vars : v → BooleanNetwork k b) (x : Basis k)
    (hd : d.eval (fun i => (bitsValue ((vars i).eval x)).toNat)≤2^n)
    (hpos : 0<d.eval (fun i => (bitsValue ((vars i).eval x)).toNat))
    (ht : t.eval (fun i => (bitsValue ((vars i).eval x)).toNat)<
      d.eval (fun i => (bitsValue ((vars i).eval x)).toNat)) :
    let dx := d.eval (fun i => (bitsValue ((vars i).eval x)).toNat)
    let jx := j.eval (fun i => (bitsValue ((vars i).eval x)).toNat)
    let tx := t.eval (fun i => (bitsValue ((vars i).eval x)).toNat)
    (modeRetentionNet n mode d j t coin vars).eval x 0=true ↔
      coin.eval (fun i => (bitsValue ((vars i).eval x)).toNat)<
        (Int.floor ((if mode=0 then firstRetention n dx jx else
          if mode=1 then discrepancyRetention n dx jx tx else remainderRetention n dx jx)*
            (2:ℚ)^(retentionBits n))).toNat := by
  dsimp only
  rw [modeRetentionNet,retentionNet_value]
  split_ifs <;> simp only [firstE_value _ n d j hd hpos,
    secondE_value _ n d j t hd hpos ht,lastE_value _ n d j hd hpos]
end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
