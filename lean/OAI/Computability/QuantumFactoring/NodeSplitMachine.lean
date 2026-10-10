import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalSplitDecoder
import OAI.Computability.QuantumFactoring.PhysicalMachine
import OAI.Computability.QuantumFactoring.UniversalSplit
import OAI.Computability.QuantumFactoring.NodeStateCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PhysicalNode

abbrev configWidth (n s : ℕ) := NodeStateCircuit.width s (n+1)
def query (n s : ℕ) : BooleanNetwork (configWidth n s) n :=
  (NodeStateCircuit.top s (n+1)).comp (resizeWord (n+1) n)
def update (n s : ℕ) : BooleanNetwork (configWidth n s+FixedSplit.width n) (configWidth n s) :=
  ((select (Fin.castAdd (FixedSplit.width n))).pair
    ((select (Fin.natAdd (configWidth n s))).comp (FixedSplit.divisorNet n))).comp
      (NodeStateCircuit.step s (n+1))
def machine (n s : ℕ) : SplitMachine n (configWidth n s) := ⟨query n s,update n s⟩
def decoded {n : ℕ} (q : Basis n) (r : FixedSplit.Raw n) : Basis (n+1) :=
  (FixedSplit.divisorNet n).eval (FixedSplit.encoding q r)

lemma query_pack (n s : ℕ) (a : Basis (n+1)) (xs ys : List (Basis (n+1))) (b : Bool) :
    (query n s).eval (NodeStateCircuit.pack (a::xs) ys b)=
      (resizeWord (n+1) n).eval a := by
  rw [query,eval_comp,NodeStateCircuit.top_pack]
  rfl
lemma query_value {n s : ℕ} (a : Basis (n+1)) (xs ys : List (Basis (n+1))) (b : Bool)
    (ha : (bitsValue a).toNat < 2^n) :
    (bitsValue ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b))).toNat=(bitsValue a).toNat := by
  rw [query_pack,resizeWord_value,BitVec.toNat_setWidth,Nat.mod_eq_of_lt ha]
lemma decoded_value {n : ℕ} (hn : 2 ≤ n) (q : Basis n) (r : FixedSplit.Raw n)
    (hq : 2 ≤ (bitsValue q).toNat) :
    (bitsValue (decoded q r)).toNat=FixedSplit.divisor q r :=
  FixedSplit.divisorNet_value hn q r hq

lemma next_eq {n s : ℕ} (x : Basis (configWidth n s)) (r : FixedSplit.Raw n) :
    (machine n s).next x r=(NodeStateCircuit.step s (n+1)).eval
      (Fin.append x (decoded ((query n s).eval x) r)) := by
  rw [SplitMachine.next]
  change (update n s).eval _=_
  rw [update,eval_comp,eval_pair,eval_select,eval_comp,eval_select]
  apply congrArg (NodeStateCircuit.step s (n+1)).eval
  apply congrArg₂ Fin.append
  · funext i
    exact Fin.append_left _ _ i
  · change (FixedSplit.divisorNet n).eval _=(FixedSplit.divisorNet n).eval _
    apply congrArg (FixedSplit.divisorNet n).eval
    funext i
    exact Fin.append_right _ _ i

lemma next_prime {n s : ℕ} (hn : 128 ≤ n) (a : Basis (n+1)) (xs ys : List (Basis (n+1)))
    (b : Bool) (hx : xs.length ≤ s) (hp : (bitsValue a).toNat.Prime) (r : FixedSplit.Raw n) :
    (machine n s).next (NodeStateCircuit.pack (a::xs) ys b) r=
      NodeStateCircuit.pack xs (a::ys) b := by
  rw [next_eq]
  exact NodeStateCircuit.step_prime (by omega) _ _ _ _ _ hx hp

/-- A passed actual split advances the bounded node stack. Its inputs are the
runtime stack top and this very clock tick's retained raw outcome. -/
lemma next_split {n s : ℕ} (hn : 128 ≤ n) (a : Basis (n+1)) (xs ys : List (Basis (n+1)))
    (b : Bool) (hx : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) (hb : (bitsValue a).toNat < 2^n)
    (hp : ¬(bitsValue a).toNat.Prime) (r : FixedSplit.Raw n)
    (hr : UniversalSplit.passed ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) r) :
    let q := (query n s).eval (NodeStateCircuit.pack (a::xs) ys b)
    let d := decoded q r
    (machine n s).next (NodeStateCircuit.pack (a::xs) ys b) r=
      NodeStateCircuit.pack (d::(NodeCircuit.quotient s (n+1)).eval
        (NodeCircuit.pack (a::xs) d)::xs) ys b ∧
      FactorController.ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  dsimp only
  have hq := query_value (s:=s) a xs ys b hb
  have hqm : 2 ≤ (bitsValue ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b))).toNat := by
    rw [hq]
    exact ha
  have he := decoded_value (by omega : 2 ≤ n) ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) r hqm
  have hd := UniversalSplit.passed_divisor hn ((query n s).eval (NodeStateCircuit.pack (a::xs) ys b)) hqm
    (by rw [hq];exact hp) r hr
  rw [hq,←he] at hd
  refine ⟨?_,hd⟩
  rw [next_eq]
  exact NodeStateCircuit.step_split (by omega) _ _ _ _ _ hx ha hp hd

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
