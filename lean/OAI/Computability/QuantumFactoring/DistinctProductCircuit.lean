import Mathlib
import OAI.Computability.QuantumFactoring.ModularMultiply
import OAI.Computability.QuantumFactoring.ArithmeticPredicates
import OAI.Computability.QuantumFactoring.BooleanFold

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
open scoped BigOperators
namespace BitArithmetic

/-- Equality is tested on runtime word values, not on network syntax. -/
def occursLater {k n : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k 1 := any (ps.map (fun q=>(p.pair q).comp (wordEq n)))

lemma occursLater_value {k n : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n))
    (x : Basis k) : (occursLater p ps).eval x 0=true ↔
      (bitsValue (p.eval x)).toNat∈ps.map (fun q=>(bitsValue (q.eval x)).toNat) := by
  simp only [occursLater,any_eval,List.mem_map,exists_exists_and_eq_and,
    eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  constructor
  · rintro ⟨q,hq,he⟩
    exact ⟨q,hq,(congrArg BitVec.toNat he).symm⟩
  · rintro ⟨q,hq,he⟩
    exact ⟨q,hq,BitVec.eq_of_toNat_eq he.symm⟩

/-- A quadratic comparison scan counts every runtime prime only once.
No sorting primitive or mathematical finset operation is used by the circuit. -/
def distinctProductNet {k n : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n) :
    List (BooleanNetwork k n)→BooleanNetwork k n
  | []=>wordConstant 1
  | p::ps=>(wordMux (occursLater p ps) (wordConstant 1) (value p)).pair
      (distinctProductNet value ps) |>.comp (mul n)

lemma distinctProductNet_value {k n : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (f : ℕ→ℕ)
    (hv : ∀ p∈ps,(bitsValue ((value p).eval x)).toNat=f (bitsValue (p.eval x)).toNat%2^n) :
    (bitsValue ((distinctProductNet value ps).eval x)).toNat=
      (∏ p∈(ps.map (fun q=>(bitsValue (q.eval x)).toNat)).toFinset,f p)%2^n := by
  induction ps with
  | nil=>simp [distinctProductNet,wordConstant_eval]
  | cons p ps ih=>
    have hp:=hv p (by simp)
    have hi:=ih (fun q hq=>hv q (by simp [hq]))
    rw [distinctProductNet,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,
      wordMux_eval,hi,List.map_cons,List.toFinset_cons]
    by_cases he : (bitsValue (p.eval x)).toNat∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)
    · rw [ite_eq_left ((occursLater_value p ps x).mpr he),wordConstant_eval,
        Finset.insert_eq_of_mem (List.mem_toFinset.mpr he),show (1 : BitVec n).toNat=1%2^n from rfl,Nat.mod_mul_mod,Nat.mul_mod_mod,one_mul]
    · rw [ite_eq_right (fun h=>he ((occursLater_value p ps x).mp h)),hp,
        Finset.prod_insert (by simpa only [List.mem_toFinset] using he),Nat.mod_mul_mod,Nat.mul_mod_mod]

lemma occursLater_count {k n c : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n))
    (hp : p.net.count≤c) (hps : ∀ q∈ps,q.net.count≤c) :
    (occursLater p ps).net.count≤ps.length*(2*c+96*n+25)+1 := by
  have hh:=any_count (ps.map (fun q=>(p.pair q).comp (wordEq n)))
    (c:=2*c+96*n+21) (by
      intro q hq
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hq
      have h:=hps b hb
      have hw:=wordEq_count n
      rw [count_comp,count_pair]
      omega)
  simpa only [occursLater,List.length_map,Nat.add_assoc] using hh

lemma distinctProductNet_count {k n c d : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n)
    (ps : List (BooleanNetwork k n))
    (hp : ∀ p∈ps,p.net.count≤c) (hv : ∀ p∈ps,(value p).net.count≤d) :
    (distinctProductNet value ps).net.count≤
      ps.length*(d+90*n*n+22*n+7+ps.length*(2*c+96*n+25))+n := by
  induction ps with
  | nil=>simp [distinctProductNet,wordConstant_count]
  | cons p ps ih=>
    have hps:=fun q hq=>hp q (List.mem_cons_of_mem p hq)
    have hvs:=fun q hq=>hv q (List.mem_cons_of_mem p hq)
    have hi:=ih hps hvs
    have ho:=occursLater_count p ps (hp p (by simp)) hps
    have hd:=hv p (by simp)
    have hm:=mul_count n
    simp only [distinctProductNet,count_comp,count_pair,wordMux_count,wordConstant_count,
      List.length_cons]
    nlinarith
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
