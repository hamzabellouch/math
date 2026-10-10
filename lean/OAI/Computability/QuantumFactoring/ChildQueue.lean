import Mathlib
import OAI.Computability.QuantumFactoring.BooleanFold
import OAI.Computability.QuantumFactoring.SplitCandidate
import OAI.Computability.QuantumFactoring.BoundedStack

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
namespace ChildQueue

def predBits {w : ℕ} (a : Basis w) : Basis w :=
  (sub w).eval (Fin.append a (fun i => (BitVec.ofNat w 1).getLsbD i.val))

/-- Children from the distinct prime fields, ignoring zero padding and 2.
Repeated labels in DIFFERENT node records are not identified. -/
def kids {w : ℕ} : List (Basis w) → List (Basis w)
  | [] => []
  | a::as => if 2<(bitsValue a).toNat ∧ a∉as then predBits a::kids as else kids as

def wordMember {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) :
    BooleanNetwork k 1 := any (as.map (fun b => (a.pair b).comp (wordEq w)))

lemma wordMember_eval {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) (x : Basis k) :
    (wordMember a as).eval x 0=true ↔ a.eval x∈as.map (fun b=>b.eval x) := by
  rw [wordMember,any_eval]
  constructor
  · rintro ⟨c,hc,ht⟩
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
    rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq] at ht
    exact List.mem_map.mpr ⟨b,hb,((bitsEquiv w).injective ht).symm⟩
  · rintro hm
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
    refine ⟨(a.pair b).comp (wordEq w),List.mem_map.mpr ⟨b,hb,rfl⟩,?_⟩
    rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq,he]


def source (k s w : ℕ) : BooleanNetwork (k+s*w) k := select (Fin.castAdd (s*w))
def queue (k s w : ℕ) : BooleanNetwork (k+s*w) (s*w) := select (Fin.natAdd k)
def liftWord {k w : ℕ} (s : ℕ) (a : BooleanNetwork k w) := (source k s w).comp a

def active {k w : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) : BooleanNetwork k 1 :=
  (wordLt (wordConstant (BitVec.ofNat w 2)) a).band (wordMember a as).bnot

def pushOne {k w : ℕ} (s : ℕ) (a : BooleanNetwork k w) (as : List (BooleanNetwork k w)) :
    BooleanNetwork (k+s*w) (k+s*w) :=
  (source k s w).pair
    (wordMux ((source k s w).comp (active a as))
      (stackPush (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w)) (queue k s w))
      (queue k s w))

/-- Tail before head: the recursive network occurs just ONCE in the syntax.
All original factor fields remain read-only while the bounded queue is updated. -/
def pushAll {k w : ℕ} (s : ℕ) : List (BooleanNetwork k w) → BooleanNetwork (k+s*w) (k+s*w)
  | [] => select id
  | a::as => (pushAll s as).comp (pushOne s a as)

lemma source_eval (k s w : ℕ) (x : Basis k) (y : Basis (s*w)) :
    (source k s w).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left _ _ _
lemma queue_eval (k s w : ℕ) (x : Basis k) (y : Basis (s*w)) :
    (queue k s w).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right _ _ _

lemma active_eval {k w : ℕ} (hw : 2 ≤ w) (a : BooleanNetwork k w)
    (as : List (BooleanNetwork k w)) (x : Basis k) :
    (active a as).eval x 0=true ↔ 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x) := by
  have hb : 2<2^w := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  simp only [active,eval_band,Bool.and_eq_true,eval_bnot,Bool.not_eq_true',wordLt_eval,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb,decide_eq_true_eq]
  have hm := wordMember_eval a as x
  cases hh : (wordMember a as).eval x 0 <;> simp_all

lemma pushOne_eval {k w : ℕ} (hw : 2 ≤ w) (s : ℕ) (a : BooleanNetwork k w)
    (as : List (BooleanNetwork k w)) (x : Basis k) (ys : List (Basis w)) :
    (pushOne s a as).eval (Fin.append x (stackEncoding s w ys))=
      Fin.append x (stackEncoding s w
        (if 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x)
          then predBits (a.eval x)::ys else ys)) := by
  have hv : ((((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w)).eval
      (Fin.append x (stackEncoding s w ys)))=predBits (a.eval x) := by
    rw [eval_comp,eval_pair,liftWord,eval_comp,source_eval]
    unfold predBits
    congr 2
    funext i
    simp [wordConstant,eval_vector,eval_constant]
  have hs := stackPush_encoding
    (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))
    (queue k s w) (Fin.append x (stackEncoding s w ys)) ys (queue_eval k s w x _)
  rw [hv] at hs
  rw [pushOne,eval_pair,source_eval,wordMux_eval,eval_comp,source_eval,hs,queue_eval]
  by_cases hc : 2<(bitsValue (a.eval x)).toNat ∧ a.eval x∉as.map (fun b=>b.eval x)
  · rw [ite_eq_left ((active_eval hw a as x).mpr hc),ite_eq_left hc]
  · rw [ite_eq_right (fun h=>hc ((active_eval hw a as x).mp h)),ite_eq_right hc]

lemma pushAll_eval {k w : ℕ} (hw : 2 ≤ w) (s : ℕ) (as : List (BooleanNetwork k w))
    (x : Basis k) (ys : List (Basis w)) :
    (pushAll s as).eval (Fin.append x (stackEncoding s w ys))=
      Fin.append x (stackEncoding s w (kids (as.map (fun a=>a.eval x))++ys)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [pushAll,eval_comp,ih,pushOne_eval hw,List.map_cons,kids]
    split_ifs <;> rfl

lemma predBits_value {w : ℕ} (hw : 1 ≤ w) (a : Basis w) (ha : 1 ≤ (bitsValue a).toNat) :
    (bitsValue (predBits a)).toNat=(bitsValue a).toNat-1 := by
  have hb : 1<2^w := Nat.one_lt_pow (by omega) (by decide)
  rw [predBits,sub_word]
  have hv : bitsValue (fun i : Fin w => (BitVec.ofNat w 1).getLsbD i.val)=BitVec.ofNat w 1 := bitsValue_bits _
  rw [hv,BitVec.toNat_sub_of_le]
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]
  · simpa only [BitVec.le_def,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb] using ha

end ChildQueue
end ExactQuantumFactoring.BitArithmetic


end

end OAI
