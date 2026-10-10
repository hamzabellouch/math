import Mathlib
import OAI.Computability.QuantumFactoring.GcdCircuit
import OAI.Computability.QuantumFactoring.FactorSplitting

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

def candidateDivisor (m a d : ℕ) : ℕ :=
  if 0 < d ∧ 2 ∣ d then Nat.gcd (a^(d/2)%m+m-1) m else 0

lemma halfOrderResidue_nat {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) :
    halfOrderResidue u=a^(orderOf u/2)%m := by
  let : NeZero m := ⟨by omega⟩
  simp only [halfOrderResidue,Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]

lemma candidateDivisor_trueOrder {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (heven : 2 ∣ orderOf u) :
    candidateDivisor m a (orderOf u)=splitGcd u := by
  let : NeZero m := ⟨by omega⟩
  rw [candidateDivisor,ite_eq_left ⟨orderOf_pos u,heven⟩,splitGcd,halfOrderResidue_nat hm u ha]

namespace BitArithmetic

def halfWord {k w : ℕ} (d : BooleanNetwork k w) : BooleanNetwork k w :=
  (d.pair (wordConstant (BitVec.ofNat w 2))).comp (div w)

lemma div_word (w : ℕ) (a b : Basis w) :
    bitsValue ((div w).eval (Fin.append a b))=bitsValue a/bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((div w).eval (Fin.append a b))).getLsbD i =
    (div w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    div_correct,leftWord_append,rightWord_append]

lemma sub_word (w : ℕ) (a b : Basis w) :
    bitsValue ((sub w).eval (Fin.append a b))=bitsValue a-bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((sub w).eval (Fin.append a b))).getLsbD i =
    (sub w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    sub_correct,leftWord_append,rightWord_append]

lemma halfWord_value {k w : ℕ} (hw : 2 ≤ w) (d : BooleanNetwork k w) (x : Basis k) :
    (bitsValue ((halfWord d).eval x)).toNat=(bitsValue (d.eval x)).toNat/2 := by
  have h2 : 2 < 2^w := (by norm_num : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [halfWord,eval_comp,eval_pair,div_word,wordConstant_eval,BitVec.toNat_udiv,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2]

/-- The repeated-squaring exponent is wired most-significant bit first. -/
def halfPower {k w : ℕ} (a m d : BooleanNetwork k w) : BooleanNetwork k w :=
  ((a.pair m).pair ((halfWord d).rewire Fin.rev)).comp (modularPower w w)

lemma halfPower_value {k w : ℕ} (hw : 2 ≤ w) (a m d : BooleanNetwork k w)
    (x : Basis k) (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    (bitsValue ((halfPower a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%(bitsValue (m.eval x)).toNat := by
  let eb := ((halfWord d).rewire Fin.rev).eval x
  have he : horner eb w le_rfl=(bitsValue (d.eval x)).toNat/2 := by
    rw [horner_full,Triangular.inputNumber_reverse]
    have hh : reverseBits w eb=(halfWord d).eval x := by
      funext i
      simp [reverseBits,eb,eval_rewire]
    rw [hh,halfWord_value hw]
  rw [halfPower,eval_comp,eval_pair,eval_pair,modularPower_value _ _ _ hm,he]

def shiftedHalfPower {k w : ℕ} (a m d : BooleanNetwork k w) : BooleanNetwork k w :=
  ((((halfPower a m d).pair m).comp (add w)).pair
    (wordConstant (BitVec.ofNat w 1))).comp (sub w)

lemma shiftedHalfPower_value {k w n : ℕ} (hwn : w=n+1) (hw : 2 ≤ w)
    (a m d : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) (hmb : (bitsValue (m.eval x)).toNat < 2^n) :
    (bitsValue ((shiftedHalfPower a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
        (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat-1 := by
  have hp := Nat.mod_lt ((bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)) (by omega : 0 < (bitsValue (m.eval x)).toNat)
  have hsum : (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
      (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat < 2^w := by
    have he : 2^w=2^n*2 := by rw [hwn,pow_succ]
    rw [he]
    omega
  have h1 : 1 < 2^w := Nat.one_lt_two_pow (by omega)
  rw [shiftedHalfPower,eval_comp,eval_pair,sub_word,eval_comp,eval_pair,add_word,
    wordConstant_eval,BitVec.toNat_sub,BitVec.toNat_add,halfPower_value hw _ _ _ _ hm,
    Nat.mod_eq_of_lt hsum,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  let v := (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
    (bitsValue (m.eval x)).toNat
  let M := (bitsValue (m.eval x)).toNat
  change (2^w-1+(v+M))%2^w=v+M-1
  have he : 2^w-1+(v+M)=2^w+(v+M-1) := by dsimp [v,M]; omega
  rw [he,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by dsimp [v,M]; omega)]

def splitRawOn {k w : ℕ} (a m d : BooleanNetwork k w) : BooleanNetwork k w :=
  ((shiftedHalfPower a m d).pair m).comp (gcdNet w)

lemma splitRawOn_value {k w n : ℕ} (hwn : w=n+1) (hw : 2 ≤ w)
    (a m d : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) (hmb : (bitsValue (m.eval x)).toNat < 2^n) :
    (bitsValue ((splitRawOn a m d).eval x)).toNat=
      Nat.gcd ((bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
        (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat-1) (bitsValue (m.eval x)).toNat := by
  rw [splitRawOn,eval_comp,eval_pair,gcdNet_value,shiftedHalfPower_value hwn hw _ _ _ _ hm hmb]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
