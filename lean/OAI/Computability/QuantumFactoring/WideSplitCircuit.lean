import Mathlib
import OAI.Computability.QuantumFactoring.SuppliedDivisorCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

/-- The exponent word may be the entire completion-guess width. In particular
an arbitrary rare-branch guess is NOT silently truncated to n bits. -/
def halfPowerBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  ((a.pair m).pair ((halfWord d).rewire Fin.rev)).comp (modularPower w e)
lemma halfPowerBits_value {k w e : ℕ} (he : 2≤e) (a m : BooleanNetwork k w)
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((halfPowerBits a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%(bitsValue (m.eval x)).toNat := by
  have hh : horner (((halfWord d).rewire Fin.rev).eval x) e le_rfl=(bitsValue (d.eval x)).toNat/2 := by
    rw [horner_full,Triangular.inputNumber_reverse]
    have hr : reverseBits e (((halfWord d).rewire Fin.rev).eval x)=(halfWord d).eval x := by
      funext i
      simp [reverseBits,eval_rewire]
    rw [hr,halfWord_value he]
  rw [halfPowerBits,eval_comp,eval_pair,eval_pair,modularPower_value _ _ _ hm,hh]

def shiftedHalfBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  ((((halfPowerBits a m d).pair m).comp (add w)).pair
    (wordConstant (BitVec.ofNat w 1))).comp (sub w)
lemma shiftedHalfBits_value {k n e : ℕ} (he : 2≤e) (a m : BooleanNetwork k (n+1))
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((shiftedHalfBits a m d).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
        (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat-1 := by
  have hp := Nat.mod_lt ((bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2))
    (by omega : 0<(bitsValue (m.eval x)).toNat)
  have hsum : (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
      (bitsValue (m.eval x)).toNat+(bitsValue (m.eval x)).toNat<2^(n+1) := by
    rw [pow_succ]; omega
  have h1 : 1<2^(n+1) := Nat.one_lt_two_pow (by omega)
  rw [shiftedHalfBits,eval_comp,eval_pair,sub_word,eval_comp,eval_pair,add_word,
    wordConstant_eval,BitVec.toNat_sub,BitVec.toNat_add,halfPowerBits_value he _ _ _ _ hm,
    Nat.mod_eq_of_lt hsum,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  let v := (bitsValue (a.eval x)).toNat^((bitsValue (d.eval x)).toNat/2)%
    (bitsValue (m.eval x)).toNat
  let M := (bitsValue (m.eval x)).toNat
  change (2^(n+1)-1+(v+M))%2^(n+1)=v+M-1
  have hh : 2^(n+1)-1+(v+M)=2^(n+1)+(v+M-1) := by dsimp [v,M];omega
  rw [hh,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by dsimp [v,M];omega)]

def candidateBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  wordMux ((zeroWord d).bnot.band (evenOn d))
    (((shiftedHalfBits a m d).pair m).comp (gcdNet w)) (wordConstant 0)
lemma candidateBits_value {k n e : ℕ} (he : 2≤e) (a m : BooleanNetwork k (n+1))
    (d : BooleanNetwork k e) (x : Basis k) (hm : 2≤(bitsValue (m.eval x)).toNat)
    (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((candidateBits a m d).eval x)).toNat=candidateDivisor
      (bitsValue (m.eval x)).toNat (bitsValue (a.eval x)).toNat (bitsValue (d.eval x)).toNat := by
  have hpos : ¬(bitsValue (d.eval x)).toNat=0 ↔ 0<(bitsValue (d.eval x)).toNat := by omega
  simp only [candidateBits,wordMux_eval,eval_band,Bool.and_eq_true,bnot_value,
    zeroWord_value,evenOn_value he,hpos,candidateDivisor]
  split_ifs
  · rw [eval_comp,eval_pair,gcdNet_value,shiftedHalfBits_value he _ _ _ _ hm hb]
  · simp [wordConstant_eval]

def ordersBits {k w e : ℕ} (m : BooleanNetwork k w)
    (ars : List (BooleanNetwork k w × BooleanNetwork k e)) : BooleanNetwork k w :=
  firstProperNet m (ars.map (fun ar => candidateBits ar.1 m ar.2))
lemma ordersBits_value {k n e : ℕ} (he : 2≤e) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((ordersBits m ars).eval x)).toNat=orderSplit (bitsValue (m.eval x)).toNat
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  rw [ordersBits,firstProperNet_value (by omega),orderSplit,List.map_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro ar _
  exact candidateBits_value he ar.1 m ar.2 x hm hb

def suppliedBits {k e : ℕ} (n : ℕ) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) : BooleanNetwork k (n+1) :=
  wordMux (evenOn m) (wordConstant (BitVec.ofNat (n+1) 2))
    (wordMux (properOn m (rootsOn n m)) (rootsOn n m) (ordersBits m ars))
theorem suppliedBits_value {k n e : ℕ} (hn : 0<n) (he : 2≤e) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((suppliedBits n m ars).eval x)).toNat=suppliedDivisor (bitsValue (m.eval x)).toNat n
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  simp only [suppliedBits,wordMux_eval,evenOn_value (by omega : 2≤n+1),
    properOn_value (by omega : 0<n+1),rootsOn_value hn,suppliedDivisor]
  split_ifs
  · rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    exact (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact rootsOn_value hn m x
  · exact ordersBits_value he m ars x hm hb

end ExactQuantumFactoring.BitArithmetic


end

end OAI
