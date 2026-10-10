import Mathlib
import OAI.Computability.QuantumFactoring.ProvidedSplits
import OAI.Computability.QuantumFactoring.NodeControlCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
namespace Primality
lemma rootSearch_lt (m e k g : ℕ) : rootSearch m e k g < g+2^k := by
  induction k generalizing g with
  | zero => simp [rootSearch]
  | succ k ih =>
    simp only [rootSearch]
    split_ifs with h
    · have hh := ih (g+2^k)
      rw [pow_succ]
      omega
    · have hh := ih g
      rw [pow_succ]
      omega
lemma boundedRoot_lt (m e n : ℕ) : boundedRoot m e n < 2^n := by
  simpa only [boundedRoot,zero_add] using rootSearch_lt m e n 0
end Primality

namespace BitArithmetic
open BooleanNetwork FactorController

def firstProperNet {k w : ℕ} (m : BooleanNetwork k w) :
    List (BooleanNetwork k w) → BooleanNetwork k w
  | [] => wordConstant 0
  | d::ds => wordMux (properOn m d) d (firstProperNet m ds)

lemma firstProperNet_value {k w : ℕ} (hw : 0<w) (m : BooleanNetwork k w)
    (ds : List (BooleanNetwork k w)) (x : Basis k) :
    (bitsValue ((firstProperNet m ds).eval x)).toNat =
      firstProper (bitsValue (m.eval x)).toNat (ds.map (fun d => (bitsValue (d.eval x)).toNat)) := by
  induction ds with
  | nil => simp [firstProperNet,firstProper,wordConstant_eval]
  | cons d ds ih =>
    rw [firstProperNet,wordMux_eval]
    simp only [properOn_value hw,List.map_cons,firstProper]
    split_ifs <;> simp_all

def evenOn {k w : ℕ} (m : BooleanNetwork k w) : BooleanNetwork k 1 :=
  zeroWord ((m.pair (wordConstant (BitVec.ofNat w 2))).comp (mod w))
lemma evenOn_value {k w : ℕ} (hw : 2≤w) (m : BooleanNetwork k w) (x : Basis k) :
    (evenOn m).eval x 0=true ↔ 2∣(bitsValue (m.eval x)).toNat := by
  have h2 : 2<2^w := (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hw)
  rw [evenOn,zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,Nat.dvd_iff_mod_eq_zero]

def candidateOn {k w : ℕ} (a m d : BooleanNetwork k w) : BooleanNetwork k w :=
  wordMux ((zeroWord d).bnot.band (evenOn d)) (splitRawOn a m d) (wordConstant 0)
lemma candidateOn_value {k w n : ℕ} (hwn : w=n+1) (hw : 2≤w)
    (a m d : BooleanNetwork k w) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((candidateOn a m d).eval x)).toNat = candidateDivisor
      (bitsValue (m.eval x)).toNat (bitsValue (a.eval x)).toNat (bitsValue (d.eval x)).toNat := by
  rw [candidateOn,wordMux_eval]
  simp only [eval_band,Bool.and_eq_true,bnot_value,zeroWord_value,evenOn_value hw]
  have hpos : ¬(bitsValue (d.eval x)).toNat=0 ↔ 0<(bitsValue (d.eval x)).toNat := by omega
  simp only [hpos,candidateDivisor]
  split_ifs
  · exact splitRawOn_value hwn hw a m d x hm hb
  · simp [wordConstant_eval]

def rootOn {k : ℕ} (n e : ℕ) (m : BooleanNetwork k (n+1)) : BooleanNetwork k (n+1) :=
  ((m.comp (resizeWord (n+1) (rootWidth n))).comp (boundedRootNet n e)).comp
    (resizeWord (rootWidth n) (n+1))
lemma rootOn_value {k n e : ℕ} (hn : 0<n) (he : e≤n)
    (m : BooleanNetwork k (n+1)) (x : Basis k) :
    (bitsValue ((rootOn n e m).eval x)).toNat=Primality.boundedRoot (bitsValue (m.eval x)).toNat e n := by
  have hw : n+1≤rootWidth n := by dsimp [rootWidth]; nlinarith
  rw [rootOn,eval_comp,resizeWord_value,BitVec.toNat_setWidth,eval_comp,
    boundedRootNet_value n e he,eval_comp,resizeWord_toNat hw]
  exact Nat.mod_eq_of_lt ((Primality.boundedRoot_lt _ _ _).trans
    (Nat.pow_lt_pow_right (by decide) (by omega)))

def rootsOn {k : ℕ} (n : ℕ) (m : BooleanNetwork k (n+1)) : BooleanNetwork k (n+1) :=
  firstProperNet m ((List.range (n+1)).map (fun e => rootOn n e m))
lemma rootsOn_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k (n+1)) (x : Basis k) :
    (bitsValue ((rootsOn n m).eval x)).toNat=rootSplit (bitsValue (m.eval x)).toNat n := by
  rw [rootsOn,firstProperNet_value (by omega),rootSplit,rootProposals,List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  exact rootOn_value hn (by have hh := List.mem_range.mp he; omega) m x

def ordersOn {k w : ℕ} (m : BooleanNetwork k w)
    (ars : List (BooleanNetwork k w × BooleanNetwork k w)) : BooleanNetwork k w :=
  firstProperNet m (ars.map (fun ar => candidateOn ar.1 m ar.2))
lemma ordersOn_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k (n+1))) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((ordersOn m ars).eval x)).toNat=orderSplit (bitsValue (m.eval x)).toNat
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  rw [ordersOn,firstProperNet_value (by omega),orderSplit,List.map_map,List.map_map]
  congr 1
  apply List.map_congr_left
  intro ar _
  exact candidateOn_value rfl (by omega) ar.1 m ar.2 x hm hb

def suppliedOn {k : ℕ} (n : ℕ) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k (n+1))) : BooleanNetwork k (n+1) :=
  wordMux (evenOn m) (wordConstant (BitVec.ofNat (n+1) 2))
    (wordMux (properOn m (rootsOn n m)) (rootsOn n m) (ordersOn m ars))

/-- The actual even/root/order implementation. No factorization information is
used in this decoder, and all loops are fixed by n and the number of slots. -/
theorem suppliedOn_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k (n+1))) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) (hb : (bitsValue (m.eval x)).toNat<2^n) :
    (bitsValue ((suppliedOn n m ars).eval x)).toNat=suppliedDivisor (bitsValue (m.eval x)).toNat n
      (ars.map (fun ar => ((bitsValue (ar.1.eval x)).toNat,(bitsValue (ar.2.eval x)).toNat))) := by
  simp only [suppliedOn,wordMux_eval,evenOn_value (by omega : 2≤n+1),
    properOn_value (by omega : 0<n+1),rootsOn_value hn,suppliedDivisor]
  split_ifs
  · rw [wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    exact (by norm_num : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  · exact rootsOn_value hn m x
  · exact ordersOn_value hn m ars x hm hb

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
