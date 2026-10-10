import Mathlib
import OAI.Computability.QuantumFactoring.LabelValidationCircuit
import OAI.Computability.QuantumFactoring.RetentionCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

inductive DecodeVar | den | num | residue | coin

private def decodeVars {k w : ℕ} (d j t c : BooleanNetwork k w) : DecodeVar → BooleanNetwork k w
  | .den => d | .num => j | .residue => t | .coin => c

def firstRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.firstE n (.var .den) (.var .num))
    (.var .coin) (decodeVars d j t c)
def secondRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.secondE n (.var .den) (.var .num) (.var .residue))
    (.var .coin) (decodeVars d j t c)
def thirdRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.lastE n (.var .den) (.var .num))
    (.var .coin) (decodeVars d j t c)

lemma firstRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat) :
    (firstRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (firstRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [firstRetNet,retentionNet_value,Expressions.firstE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) hd hp]
  rfl
lemma secondRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat)
    (ht : (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat) :
    (secondRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (discrepancyRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat
          (bitsValue (t.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [secondRetNet,retentionNet_value,Expressions.secondE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) (.var .residue) hd hp ht]
  rfl
lemma thirdRetNet_value {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) (x : Basis k)
    (hd : (bitsValue (d.eval x)).toNat≤2^n) (hp : 0<(bitsValue (d.eval x)).toNat) :
    (thirdRetNet n d j t c).eval x 0=true ↔
      (bitsValue (c.eval x)).toNat<(Int.floor (remainderRetention n
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat := by
  rw [thirdRetNet,retentionNet_value,Expressions.lastE_value (fun i => (bitsValue ((decodeVars d j t c i).eval x)).toNat) n (.var .den) (.var .num) hd hp]
  rfl

/-- Mode guards are outside the rational computations. In particular malformed
labels and residue guesses cannot turn an irrelevant retention into acceptance. -/
def trialAcceptOn {k w : ℕ} (n : ℕ) (a m mode d j t c : BooleanNetwork k w)
    (selected : BooleanNetwork k 1) : BooleanNetwork k 1 :=
  (labelValidNet n a m d j).band
    (((wordLt mode (wordConstant (BitVec.ofNat w 2))).band
      (selected.band (firstRetNet n d j t c))).bor
    (((equalOn mode (wordConstant (BitVec.ofNat w 2))).band
      ((wordLt t d).band (secondRetNet n d j t c))).bor
     ((equalOn mode (wordConstant (BitVec.ofNat w 3))).band (thirdRetNet n d j t c))))

lemma trialAcceptOn_value {k w : ℕ} (n : ℕ) (a m mode d j t c : BooleanNetwork k w)
    (selected : BooleanNetwork k 1) (hn : n<w) (hw : 2≤w) (x : Basis k)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (trialAcceptOn n a m mode d j t c selected).eval x 0=true ↔
      ValidLabel n (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat ∧
      (((bitsValue (mode.eval x)).toNat<2 ∧ selected.eval x 0=true ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (firstRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat) ∨
       ((bitsValue (mode.eval x)).toNat=2 ∧ (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (discrepancyRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat
            (bitsValue (t.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat) ∨
       ((bitsValue (mode.eval x)).toNat=3 ∧
        (bitsValue (c.eval x)).toNat<(Int.floor (remainderRetention n
          (bitsValue (d.eval x)).toNat (bitsValue (j.eval x)).toNat*(2:ℚ)^(retentionBits n))).toNat)) := by
  have h2 : 2<2^w := lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hw)
  have h3 : 3<2^w := lt_of_lt_of_le (by decide : 3<2^2) (Nat.pow_le_pow_right (by decide) hw)
  simp only [trialAcceptOn,eval_band,eval_bor,Bool.and_eq_true,Bool.or_eq_true,
    labelValidNet_value n a m d j hn x hm,wordLt_eval,decide_eq_true_eq,equalOn_value,
    wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,Nat.mod_eq_of_lt h3]
  apply and_congr_right
  intro hv
  rw [firstRetNet_value n d j t c x hv.2.1.le hv.1,
    thirdRetNet_value n d j t c x hv.2.1.le hv.1]
  by_cases ht : (bitsValue (t.eval x)).toNat<(bitsValue (d.eval x)).toNat
  · rw [secondRetNet_value n d j t c x hv.2.1.le hv.1 ht]
  · simp only [ht,false_and,and_false]

/-- At the actually recovered/guessed pair, pair equality checks simplify but
sampler scratch selection and the actual recorded retention coin do not. -/
lemma labelEvent_self {u s n : ℕ} (a m : Basis u) (r : Raw u s n) :
    labelEvent s n a m (labelPair s n r).1 (labelPair s n r).2 r ↔
      (((bitsValue r.1).toNat<2 ∧ SampleSelected a m r.2.1 ∧
        Retains (firstRetention n (labelPair s n r).1 (labelPair s n r).2) r.2.2.2.2.2) ∨
       ((bitsValue r.1).toNat=2 ∧ (bitsValue r.2.2.2.2.1).toNat<(labelPair s n r).1 ∧
        Retains (discrepancyRetention n (labelPair s n r).1 (labelPair s n r).2
          (bitsValue r.2.2.2.2.1).toNat) r.2.2.2.2.2) ∨
       ((bitsValue r.1).toNat=3 ∧
        Retains (remainderRetention n (labelPair s n r).1 (labelPair s n r).2) r.2.2.2.2.2)) := by
  by_cases h : (bitsValue r.1).toNat<2
  · have h2 : (bitsValue r.1).toNat≠2 := by omega
    have h3 : (bitsValue r.1).toNat≠3 := by omega
    simp only [labelEvent,modeFirst,modeSecond,modeThird,h,h2,h3,true_and,false_and,
      or_false,firstPass,recovered,labelPair,ite_true,Prod.mk.eta,and_true]
  · simp only [labelEvent,modeFirst,modeSecond,modeThird,h,false_and,false_or,
      labelPair,ite_false,secondPass,thirdPass,true_and]

end ExactQuantumFactoring.OrderTrial


end

end OAI
