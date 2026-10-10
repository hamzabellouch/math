import Mathlib
import OAI.Computability.QuantumFactoring.ModularPower
import OAI.Computability.QuantumFactoring.HornerEncoding
import OAI.Computability.QuantumFactoring.ArithmeticPredicates

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def equalOn {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (a.pair b).comp (wordEq w)

lemma equalOn_value {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (equalOn a b).eval x 0=true ↔ (bitsValue (a.eval x)).toNat=(bitsValue (b.eval x)).toNat := by
  rw [equalOn,eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  exact ⟨congrArg BitVec.toNat,BitVec.eq_of_toNat_eq⟩

lemma equalOn_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (equalOn a b).net.count ≤ a.net.count+b.net.count+96*w+21 := by
  simp only [equalOn,count_comp,count_pair]
  have := wordEq_count w
  omega

def constMod (w d : ℕ) : BooleanNetwork w w :=
  ((select id).pair (wordConstant (BitVec.ofNat w d))).comp (mod w)

lemma constMod_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (bitsValue ((constMod w d).eval x)).toNat=(bitsValue x).toNat%d := by
  rw [constMod,eval_comp,eval_pair,eval_select,Function.comp_id,mod_word,wordConstant_eval,
    BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hd]

lemma constMod_count (w d : ℕ) : (constMod w d).net.count ≤ 216*w*w+57*w+6 := by
  simp only [constMod,count_comp,count_pair,count_select,wordConstant_count,zero_add]
  have := mod_count w
  omega

def dividesNet (w d : ℕ) : BooleanNetwork w 1 :=
  equalOn (constMod w d) (wordConstant (BitVec.ofNat w 0))

lemma dividesNet_value (w d : ℕ) (x : Basis w) (hd : d < 2^w) :
    (dividesNet w d).eval x 0=true ↔ d ∣ (bitsValue x).toNat := by
  rw [dividesNet,equalOn_value,constMod_value _ _ _ hd,wordConstant_eval]
  simp only [BitVec.toNat_ofNat,Nat.zero_mod]
  exact Nat.dvd_iff_mod_eq_zero.symm

lemma dividesNet_count (w d : ℕ) : (dividesNet w d).net.count ≤ 216*w*w+154*w+27 := by
  have h := equalOn_count (constMod w d) (wordConstant (BitVec.ofNat w 0))
  rw [wordConstant_count] at h
  have := constMod_count w d
  change (equalOn (constMod w d) (wordConstant (BitVec.ofNat w 0))).net.count ≤ _
  omega

/-- Static modulus and exponent; exponent wiring is reversed explicitly. -/
def constPowMod (w s j : ℕ) : BooleanNetwork w w :=
  (((select id).pair (wordConstant (BitVec.ofNat w s))).pair
    ((wordConstant (BitVec.ofNat w j)).rewire Fin.rev)).comp (modularPower w w)

lemma constPowMod_value (w s j : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hjw : j < 2^w) :
    (bitsValue ((constPowMod w s j).eval x)).toNat = (bitsValue x).toNat^j%s := by
  let sb := (wordConstant (n := w) (BitVec.ofNat w s)).eval x
  let eb := ((wordConstant (n := w) (BitVec.ofNat w j)).rewire Fin.rev).eval x
  have hs' : (bitsValue sb).toNat=s := by
    simp only [sb,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hsw]
  have he : horner eb w le_rfl=j := by
    rw [horner_full,Triangular.inputNumber_reverse]
    have hh : reverseBits w eb = (wordConstant (n := w) (BitVec.ofNat w j)).eval x := by
      funext i
      simp [reverseBits,eb]
    rw [hh,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hjw]
  have hm : 2 ≤ (bitsValue sb).toNat := by omega
  simp only [constPowMod,eval_comp,eval_pair,eval_select,Function.comp_id]
  change (bitsValue ((modularPower w w).eval (Fin.append (Fin.append x sb) eb))).toNat=_
  rw [modularPower_value _ _ _ hm,he,hs']

lemma constPowMod_count (w s j : ℕ) :
    (constPowMod w s j).net.count ≤ 3*w+w*(3672*w*w+436*w+36) := by
  simp only [constPowMod,count_comp,count_pair,count_select,wordConstant_count,count_rewire,zero_add]
  have := modularPower_count w w
  omega

def powerOneNet (w s j : ℕ) : BooleanNetwork w 1 :=
  equalOn (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))

lemma powerOneNet_value (w s j : ℕ) (x : Basis w) (hs : 2 ≤ s)
    (hsw : s < 2^w) (hjw : j < 2^w) :
    (powerOneNet w s j).eval x 0=true ↔ (bitsValue x).toNat^j%s=1 := by
  rw [powerOneNet,equalOn_value,constPowMod_value _ _ _ _ hs hsw hjw,wordConstant_eval,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1 < 2^w)]

lemma powerOneNet_count (w s j : ℕ) :
    (powerOneNet w s j).net.count ≤ 100*w+21+w*(3672*w*w+436*w+36) := by
  have h := equalOn_count (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))
  rw [wordConstant_count] at h
  have := constPowMod_count w s j
  change (equalOn (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))).net.count ≤ _
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
