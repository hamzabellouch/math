import Mathlib
import OAI.Computability.QuantumFactoring.SplitCandidate
import OAI.Computability.QuantumFactoring.ContinuedFractionPairs

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open OrderTrial

abbrev cfWidth (s k : ℕ) := s*(k+1)+1

def cfHead (w : ℕ) : BooleanNetwork (w+(w+w)) w := select (Fin.castAdd (w+w))
def cfTail (w : ℕ) : BooleanNetwork (w+(w+w)) (w+w) := select (Fin.natAdd w)
def cfP (w : ℕ) : BooleanNetwork (w+(w+w)) w := (cfTail w).comp (rootModulus w)
def cfQ (w : ℕ) : BooleanNetwork (w+(w+w)) w := (cfTail w).comp (rootGuess w)
def cfProduct (w : ℕ) : BooleanNetwork (w+(w+w)) w :=
  (((cfHead w).pair (cfP w)).comp (mul w)).pair (cfQ w) |>.comp (add w)
def cfCombine (w : ℕ) : BooleanNetwork (w+(w+w)) (w+w) :=
  let z := equalOn (cfP w) (wordConstant (BitVec.ofNat w 0))
  (wordMux z (cfHead w) (cfProduct w)).pair
    (wordMux z (wordConstant (BitVec.ofNat w 1)) (cfP w))

def convergentNet (w : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => (div w).pair (wordConstant (BitVec.ofNat w 1))
  | k+1 =>
    ((div w).pair ((rootGuess w).pair (mod w))).comp
      ((cfHead w).pair ((cfTail w).comp (convergentNet w k))) |>.comp (cfCombine w)

lemma cfHead_eval (w : ℕ) (h p q : Basis w) :
    (cfHead w).eval (Fin.append h (Fin.append p q))=h := by
  funext i
  exact Fin.append_left h (Fin.append p q) i
lemma cfTail_eval (w : ℕ) (h : Basis w) (pq : Basis (w+w)) :
    (cfTail w).eval (Fin.append h pq)=pq := by
  funext i
  exact Fin.append_right h pq i
lemma cfP_eval (w : ℕ) (h p q : Basis w) :
    (cfP w).eval (Fin.append h (Fin.append p q))=p := by
  rw [cfP,eval_comp,cfTail_eval,rootModulus_eval]
lemma cfQ_eval (w : ℕ) (h p q : Basis w) :
    (cfQ w).eval (Fin.append h (Fin.append p q))=q := by
  rw [cfQ,eval_comp,cfTail_eval,rootGuess_eval]

lemma cfProduct_value (w : ℕ) (h p q : Basis w) :
    (bitsValue ((cfProduct w).eval (Fin.append h (Fin.append p q)))).toNat=
      ((bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat)%2^w := by
  simp only [cfProduct,eval_comp,eval_pair,add_word,mul_word,cfHead_eval,cfP_eval,cfQ_eval,
    BitVec.toNat_add,BitVec.toNat_mul,Nat.mod_add_mod]

lemma cfCombine_value {w : ℕ} (hw : 0<w) (h p q : Basis w)
    (hn : (bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat<2^w) :
    ∃ u v : Basis w,
      (cfCombine w).eval (Fin.append h (Fin.append p q))=Fin.append u v ∧
      (bitsValue u).toNat=(if (bitsValue p).toNat=0 then (bitsValue h).toNat
        else (bitsValue h).toNat*(bitsValue p).toNat+(bitsValue q).toNat) ∧
      (bitsValue v).toNat=(if (bitsValue p).toNat=0 then 1 else (bitsValue p).toNat) := by
  have hc : (equalOn (cfP w) (wordConstant (BitVec.ofNat w 0))).eval
      (Fin.append h (Fin.append p q)) 0=true ↔ (bitsValue p).toNat=0 := by
    rw [equalOn_value,cfP_eval,wordConstant_eval]
    simp
  by_cases hp : (bitsValue p).toNat=0
  · refine ⟨h,(wordConstant (n:=w+(w+w)) (BitVec.ofNat w 1)).eval
      (Fin.append h (Fin.append p q)),?_,by simp [hp],?_⟩
    · rw [cfCombine,eval_pair,wordMux_eval,wordMux_eval,ite_eq_left (hc.mpr hp),ite_eq_left (hc.mpr hp),cfHead_eval]
    · simp [wordConstant_eval,hp,Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]
  · refine ⟨(cfProduct w).eval (Fin.append h (Fin.append p q)),p,?_,?_,by simp [hp]⟩
    · rw [cfCombine,eval_pair,wordMux_eval,wordMux_eval,
        ite_eq_right (fun hh => hp (hc.mp hh)),ite_eq_right (fun hh => hp (hc.mp hh)),cfP_eval]
    · rw [ite_eq_right hp,cfProduct_value,Nat.mod_eq_of_lt hn]

/-- One recursive circuit is used once per Euclidean level; no exponential
syntax duplication of earlier convergents. -/
lemma convergentNet_value {s w : ℕ} (k : ℕ) (hw : cfWidth s k ≤ w)
    (a b : Basis w) (ha : (bitsValue a).toNat<2^s) (hb : (bitsValue b).toNat<2^s) :
    ∃ p q : Basis w,
      (convergentNet w k).eval (Fin.append a b)=Fin.append p q ∧
      ((bitsValue p).toNat,(bitsValue q).toNat)=convergentPair (bitsValue a).toNat (bitsValue b).toNat k := by
  induction k generalizing a b with
  | zero =>
    refine ⟨(div w).eval (Fin.append a b),(wordConstant (n:=w+w) (BitVec.ofNat w 1)).eval
      (Fin.append a b),eval_pair _ _ _,?_⟩
    simp only [div_word,BitVec.toNat_udiv,wordConstant_eval,BitVec.toNat_ofNat,convergentPair]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by dsimp [cfWidth] at hw; omega))]
  | succ k ih =>
    let r := (mod w).eval (Fin.append a b)
    let d := (div w).eval (Fin.append a b)
    have hr : (bitsValue r).toNat=(bitsValue a).toNat%(bitsValue b).toNat := by
      
      change (bitsValue ((mod w).eval (Fin.append a b))).toNat=_
      rw [mod_word,BitVec.toNat_umod]
    have hd : (bitsValue d).toNat=(bitsValue a).toNat/(bitsValue b).toNat := by
      
      change (bitsValue ((div w).eval (Fin.append a b))).toNat=_
      rw [div_word,BitVec.toNat_udiv]
    have hwk : cfWidth s k ≤ w := by dsimp [cfWidth] at *; nlinarith
    have hrb : (bitsValue r).toNat<2^s := by rw [hr]; exact (Nat.mod_le _ _).trans_lt ha
    obtain ⟨p,q,hpq,he⟩ := ih hwk b r hb hrb
    have hep := congrArg Prod.fst he
    have heq := congrArg Prod.snd he
    simp only [hr] at hep heq
    have hn : (bitsValue d).toNat*(bitsValue p).toNat+(bitsValue q).toNat<2^w := by
      rw [hd,hep,heq]
      by_cases hp : (convergentPair (bitsValue b).toNat ((bitsValue a).toNat%(bitsValue b).toNat) k).1=0
      · rw [hp,mul_zero,zero_add]
        have hh := (convergentPair_bound hb ((Nat.mod_le (bitsValue a).toNat (bitsValue b).toNat).trans_lt ha) k).2
        exact hh.trans_le (Nat.pow_le_pow_right (by omega) hwk)
      · have hh := (convergentPair_bound ha hb (k+1)).1
        simp only [convergentPair,ite_eq_right hp] at hh
        exact hh.trans_le (Nat.pow_le_pow_right (by omega) hw)
    obtain ⟨u,v,huv,hun,hvn⟩ := cfCombine_value (by dsimp [cfWidth] at hw; omega) d p q hn
    refine ⟨u,v,?_,?_⟩
    · simp only [convergentNet,eval_comp,eval_pair,rootGuess_eval,cfTail_eval]
      change (cfCombine w).eval (Fin.append ((cfHead w).eval (Fin.append d (Fin.append b r)))
        ((convergentNet w k).eval (Fin.append b r)))=Fin.append u v
      rw [cfHead_eval,hpq,huv]
    · simp only [hun,hvn,hd,hep,heq,convergentPair]
      split_ifs <;> rfl

lemma cfProduct_count (w : ℕ) : (cfProduct w).net.count ≤ 90*w*w+100*w+12 := by
  simp only [cfProduct,count_comp,count_pair,cfHead,cfP,cfQ,cfTail,rootModulus,rootGuess,
    count_select,zero_add,add_zero]
  have := mul_count w
  have := add_count w
  omega

lemma cfCombine_count (w : ℕ) : (cfCombine w).net.count ≤ 90*w*w+400*w+100 := by
  have hc := equalOn_count (cfP w) (wordConstant (n:=w+(w+w)) (BitVec.ofNat w 0))
  simp only [cfP,cfTail,rootModulus,count_comp,count_select,wordConstant_count,zero_add] at hc
  have hp := cfProduct_count w
  simp only [cfCombine,count_pair,wordMux_count,cfHead,cfP,cfTail,rootModulus,
    count_comp,count_select,wordConstant_count]
  omega

lemma convergentNet_count (w k : ℕ) :
    (convergentNet w k).net.count ≤ (k+1)*(600*w*w+600*w+120) := by
  induction k with
  | zero =>
    simp only [convergentNet,count_pair,wordConstant_count]
    have := div_count w
    nlinarith
  | succ k ih =>
    simp only [convergentNet,count_comp,count_pair,cfHead,cfTail,rootGuess,count_select]
    have := div_count w
    have := mod_count w
    have := cfCombine_count w
    nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
