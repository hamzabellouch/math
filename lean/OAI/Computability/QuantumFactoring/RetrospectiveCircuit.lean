import Mathlib
import OAI.Computability.QuantumFactoring.SplitCandidate
import OAI.Computability.QuantumFactoring.RetrospectiveOrder

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

def stripPrimeNat (a m q v : ℕ) : ℕ :=
  if v%q=0 ∧ a^(v/q)%m=1 then v/q else v

lemma stripPrimeNat_unit {m a : ℕ} (hm : 2 ≤ m) (u : (ZMod m)ˣ)
    (ha : (a : ZMod m)=(u : ZMod m)) (q v : ℕ) :
    stripPrimeNat a m q v=stripOrderPrime u q v := by
  let : NeZero m := ⟨by omega⟩
  have he : a^(v/q)%m=1 ↔ u^(v/q)=1 := by
    rw [show a^(v/q)%m=((u^(v/q) : (ZMod m)ˣ) : ZMod m).val by
      rw [Units.val_pow_eq_pow_val,← ha,← Nat.cast_pow,ZMod.val_natCast]]
    constructor
    · intro h
      apply Units.ext
      apply ZMod.val_injective
      simpa only [Units.val_one,ZMod.val_one'' (by omega : m≠1)] using h
    · intro h
      rw [h,Units.val_one,ZMod.val_one'' (by omega : m≠1)]
  simp only [stripPrimeNat,stripOrderPrime,← Nat.dvd_iff_mod_eq_zero,he]

namespace BitArithmetic

def liftInput {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) : BooleanNetwork l w :=
  (select f).comp a

@[simp] lemma liftInput_eval {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) (x : Basis l) :
    (liftInput a f).eval x=a.eval (x∘f) := by simp [liftInput,eval_comp]

@[simp] lemma liftInput_count {k l w : ℕ} (a : BooleanNetwork k w) (f : Fin k → Fin l) :
    (liftInput a f).net.count=a.net.count := by simp [liftInput,count_comp]

def powOn {k w : ℕ} (a m e : BooleanNetwork k w) : BooleanNetwork k w :=
  ((a.pair m).pair (e.rewire Fin.rev)).comp (modularPower w w)

lemma powOn_value {k w : ℕ} (a m e : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    (bitsValue ((powOn a m e).eval x)).toNat=
      (bitsValue (a.eval x)).toNat^(bitsValue (e.eval x)).toNat%(bitsValue (m.eval x)).toNat := by
  have hh : horner ((e.rewire Fin.rev).eval x) w le_rfl=(bitsValue (e.eval x)).toNat := by
    rw [horner_full,Triangular.inputNumber_reverse]
    congr 2
    funext i
    simp [reverseBits,eval_rewire]
  rw [powOn,eval_comp,eval_pair,eval_pair,modularPower_value _ _ _ hm,hh]

lemma powOn_count {k w : ℕ} (a m e : BooleanNetwork k w) :
    (powOn a m e).net.count ≤ a.net.count+m.net.count+e.net.count+
      w+w*(3672*w*w+436*w+36) := by
  have h := modularPower_count w w
  simp only [powOn,count_comp,count_pair,count_rewire]
  omega

def stripOn {k w : ℕ} (a m q v : BooleanNetwork k w) : BooleanNetwork k w :=
  let d := (v.pair q).comp (div w)
  let cond := (equalOn ((v.pair q).comp (mod w)) (wordConstant (BitVec.ofNat w 0))).band
    (equalOn (powOn a m d) (wordConstant (BitVec.ofNat w 1)))
  wordMux cond d v

lemma stripOn_value {k w : ℕ} (a m q v : BooleanNetwork k w) (x : Basis k)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    (bitsValue ((stripOn a m q v).eval x)).toNat=stripPrimeNat
      (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
      (bitsValue (q.eval x)).toNat (bitsValue (v.eval x)).toNat := by
  have h1 : 1 < 2^w := lt_of_lt_of_le (by omega : 1 < (bitsValue (m.eval x)).toNat)
    (bitsValue (m.eval x)).isLt.le
  have hd : (bitsValue (((v.pair q).comp (div w)).eval x)).toNat=
      (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
    rw [eval_comp,eval_pair,div_word,BitVec.toNat_udiv]
  have hc : ((equalOn ((v.pair q).comp (mod w)) (wordConstant (BitVec.ofNat w 0))).band
      (equalOn (powOn a m ((v.pair q).comp (div w))) (wordConstant (BitVec.ofNat w 1)))).eval x 0=true ↔
      (bitsValue (v.eval x)).toNat%(bitsValue (q.eval x)).toNat=0 ∧
      (bitsValue (a.eval x)).toNat^((bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat)%
        (bitsValue (m.eval x)).toNat=1 := by
    rw [eval_band,Bool.and_eq_true,equalOn_value,equalOn_value,powOn_value _ _ _ _ hm,hd,
      eval_comp,eval_pair,mod_word,BitVec.toNat_umod,wordConstant_eval,wordConstant_eval,
      BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.zero_mod,Nat.mod_eq_of_lt h1]
  simp only [stripOn,wordMux_eval]
  split_ifs with hh
  · rw [hd,stripPrimeNat,ite_eq_left (hc.mp hh)]
  · rw [stripPrimeNat,ite_eq_right (fun h => hh (hc.mpr h))]

def stripStepBound (w c : ℕ) : ℕ := 9*c+4000*w^3+1500*w^2+500*w+100

lemma stripOn_count {k w c : ℕ} (a m q v : BooleanNetwork k w)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : q.net.count ≤ c) (hv : v.net.count ≤ c) :
    (stripOn a m q v).net.count ≤ stripStepBound w c := by
  have hdiv := div_count w
  have hmod := mod_count w
  have hpow := powOn_count a m ((v.pair q).comp (div w))
  have he0 := equalOn_count ((v.pair q).comp (mod w)) (wordConstant (n:=k) (BitVec.ofNat w 0))
  have he1 := equalOn_count (powOn a m ((v.pair q).comp (div w))) (wordConstant (n:=k) (BitVec.ofNat w 1))
  simp only [count_comp,count_pair,wordConstant_count] at hpow he0 he1
  simp only [stripOn,wordMux_count,count_band,count_comp,count_pair]
  dsimp [stripStepBound]
  nlinarith

/-- The original input stays read-only; the accumulator is updated once. -/
def stripUpdate {k w : ℕ} (a m q : BooleanNetwork k w) : BooleanNetwork (k+w) (k+w) :=
  (select (Fin.castAdd w)).pair (stripOn (liftInput a (Fin.castAdd w))
    (liftInput m (Fin.castAdd w)) (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k)))

lemma stripUpdate_value {k w : ℕ} (a m q : BooleanNetwork k w) (x : Basis k) (z : Basis w)
    (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    ∃ z', (stripUpdate a m q).eval (Fin.append x z)=Fin.append x z' ∧
      (bitsValue z').toNat=stripPrimeNat (bitsValue (a.eval x)).toNat (bitsValue (m.eval x)).toNat
        (bitsValue (q.eval x)).toNat (bitsValue z).toNat := by
  let v := stripOn (liftInput a (Fin.castAdd w)) (liftInput m (Fin.castAdd w))
      (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k))
  have hx : Fin.append x z ∘ Fin.castAdd w=x := by funext i; exact Fin.append_left _ _ i
  have hz : Fin.append x z ∘ Fin.natAdd k=z := by funext i; exact Fin.append_right _ _ i
  refine ⟨v.eval (Fin.append x z),?_,?_⟩
  · simp only [stripUpdate,eval_pair,eval_select,hx]
    rfl
  · have hh := stripOn_value (liftInput a (Fin.castAdd w)) (liftInput m (Fin.castAdd w))
      (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k)) (Fin.append x z)
      (by simpa only [liftInput_eval,hx] using hm)
    simpa only [liftInput_eval,eval_select,hx,hz] using hh

lemma stripUpdate_count {k w c : ℕ} (a m q : BooleanNetwork k w)
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : q.net.count ≤ c) :
    (stripUpdate a m q).net.count ≤ stripStepBound w c := by
  simp only [stripUpdate,count_pair,count_select,zero_add]
  exact stripOn_count _ _ _ _ (by simpa using ha) (by simpa using hm) (by simpa using hq) (by simp)

def stripScan {k w : ℕ} (a m : BooleanNetwork k w) : List (BooleanNetwork k w)→BooleanNetwork (k+w) (k+w)
  | [] => select id
  | q::qs => (stripUpdate a m q).comp (stripScan a m qs)

lemma stripScan_count {k w c : ℕ} (a m : BooleanNetwork k w) (qs : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hm : m.net.count ≤ c) (hq : ∀ q∈qs,q.net.count ≤ c) :
    (stripScan a m qs).net.count ≤ qs.length*stripStepBound w c := by
  induction qs with
  | nil => simp [stripScan]
  | cons q qs ih =>
    have hh := stripUpdate_count a m q ha hm (hq q (by simp))
    have ht := ih (fun r hr => hq r (by simp [hr]))
    simp only [stripScan,count_comp,List.length_cons]
    nlinarith

lemma stripScan_unit {k w m : ℕ} (hm : 2 ≤ m) (aN mN : BooleanNetwork k w)
    (u : (ZMod m)ˣ) (qs : List (BooleanNetwork k w)) (x : Basis k) (z : Basis w)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m) :
    ∃ z', (stripScan aN mN qs).eval (Fin.append x z)=Fin.append x z' ∧
      (bitsValue z').toNat=stripOrderFactors u (qs.map (fun q => (bitsValue (q.eval x)).toNat)) (bitsValue z).toNat := by
  induction qs generalizing z with
  | nil => exact ⟨z,by simp [stripScan],rfl⟩
  | cons q qs ih =>
    obtain ⟨z₁,hz₁,hv₁⟩ := stripUpdate_value aN mN q x z (by omega)
    obtain ⟨z₂,hz₂,hv₂⟩ := ih z₁
    refine ⟨z₂,?_,?_⟩
    · rw [stripScan,eval_comp,hz₁,hz₂]
    · rw [hv₂,hv₁,hmN,stripPrimeNat_unit hm u ha]
      rfl

/-- Exact order from the completed data, by explicit polynomial-size Boolean
networks of division and repeated modular squaring. -/
theorem stripScan_exact {k w m : ℕ} (hm : 2 ≤ m) (aN mN : BooleanNetwork k w)
    (u : (ZMod m)ˣ) (qs : List (BooleanNetwork k w)) (x : Basis k) (z : Basis w)
    (ha : ((bitsValue (aN.eval x)).toNat : ZMod m)=(u : ZMod m))
    (hmN : (bitsValue (mN.eval x)).toNat=m) (hz : (bitsValue z).toNat=m.totient)
    (hp : ∀ q∈qs, ((bitsValue (q.eval x)).toNat).Prime)
    (hprod : (qs.map (fun q => (bitsValue (q.eval x)).toNat)).prod=m.totient) :
    ∃ z', (stripScan aN mN qs).eval (Fin.append x z)=Fin.append x z' ∧ (bitsValue z').toNat=orderOf u := by
  obtain ⟨z',he,hv⟩ := stripScan_unit hm aN mN u qs x z ha hmN
  refine ⟨z',he,?_⟩
  rw [hv,hz]
  apply strip_totient_factors hm u _ _ hprod
  intro p hp'
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
  exact hp q hq

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
