import Mathlib
import OAI.Computability.QuantumFactoring.TotientAccumulator

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- A division-based totient step. Redundant prime entries do nothing. -/
def totientPair {k w : ℕ} (q v a : BooleanNetwork k w) : BooleanNetwork k (w+w) :=
  let d := (v.pair q).comp (div w)
  let cond := zeroWord ((v.pair q).comp (mod w))
  let weight := wordMux (zeroWord ((d.pair q).comp (mod w))) q
    (natSubOn q (wordConstant (BitVec.ofNat w 1)))
  (wordMux cond d v).pair (wordMux cond ((a.pair weight).comp (mul w)) a)

lemma totientPair_value {k w : ℕ} (hw : 0 < w) (q v a : BooleanNetwork k w) (x : Basis k) :
    let y := (totientPair q v a).eval x
    ((bitsValue (y ∘ Fin.castAdd w)).toNat,(bitsValue (y ∘ Fin.natAdd w)).toNat)=
      totientStepNat (2^w) (bitsValue (q.eval x)).toNat
        ((bitsValue (v.eval x)).toNat,(bitsValue (a.eval x)).toNat) := by
  have h1 : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  let d := (v.pair q).comp (div w)
  let cond := zeroWord ((v.pair q).comp (mod w))
  let weight := wordMux (zeroWord ((d.pair q).comp (mod w))) q
    (natSubOn q (wordConstant (BitVec.ofNat w 1)))
  have hd : (bitsValue (d.eval x)).toNat=(bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
    rw [show d=(v.pair q).comp (div w) from rfl,eval_comp,eval_pair,div_word,BitVec.toNat_udiv]
  have hc : cond.eval x 0=true ↔ (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat := by
    rw [show cond=zeroWord ((v.pair q).comp (mod w)) from rfl,zeroWord_value,
      eval_comp,eval_pair,mod_word,BitVec.toNat_umod,Nat.dvd_iff_mod_eq_zero]
  have hweight : (bitsValue (weight.eval x)).toNat=
      if (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat
      then (bitsValue (q.eval x)).toNat else (bitsValue (q.eval x)).toNat-1 := by
    have hh : (zeroWord ((d.pair q).comp (mod w))).eval x 0=true ↔
        (bitsValue (q.eval x)).toNat ∣ (bitsValue (v.eval x)).toNat/(bitsValue (q.eval x)).toNat := by
      rw [zeroWord_value,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,hd,Nat.dvd_iff_mod_eq_zero]
    rw [show weight=wordMux (zeroWord ((d.pair q).comp (mod w))) q
      (natSubOn q (wordConstant (BitVec.ofNat w 1))) from rfl,wordMux_eval]
    by_cases he : (zeroWord ((d.pair q).comp (mod w))).eval x 0=true
    · rw [ite_eq_left he,ite_eq_left (hh.mp he)]
    · rw [ite_eq_right he,ite_eq_right (fun h=>he (hh.mpr h)),natSubOn_value,wordConstant_eval,
        BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1]
  dsimp only
  rw [totientPair,eval_pair]
  change ((bitsValue ((Fin.append ((wordMux cond d v).eval x)
      ((wordMux cond ((a.pair weight).comp (mul w)) a).eval x)) ∘ Fin.castAdd w)).toNat,
    (bitsValue ((Fin.append ((wordMux cond d v).eval x)
      ((wordMux cond ((a.pair weight).comp (mul w)) a).eval x)) ∘ Fin.natAdd w)).toNat)=_
  have hl (l r : Basis w) : Fin.append l r ∘ Fin.castAdd w=l := by
    funext i; exact Fin.append_left _ _ i
  have hr (l r : Basis w) : Fin.append l r ∘ Fin.natAdd w=r := by
    funext i; exact Fin.append_right _ _ i
  rw [hl,hr,wordMux_eval,wordMux_eval,totientStepNat]
  by_cases he : cond.eval x 0=true
  · rw [ite_eq_left he,ite_eq_left he,ite_eq_left (hc.mp he),hd,eval_comp,eval_pair,mul_word,
      BitVec.toNat_mul,hweight]
  · rw [ite_eq_right he,ite_eq_right he,ite_eq_right (fun h=>he (hc.mpr h))]

/-- A loose but explicit uniform polynomial bound; the residual, prime and
accumulator subcircuits are evaluated a constant number of times per step. -/
def totientStepBound (w c : ℕ) : ℕ := 30*c+3000*w*w+3000*w+300

lemma totientPair_count {k w c : ℕ} (q v a : BooleanNetwork k w)
    (hq : q.net.count ≤ c) (hv : v.net.count ≤ c) (ha : a.net.count ≤ c) :
    (totientPair q v a).net.count ≤ totientStepBound w c := by
  have hd := div_count w
  have hm := mod_count w
  have hmul := mul_count w
  have hzero := zeroWord_count ((v.pair q).comp (mod w))
  have hz := zeroWord_count ((((v.pair q).comp (div w)).pair q).comp (mod w))
  have hs := natSubOn_count q (wordConstant (n:=k) (BitVec.ofNat w 1))
  simp only [count_comp,count_pair,wordConstant_count] at hzero hz hs
  simp only [totientPair,count_pair,wordMux_count,count_comp]
  dsimp only [totientStepBound]
  nlinarith

/-- Carry the input unchanged and update two finite-word accumulators. -/
def totientUpdate {k w : ℕ} (q : BooleanNetwork k w) :
    BooleanNetwork (k+(w+w)) (k+(w+w)) :=
  (select (Fin.castAdd (w+w))).pair (totientPair (liftInput q (Fin.castAdd (w+w)))
    (select (fun i=>Fin.natAdd k (Fin.castAdd w i)))
    (select (fun i=>Fin.natAdd k (Fin.natAdd w i))))

lemma totientUpdate_value {k w : ℕ} (hw : 0 < w) (q : BooleanNetwork k w)
    (x : Basis k) (s : Basis (w+w)) :
    ∃ s', (totientUpdate q).eval (Fin.append x s)=Fin.append x s' ∧
      ((bitsValue (s' ∘ Fin.castAdd w)).toNat,(bitsValue (s' ∘ Fin.natAdd w)).toNat)=
        totientStepNat (2^w) (bitsValue (q.eval x)).toNat
          ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat) := by
  have hx : Fin.append x s ∘ Fin.castAdd (w+w)=x := by funext i;exact Fin.append_left _ _ i
  let Q:=liftInput q (Fin.castAdd (w+w))
  let V : BooleanNetwork (k+(w+w)) w:=select (fun i=>Fin.natAdd k (Fin.castAdd w i))
  let A : BooleanNetwork (k+(w+w)) w:=select (fun i=>Fin.natAdd k (Fin.natAdd w i))
  have hq : Q.eval (Fin.append x s)=q.eval x := by simp only [Q,liftInput_eval,hx]
  have hv : V.eval (Fin.append x s)=s ∘ Fin.castAdd w := by
    funext i; exact Fin.append_right _ _ _
  have ha : A.eval (Fin.append x s)=s ∘ Fin.natAdd w := by
    funext i; exact Fin.append_right _ _ _
  refine ⟨(totientPair Q V A).eval (Fin.append x s),?_,?_⟩
  · simp only [totientUpdate,eval_pair,eval_select,hx]
    rfl
  · simpa only [hq,hv,ha] using totientPair_value hw Q V A (Fin.append x s)

lemma totientUpdate_count {k w c : ℕ} (q : BooleanNetwork k w) (hq : q.net.count ≤ c) :
    (totientUpdate q).net.count ≤ totientStepBound w c := by
  simp only [totientUpdate,count_pair,count_select,zero_add]
  exact totientPair_count _ _ _ (by simpa using hq) (by simp) (by simp)

def totientScanNet {k w : ℕ} : List (BooleanNetwork k w)→BooleanNetwork (k+(w+w)) (k+(w+w))
  | []=>select id
  | q::qs=>(totientUpdate q).comp (totientScanNet qs)

lemma totientScanNet_count {k w c : ℕ} (qs : List (BooleanNetwork k w))
    (hq : ∀ q∈qs,q.net.count ≤ c) :
    (totientScanNet qs).net.count ≤ qs.length*totientStepBound w c := by
  induction qs with
  | nil=>simp [totientScanNet]
  | cons q qs ih=>
    have hh:=totientUpdate_count q (hq q (List.mem_cons_self))
    have ht:=ih (fun q h=>hq q (List.mem_cons_of_mem _ h))
    simp only [totientScanNet,count_comp,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma totientScanNet_value {k w : ℕ} (hw : 0 < w) (qs : List (BooleanNetwork k w))
    (x : Basis k) (s : Basis (w+w)) :
    ∃ s', (totientScanNet qs).eval (Fin.append x s)=Fin.append x s' ∧
      ((bitsValue (s' ∘ Fin.castAdd w)).toNat,(bitsValue (s' ∘ Fin.natAdd w)).toNat)=
        totientFoldNat (2^w) (qs.map (fun q=>(bitsValue (q.eval x)).toNat))
          ((bitsValue (s ∘ Fin.castAdd w)).toNat,(bitsValue (s ∘ Fin.natAdd w)).toNat) := by
  induction qs generalizing s with
  | nil=>exact ⟨s,rfl,rfl⟩
  | cons q qs ih=>
    obtain ⟨s₁,he₁,hv₁⟩:=totientUpdate_value hw q x s
    obtain ⟨s₂,he₂,hv₂⟩:=ih s₁
    refine ⟨s₂,?_,?_⟩
    · rw [totientScanNet,eval_comp,he₁,he₂]
    · rw [List.map_cons,totientFoldNat,←hv₁]
      exact hv₂

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
