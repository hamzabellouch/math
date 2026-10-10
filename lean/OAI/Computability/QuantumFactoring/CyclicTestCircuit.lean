import Mathlib
import OAI.Computability.QuantumFactoring.HornerEncoding
import OAI.Computability.QuantumFactoring.ArithmeticPredicates
import OAI.Computability.QuantumFactoring.CyclicPowerCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

lemma arrayConstant_decode {n s w m : ℕ} (f : Fin s → ℕ)
    (hf : ∀ i, f i < 2^w) (x : Basis n) :
    decodeCyclic m ((arrayConstant s w f).eval x)=cyclicOf (fun i => (f i : ZMod m)) := by
  ext i
  rw [decodeCyclic_coeff,arrayConstant_value,cyclicOf_coeff,Nat.mod_eq_of_lt (hf i)]

def cyclicXNet {n : ℕ} (s w : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=1 then 1 else 0)
def cyclicCNet {n : ℕ} (s w a : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=0 then a else 0)

lemma cyclicXNet_value {n s w m : ℕ} [NeZero s] (hw : 0 < w) (x : Basis n) :
    decodeCyclic m ((cyclicXNet s w).eval x)=cyclicX s := by
  have hp : 1 < 2^w := Nat.one_lt_pow (by omega) (by decide)
  unfold cyclicXNet
  rw [arrayConstant_decode _ (by intro i; split_ifs <;> omega)]
  ext i
  simp only [cyclicOf_coeff,cyclicX,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all

lemma cyclicCNet_value {n s w m a : ℕ} [NeZero s] (ha : a < 2^w) (x : Basis n) :
    decodeCyclic m ((cyclicCNet s w a).eval x)=cyclicC s (a : ZMod m) := by
  unfold cyclicCNet
  rw [arrayConstant_decode _ (by intro i; split_ifs <;> omega)]
  ext i
  simp only [cyclicOf_coeff,cyclicC,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  split_ifs <;> simp_all

def cyclicPowerOn {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) : BooleanNetwork n (s*w) :=
  ((a.pair m).pair e).comp (cyclicPower s w b)

lemma cyclicPowerOn_value {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) (x : Basis n)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicPowerOn a m e).eval x)=
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)^horner (e.eval x) b le_rfl ∧
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicPowerOn a m e).eval x) := by
  simpa only [cyclicPowerOn,eval_comp,eval_pair] using
    cyclicPower_value (a.eval x) (m.eval x) (e.eval x) hw hm

lemma cyclicPowerOn_count {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) :
    (cyclicPowerOn a m e).net.count ≤ a.net.count+m.net.count+e.net.count+
      s*w*w+b*cyclicStepBound s w := by
  have h := cyclicPower_count s w b
  simp only [cyclicPowerOn,count_comp,count_pair]
  omega

lemma horner_reverse {w : ℕ} (x : Basis w) :
    horner (x ∘ Fin.rev) w le_rfl = (bitsValue x).toNat := by
  rw [horner_full,Triangular.inputNumber_reverse]
  congr 2
  funext i
  simp [reverseBits]

/-- Literal 8s AKS congruence on s coefficient words, m in the input word. -/
def cyclicTest (s w a : ℕ) [NeZero s] : BooleanNetwork w 1 :=
  let m := select id
  let e := select Fin.rev
  let X := cyclicXNet s w
  let C := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  (lhs.pair rhs).comp (wordEq (s*w))

lemma cyclicTest_correct (s w a : ℕ) [NeZero s] (x : Basis w)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue x).toNat) (ha : a < 2^w) :
    (cyclicTest s w a).eval x 0=true ↔
      (cyclicX s+cyclicC s (a : ZMod (bitsValue x).toNat) : Cyclic (ZMod (bitsValue x).toNat) s)^
        (bitsValue x).toNat = cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
  let m : BooleanNetwork w w := select id
  let e : BooleanNetwork w w := select Fin.rev
  let X : BooleanNetwork w (s*w) := cyclicXNet s w
  let C : BooleanNetwork w (s*w) := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  have hm' : 2 ≤ (bitsValue (m.eval x)).toNat := hm
  have hl := cyclicPowerOn_value (cyclicAddNet X C m) m e x hw hm'
  have hX := cyclicPowerOn_value X m e x hw hm'
  have ha' := cyclicAddNet_correct X C m x (by omega)
  have hr := cyclicAddNet_correct (cyclicPowerOn X m e) C m x (by omega)
  have hrc := cyclicAddNet_canonical (cyclicPowerOn X m e) C m x (by omega)
  have he : horner (e.eval x) w le_rfl=(bitsValue x).toNat := horner_reverse x
  have hx : decodeCyclic (bitsValue (m.eval x)).toNat (X.eval x)=cyclicX s := cyclicXNet_value hw x
  have hc : decodeCyclic (bitsValue x).toNat (C.eval x)=cyclicC s (a : ZMod (bitsValue x).toNat) :=
    cyclicCNet_value ha x
  have hmval : m.eval x=x := by simp [m]
  rw [hmval] at hl hX ha' hr hrc hx
  have hleft : decodeCyclic (bitsValue x).toNat (lhs.eval x)=
      (cyclicX s+cyclicC s (a : ZMod (bitsValue x).toNat))^(bitsValue x).toNat := by
    change decodeCyclic (bitsValue x).toNat ((cyclicPowerOn (cyclicAddNet X C m) m e).eval x)=_
    rw [hl.1,ha',hx,hc,he]
  have hright : decodeCyclic (bitsValue x).toNat (rhs.eval x)=
      cyclicX s^(bitsValue x).toNat+cyclicC s (a : ZMod (bitsValue x).toNat) := by
    change decodeCyclic (bitsValue x).toNat ((cyclicAddNet (cyclicPowerOn X m e) C m).eval x)=_
    rw [hr,hX.1,hx,hc,he]
  change ((lhs.pair rhs).comp (wordEq (s*w))).eval x 0=true ↔ _
  rw [eval_comp,eval_pair,wordEq_eval,decide_eq_true_eq]
  rw [show bitsValue (lhs.eval x)=bitsValue (rhs.eval x) ↔ lhs.eval x=rhs.eval x from
    (bitsEquiv (s*w)).injective.eq_iff]
  constructor
  · intro h
    have hh := congrArg (decodeCyclic (bitsValue x).toNat) h
    simpa only [hleft,hright] using hh
  · intro h
    apply decodeCyclic_injective (by omega) hl.2 hrc
    change decodeCyclic (bitsValue x).toNat (lhs.eval x)=decodeCyclic (bitsValue x).toNat (rhs.eval x)
    rw [hleft,hright]
    exact h

end ExactQuantumFactoring.BitArithmetic


end

end OAI
