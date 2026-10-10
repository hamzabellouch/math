import Mathlib
import OAI.Computability.QuantumFactoring.RawTrialDecoder
import OAI.Computability.QuantumFactoring.MinimumCandidateCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial

lemma resizeWord_eq_natBasis {u w : ℕ} (x : Basis u) :
    (resizeWord u w).eval x=natBasis w (bitsValue x).toNat := by
  apply (bitsEquiv w).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue ((resizeWord u w).eval x)).toNat = (bitsValue (natBasis w (bitsValue x).toNat)).toNat
  rw [resizeWord_value,BitVec.toNat_setWidth,natBasis_value]

namespace OrderSlots

def usableOn {k n : ℕ} (a m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (wordLt a m).band (equalOn ((a.pair m).comp (gcdNet n)) (wordConstant (BitVec.ofNat n 1)))
lemma usableOn_value {k n : ℕ} (a m : BooleanNetwork k n) (x : Basis k) (hn : 1≤n) :
    (usableOn a m).eval x 0=true ↔ Usable (a.eval x) (m.eval x) := by
  have h1 : 1<2^n := Nat.one_lt_two_pow (by omega)
  simp only [usableOn,eval_band,Bool.and_eq_true,wordLt_eval,decide_eq_true_eq,equalOn_value,
    eval_comp,eval_pair,gcdNet_value,wordConstant_eval,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,
    Usable,ZMod.isUnit_iff_coprime,Nat.Coprime]
lemma usableOn_count {k n : ℕ} (a m : BooleanNetwork k n) :
    (usableOn a m).net.count≤2*a.net.count+2*m.net.count+
      2*n*(216*n*n+300*n+100)+145*n+30 := by
  have he := equalOn_count ((a.pair m).comp (gcdNet n)) (wordConstant (n:=k) (BitVec.ofNat n 1))
  have hl := wordLt_count a m
  have hg := gcdNet_count n
  simp only [count_comp,count_pair,wordConstant_count] at he
  rw [usableOn,count_band]
  omega

/-- Every ordinary raw trial uses its actual tensor block. Nonempty candidates
are validated before a shared, linear-size least-positive-candidate fold. -/
def orderResultNet {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) : BooleanNetwork k n :=
  minimumNet (fun i : Fin (n^5) => trialSmallValueNet a m
    (raw.comp (tensorSelect (rawWidth n (sampleExponent n) n) (n^5) i)))
lemma orderResultNet_value {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) (x : Basis k)
    (y : Fin (n^5)→Raw n (sampleExponent n) n) (h : raw.eval x=ordinaryLayout n y)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (bitsValue ((orderResultNet a m raw).eval x)).toNat=
      orderResult (sampleExponent n) n (a.eval x) (m.eval x) (n^5) y := by
  apply minimumNet_value _ x (fun i=>trialResult (sampleExponent n) n (a.eval x) (m.eval x) (y i))
  · intro i
    apply trialSmallValueNet_value _ _ _ x (y i) _ hm
    rw [eval_comp,h]
    exact tensorSelect_eval _ i
  · intro i d hd
    exact ((trialResult_some _ _ _).mp hd).choose_spec.1.1

def ordinaryOn {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) : BooleanNetwork k (Completion.transitionWidth n) :=
  (wordMux (usableOn a m) (orderResultNet a m raw) (wordConstant (BitVec.ofNat n 0))).comp
    (resizeWord n (Completion.transitionWidth n))
lemma ordinaryOn_eval {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) (x : Basis k)
    (y : Fin (n^5)→Raw n (sampleExponent n) n) (h : raw.eval x=ordinaryLayout n y)
    (hn : 1≤n) (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (ordinaryOn a m raw).eval x=ordinary (a.eval x) (m.eval x) y := by
  classical
  rw [ordinaryOn,eval_comp,resizeWord_eq_natBasis,wordMux_eval]
  simp only [usableOn_value a m x hn]
  by_cases hu : Usable (a.eval x) (m.eval x)
  · rw [ite_eq_left hu,orderResultNet_value a m raw x y h hm,ordinary,ite_eq_left hu]
  · rw [ite_eq_right hu,wordConstant_eval,BitVec.toNat_ofNat,Nat.zero_mod,ordinary,ite_eq_right hu]

/-- Completed output decoding keeps the FULL rare guessed transition word. No
truncation, success flag, or later true-order certificate enters this decoder. -/
def outputOn {k n : ℕ} (a m : BooleanNetwork k n) (raw : BooleanNetwork k (width n)) :
    BooleanNetwork k (Completion.transitionWidth n) :=
  wordMux (raw.comp (Completion.rareNet (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
    (raw.comp (Completion.guessWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
    (ordinaryOn a m (raw.comp (Completion.ordinaryWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5))))
lemma outputOn_eval {k n : ℕ} (a m : BooleanNetwork k n) (raw : BooleanNetwork k (width n))
    (x : Basis k) (y : Result n) (h : raw.eval x=layout n y) (hn : 1≤n)
    (hm : 2≤(bitsValue (m.eval x)).toNat) :
    (outputOn a m raw).eval x=output (a.eval x) (m.eval x) y := by
  let z : Completion.Raw (Basis (ordinaryWidth n)) (Completion.transitionWidth n) (2*n) ((n+10)*n^5) :=
    (y.1,ordinaryLayout n y.2.1,y.2.2)
  have hz : layout n y=Completion.layout (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5) z := rfl
  have ho : (raw.comp (Completion.ordinaryWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).eval x=
      ordinaryLayout n y.2.1 := by
    rw [eval_comp,h,hz,Completion.ordinaryWires_eval]
  rw [outputOn,wordMux_eval,ordinaryOn_eval a m _ x y.2.1 ho hn hm]
  simp only [eval_comp,h,hz,Completion.guessWires_eval,Completion.rareNet_eval,output,Completion.output,z]

end OrderSlots
end ExactQuantumFactoring


end

end OAI
