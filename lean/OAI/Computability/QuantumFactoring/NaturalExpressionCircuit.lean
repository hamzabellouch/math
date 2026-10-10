import Mathlib
import OAI.Computability.QuantumFactoring.NaturalExpressions
import OAI.Computability.QuantumFactoring.SplitCandidate

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace BitArithmetic

def natSubOn {k w : ℕ} (a b : BooleanNetwork k w) : BooleanNetwork k w :=
  wordMux (wordLe b a) ((a.pair b).comp (sub w)) (wordConstant (BitVec.ofNat w 0))

lemma natSubOn_value {k w : ℕ} (a b : BooleanNetwork k w) (x : Basis k) :
    (bitsValue ((natSubOn a b).eval x)).toNat=
      (bitsValue (a.eval x)).toNat-(bitsValue (b.eval x)).toNat := by
  rw [natSubOn,wordMux_eval,wordLe_eval]
  by_cases h : (bitsValue (b.eval x)).toNat ≤ (bitsValue (a.eval x)).toNat
  · rw [ite_eq_left (by simpa using h),eval_comp,eval_pair,sub_word,BitVec.toNat_sub]
    have hb := (bitsValue (b.eval x)).isLt
    have ha := (bitsValue (a.eval x)).isLt
    have he : 2^w-(bitsValue (b.eval x)).toNat+(bitsValue (a.eval x)).toNat=
        2^w+((bitsValue (a.eval x)).toNat-(bitsValue (b.eval x)).toNat) := by omega
    rw [he,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using h),wordConstant_eval]
    simp only [BitVec.toNat_ofNat,Nat.zero_mod]
    omega

lemma natSubOn_count {k w : ℕ} (a b : BooleanNetwork k w) :
    (natSubOn a b).net.count ≤ 2*a.net.count+2*b.net.count+214*w+15 := by
  have hc := wordLe_count b a
  have hs := sub_count w
  simp only [natSubOn,wordMux_count,count_comp,count_pair,wordConstant_count]
  omega

end BitArithmetic
namespace NatExpr
variable {v : Type*} {k w : ℕ}

def compile (vars : v → BooleanNetwork k w) : NatExpr v → BooleanNetwork k w
  | .var i => vars i
  | .const c => wordConstant (BitVec.ofNat w c)
  | .add a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.add w)
  | .mul a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.mul w)
  | .sub a b => natSubOn (compile vars a) (compile vars b)
  | .div a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.div w)
  | .mod a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.mod w)
  | .iteLe a b c d => wordMux (wordLe (compile vars a) (compile vars b))
      (compile vars c) (compile vars d)

lemma compile_value (vars : v → BooleanNetwork k w) (x : Basis k)
    (e : NatExpr v) (he : Fits (2^w) (fun i => (bitsValue ((vars i).eval x)).toNat) e) :
    (bitsValue ((e.compile vars).eval x)).toNat=
      e.eval (fun i => (bitsValue ((vars i).eval x)).toNat) := by
  induction e with
  | var i => rfl
  | const c =>
    rw [compile,wordConstant_eval,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt he.1
  | add a b ia ib =>
    rw [compile,eval_comp,eval_pair,add_word,BitVec.toNat_add,ia he.2.1,ib he.2.2]
    exact Nat.mod_eq_of_lt he.1
  | mul a b ia ib =>
    rw [compile,eval_comp,eval_pair,mul_word,BitVec.toNat_mul,ia he.2.1,ib he.2.2]
    exact Nat.mod_eq_of_lt he.1
  | sub a b ia ib =>
    rw [compile,natSubOn_value,ia he.2.1,ib he.2.2]
    rfl
  | div a b ia ib =>
    rw [compile,eval_comp,eval_pair,div_word,BitVec.toNat_udiv,ia he.2.1,ib he.2.2]
    rfl
  | mod a b ia ib =>
    rw [compile,eval_comp,eval_pair,mod_word,BitVec.toNat_umod,ia he.2.1,ib he.2.2]
    rfl
  | iteLe a b c d ia ib ic id =>
    rw [compile,wordMux_eval,wordLe_eval,ia he.2.1,ib he.2.2.1]
    simp only [eval,decide_eq_true_eq]
    split_ifs
    · exact ic he.2.2.2.1
    · exact id he.2.2.2.2

/-- Syntactic duplication cost; independent of the numerical constants. -/
def cost : NatExpr v → ℕ
  | .var _ | .const _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => 2*(cost a+cost b)+1
  | .iteLe a b c d => 2*(cost a+cost b+cost c+cost d)+1

def operationBound (w : ℕ) : ℕ := 300*w*w+1000*w+200

lemma compile_count (vars : v → BooleanNetwork k w) {c : ℕ} (hc : ∀ i, (vars i).net.count ≤ c)
    (e : NatExpr v) : (e.compile vars).net.count ≤ e.cost*(operationBound w+c) := by
  induction e with
  | var i =>
    simp only [compile,cost,one_mul]
    exact (hc i).trans (Nat.le_add_left _ _)
  | const d => simp only [compile,cost,one_mul,wordConstant_count,operationBound]; omega
  | add a b ia ib =>
    have hh := add_count w
    simp only [compile,count_comp,count_pair,cost]
    dsimp [operationBound] at *
    nlinarith
  | mul a b ia ib =>
    have hh := mul_count w
    simp only [compile,count_comp,count_pair,cost]
    dsimp [operationBound] at *
    nlinarith
  | sub a b ia ib =>
    have hh := natSubOn_count (a.compile vars) (b.compile vars)
    change (natSubOn (a.compile vars) (b.compile vars)).net.count ≤ _
    simp only [cost]
    dsimp [operationBound] at *
    nlinarith
  | div a b ia ib =>
    have hh := div_count w
    simp only [compile,count_comp,count_pair,cost]
    dsimp [operationBound] at *
    nlinarith
  | mod a b ia ib =>
    have hh := mod_count w
    simp only [compile,count_comp,count_pair,cost]
    dsimp [operationBound] at *
    nlinarith
  | iteLe a b d e ia ib id ie =>
    have hh := wordLe_count (a.compile vars) (b.compile vars)
    simp only [compile,wordMux_count,cost]
    dsimp [operationBound] at *
    nlinarith

end NatExpr
end ExactQuantumFactoring


end

end OAI
