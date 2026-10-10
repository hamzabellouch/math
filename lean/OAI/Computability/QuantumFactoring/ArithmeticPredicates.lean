import Mathlib
import OAI.Computability.QuantumFactoring.WordNetworks

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide
open AIGCompiler BooleanNetwork

def ult (w : ℕ) : BooleanNetwork (w+w) 1 :=
  let r := BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)
  compile r.aig (fun _ => r.ref)

lemma ult_correct (w : ℕ) (a b : Basis w) :
    (ult w).eval (Fin.append a b) 0 =
      decide ((bitsValue a).toNat < (bitsValue b).toNat) := by
  rw [ult,compile_correct]
  have h := BVPred.mkUlt_denote_eq (inputs (w+w)).1
    (leftWord (Fin.append a b)) (rightWord (Fin.append a b))
    (binaryInputs w) (Fin.append a b) (binaryInputs_left w _) (binaryInputs_right w _)
  simpa only [leftWord_append,rightWord_append,BitVec.ult] using h

lemma ult_count (w : ℕ) : (ult w).net.count ≤ 48*w+8 := by
  have h := compile_count (BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)).aig
    (m := 1) (fun _ => (BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)).ref)
  have hs := AIGBounds.ult_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [ult]
  omega

def wordLt {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (a.pair b).comp (ult w)

lemma wordLt_eval {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (wordLt a b).eval x 0 = decide ((bitsValue (a.eval x)).toNat < (bitsValue (b.eval x)).toNat) := by
  rw [wordLt,eval_comp,eval_pair,ult_correct]

lemma wordLt_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (wordLt a b).net.count ≤ a.net.count+b.net.count+48*w+8 := by
  simp only [wordLt,count_comp,count_pair]
  have := ult_count w
  omega

def wordLe {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (wordLt b a).bnot

lemma wordLe_eval {n w : ℕ} (a b : BooleanNetwork n w) (x : Basis n) :
    (wordLe a b).eval x 0 = decide ((bitsValue (a.eval x)).toNat ≤ (bitsValue (b.eval x)).toNat) := by
  rw [wordLe,eval_bnot,wordLt_eval]
  by_cases h : (bitsValue (a.eval x)).toNat ≤ (bitsValue (b.eval x)).toNat
  · simp [h,Nat.not_lt.mpr h]
  · simp [h,Nat.lt_of_not_ge h]

lemma wordLe_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (wordLe a b).net.count ≤ a.net.count+b.net.count+48*w+9 := by
  simp only [wordLe,count_bnot]
  have := wordLt_count b a
  omega

def wordEq (w : ℕ) : BooleanNetwork (w+w) 1 :=
  ((ult w).bor (((select (Fin.addCases (Fin.natAdd w) (Fin.castAdd w))).comp (ult w)))).bnot

lemma wordEq_eval (w : ℕ) (a b : Basis w) :
    (wordEq w).eval (Fin.append a b) 0 = decide (bitsValue a = bitsValue b) := by
  have he : (select (Fin.addCases (Fin.natAdd w) (Fin.castAdd w))).eval (Fin.append a b) =
      Fin.append b a := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [eval_select,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right]
  rw [wordEq,eval_bnot,eval_bor,eval_comp,he,ult_correct,ult_correct]
  have hh : bitsValue a = bitsValue b ↔ (bitsValue a).toNat=(bitsValue b).toNat := by
    constructor
    · exact congrArg BitVec.toNat
    · exact BitVec.eq_of_toNat_eq
  simp only [hh]
  cases h₁ : decide ((bitsValue a).toNat < (bitsValue b).toNat) <;>
    cases h₂ : decide ((bitsValue b).toNat < (bitsValue a).toNat) <;>
    simp_all <;> omega

lemma wordEq_count (w : ℕ) : (wordEq w).net.count ≤ 96*w+21 := by
  simp only [wordEq,count_bnot,count_bor,count_comp,count_select,zero_add]
  have := ult_count w
  omega

/-- Static natural exponent, with retained accumulator and no repeated
construction of earlier expressions. This circuit has O(e w²) Boolean nodes. -/
def staticPowerStep (w : ℕ) : BooleanNetwork (w+w) (w+w) :=
  (select (Fin.castAdd w)).pair (mul w)

def staticPower (w e : ℕ) : BooleanNetwork w w :=
  ((select id).pair (wordConstant (BitVec.ofNat w 1))).comp
    (((staticPowerStep w).iterate e).rewire (Fin.natAdd w))

lemma staticPowerStep_eval (w : ℕ) (a b : Basis w) :
    (staticPowerStep w).eval (Fin.append a b) =
      Fin.append a ((mul w).eval (Fin.append a b)) := by
  simp only [staticPowerStep,eval_pair,eval_select]
  congr 1
  funext i
  exact Fin.append_left a b i

lemma staticPower_iterate (w e : ℕ) (a b : Basis w) :
    ∃ z : Basis w,
      ((staticPowerStep w).iterate e).eval (Fin.append a b) = Fin.append a z ∧
      bitsValue z = bitsValue a^e * bitsValue b := by
  induction e generalizing b with
  | zero => refine ⟨b,?_,?_⟩ <;> simp [eval_iterate]
  | succ e ih =>
    rw [eval_iterate,Function.iterate_succ_apply,staticPowerStep_eval]
    have h := ih ((mul w).eval (Fin.append a b))
    rw [eval_iterate] at h
    obtain ⟨z,hz,hv⟩ := h
    refine ⟨z,hz,?_⟩
    rw [hv,mul_word,pow_succ]
    exact (mul_assoc _ _ _).symm

lemma staticPower_eval (w e : ℕ) (a : Basis w) :
    bitsValue ((staticPower w e).eval a) = bitsValue a^e := by
  simp only [staticPower,eval_comp,eval_pair,eval_select,Function.comp_id,eval_rewire]
  obtain ⟨z,hz,hv⟩ := staticPower_iterate w e a ((wordConstant (BitVec.ofNat w 1)).eval a)
  rw [hz]
  have he : Fin.append a z ∘ Fin.natAdd w = z := by funext i; exact Fin.append_right _ _ i
  rw [he,hv,wordConstant_eval]
  simp

lemma staticPower_count (w e : ℕ) : (staticPower w e).net.count ≤
    w+e*(90*w*w+14*w+6) := by
  simp only [staticPower,count_comp,count_pair,count_select,wordConstant_count,zero_add,
    count_rewire,count_iterate,staticPowerStep]
  have h := mul_count w
  exact Nat.add_le_add_left (Nat.mul_le_mul_left e h) w

end ExactQuantumFactoring.BitArithmetic


end

end OAI
