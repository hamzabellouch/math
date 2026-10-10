import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.BinaryNormalize

namespace OAI

namespace MatchingFPRAS.BinaryDivision
open StackAddition (value value_bits)

def low (b : Bool) (B R : List Bool) : Bool := decide (value (b::R)<value B)
def nextQ (b : Bool) (B Q R : List Bool) : List Bool := (!low b B R)::Q
def nextR (b : Bool) (B R : List Bool) : List Bool :=
  if low b B R then b::R else (value (b::R)-value B).bits

def run : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | [],_,Q,R => (Q,R)
  | b::A,B,Q,R => run A B (nextQ b B Q R) (nextR b B R)

lemma value_bits_length (A : List Bool) : (value A).bits.length≤A.length := by
  simpa only [BinaryNormalize.normalize_bits] using BinaryNormalize.normalize_length A
lemma bits_length_mono {m n : ℕ} (h : m≤n) : m.bits.length≤n.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h
lemma nextR_length (b : Bool) (B R : List Bool) : (nextR b B R).length≤R.length+1 := by
  unfold nextR
  split_ifs
  · simp
  · exact (bits_length_mono (Nat.sub_le _ _)).trans (value_bits_length (b::R))
lemma nextQ_length (b : Bool) (B Q R : List Bool) : (nextQ b B Q R).length=Q.length+1 := rfl

lemma step_remainder (b : Bool) (B R : List Bool) (h : value R<value B) :
    value (nextR b B R)<value B := by
  have hb : b.toNat≤1 := by cases b <;> decide
  unfold nextR low
  split_ifs with hl
  · simpa using hl
  · rw [value_bits]
    simp only [value] at *
    omega
lemma step_mass (b : Bool) (B Q R : List Bool) :
    value (nextQ b B Q R)*value B+value (nextR b B R)=
      2*(value Q*value B+value R)+b.toNat := by
  by_cases hh : value (b::R)<value B
  · simp only [nextQ,nextR,low,hh,decide_true,Bool.not_true,↓reduceIte]
    simp only [value,Bool.toNat_false]
    ring
  · have hle : value B≤value (b::R) := by omega
    simp only [nextQ,nextR,low,hh,decide_false,Bool.not_false,Bool.false_eq_true,↓reduceIte]
    simp only [value_bits,value,Bool.toNat_true]
    simp only [value] at hle
    have he := Nat.sub_add_cancel hle
    nlinarith

lemma value_append (A B : List Bool) : value (A++B)=value A+2^A.length*value B := by
  induction A with
  | nil => simp [value]
  | cons a A ih => simp only [List.cons_append,value,ih,List.length_cons,pow_succ]; ring
lemma value_reverse_cons (b : Bool) (A : List Bool) :
    value (b::A).reverse=value A.reverse+2^A.length*b.toNat := by
  rw [List.reverse_cons,value_append]
  simp [value,List.length_reverse]

lemma run_mass (A B Q R : List Bool) :
    value (run A B Q R).1*value B+value (run A B Q R).2=
      (value Q*value B+value R)*2^A.length+value A.reverse := by
  induction A generalizing Q R with
  | nil => simp [run,value]
  | cons b A ih =>
    rw [run,ih,step_mass,value_reverse_cons,List.length_cons,pow_succ]
    ring
lemma run_remainder (A B Q R : List Bool) (h : value R<value B) :
    value (run A B Q R).2<value B := by
  induction A generalizing Q R with
  | nil => exact h
  | cons b A ih => exact ih _ _ (step_remainder b B R h)
lemma run_lengths (A B Q R : List Bool) :
    (run A B Q R).1.length=Q.length+A.length ∧
      (run A B Q R).2.length≤R.length+A.length := by
  induction A generalizing Q R with
  | nil => simp [run]
  | cons b A ih =>
    obtain ⟨hQ,hR⟩:=ih (nextQ b B Q R) (nextR b B R)
    have hr:=nextR_length b B R
    simp only [run,List.length_cons]
    rw [hQ,nextQ_length]
    exact ⟨by omega,by omega⟩

theorem correct (m n : ℕ) (hn : 0<n) :
    value (run m.bits.reverse n.bits [] []).1=m/n ∧
      value (run m.bits.reverse n.bits [] []).2=m%n := by
  have hm:=run_mass m.bits.reverse n.bits [] []
  have hr:=run_remainder m.bits.reverse n.bits [] [] (by simpa only [value,value_bits] using hn)
  simp only [List.reverse_reverse,value_bits,value,Nat.zero_mul,Nat.zero_add] at hm hr
  have hd := (Nat.div_mod_unique hn).2 ⟨by simpa only [Nat.add_comm,Nat.mul_comm] using hm,hr⟩
  exact ⟨hd.1.symm,hd.2.symm⟩
end MatchingFPRAS.BinaryDivision

end OAI
