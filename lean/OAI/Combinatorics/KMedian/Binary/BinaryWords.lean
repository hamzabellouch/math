import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanReverse

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

@[simp] theorem value_nil : value []=0 := rfl
@[simp] theorem value_cons (b : Bool) (xs : List Bool) : value (b::xs)=b.toNat+2*value xs := rfl

 theorem value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn,value_cons,ih,Nat.bit_val]; omega

 theorem value_zero (xs : List Bool) : value xs=0 ↔ ∀ b∈xs,b=false := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [value_cons,Nat.add_eq_zero_iff,Nat.mul_eq_zero,OfNat.ofNat_ne_zero,false_or,Bool.toNat_eq_zero,ih,List.forall_mem_cons]

 theorem bits_value (xs : List Bool) (h : xs.getLast?≠some false) : (value xs).bits=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      by_cases he : xs=[]
      · subst xs
        cases b
        · exact False.elim (h rfl)
        · rfl
      · have ht : xs.getLast?≠some false := by
          intro hh
          apply h
          simp only [List.getLast?_cons,hh,Option.getD_some]
        rw [value_cons,show b.toNat+2*value xs=Nat.bit b (value xs) by rw [Nat.bit_val]; omega]
        rw [Nat.bits_append_bit,ih ht]
        intro hzero
        exfalso
        have hh := value_zero xs |>.mp hzero
        have hl := List.getLast_mem he
        have hb := hh _ hl
        apply ht
        rw [List.getLast?_eq_some_getLast he,hb]

 theorem value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [List.cons_append,value_cons,ih,List.length_cons,pow_succ]; ring

 theorem value_reverse_drop (xs : List Bool) : value (xs.dropWhile Bool.not).reverse=value xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · simp only [List.dropWhile_cons,Bool.not_false,ite_true,List.reverse_cons,value_append,
          value_cons,value_nil,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,zero_add]
        exact ih
      · simp

 theorem drop_head (xs : List Bool) : (xs.dropWhile Bool.not).head?≠some false := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all

 def normalize (xs : List Bool) : List Bool := (xs.reverse.dropWhile Bool.not).reverse

 theorem normalize_eq_bits (xs : List Bool) : normalize xs=(value xs).bits := by
  have hv : value (normalize xs)=value xs := by
    simpa only [normalize,List.reverse_reverse] using value_reverse_drop xs.reverse
  rw [← hv,bits_value]
  simp only [normalize,List.getLast?_reverse]
  exact drop_head _

end Word

namespace WordTransducer

def dropFalse : Transducer where
  Q := Bool
  initial := false
  next q b := (q || b,if q || b then [b] else [])
  finish _ := []

 theorem dropFalse_true (xs : List Bool) : dropFalse.run true xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::dropFalse.run true xs=b::xs; rw [ih]

 theorem dropFalse_run (xs : List Bool) : dropFalse.run false xs=xs.dropWhile Bool.not := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · exact ih
      · exact congrArg (List.cons true) (dropFalse_true xs)

end WordTransducer

namespace PolyProgram
noncomputable def append : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => x.1++x.2) :=
  ((reverse.thread id).comp ReverseLoop.loop).congr _ (fun x => by
    simp only [Function.comp_apply,ReverseLoop.result,List.reverse_reverse])

noncomputable def dropFalse : PolyProgram id id (List.dropWhile Bool.not) :=
  WordTransducer.dropFalse.program.of_word (fun xs => by
    simpa only [WordTransducer.dropFalse,id_eq] using WordTransducer.dropFalse_run xs)

noncomputable def normalize : PolyProgram id id Word.normalize :=
  ((reverse.comp dropFalse).comp reverse).congr _ (fun _ => rfl)

noncomputable def toBits : PolyProgram id Nat.bits Word.value :=
  normalize.of_word (fun xs => Word.normalize_eq_bits xs)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
