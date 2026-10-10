import Mathlib
import OAI.Combinatorics.KMedianRecovery.Model
import OAI.Combinatorics.KMedianRecovery.Encoding.Reencode
import OAI.Combinatorics.KMedianRecovery.Recovery.Value

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinaryArithmetic

lemma value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih => simp only [List.cons_append,value,ih,List.length_cons,pow_succ]; ring

lemma value_append_true_pos (xs : List Bool) : 0<value (xs++[true]) := by
  rw [value_append]
  simp only [value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
  have hh : 0<2^xs.length := pow_pos (by norm_num) _
  omega

lemma bits_value_append_true (xs : List Bool) : (value (xs++[true])).bits=xs++[true] := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    simp only [List.cons_append,value]
    have he (n : ℕ) : b.toNat+2*n=Nat.bit b n := by cases b <;> simp [Nat.bit,Nat.add_comm]
    rw [he,Nat.bits_append_bit _ _ (fun h => (value_append_true_pos xs).ne' h |>.elim),ih]

lemma bits_value_reverse (xs : List Bool) :
    (value xs.reverse).bits=(xs.dropWhile (fun b => !b)).reverse := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b with
    | false => simpa [List.reverse_cons,value_append,value] using ih
    | true => simpa using bits_value_append_true xs.reverse

def normalize (xs : List Bool) : List Bool :=
  (xs.reverse.dropWhile (fun b => !b)).reverse

lemma normalize_eq_bits (xs : List Bool) : normalize xs=(value xs).bits := by
  simpa only [List.reverse_reverse,normalize] using (bits_value_reverse xs.reverse).symm

lemma normalize_add (n m : ℕ) : normalize (add false n.bits m.bits)=(n+m).bits := by
  rw [normalize_eq_bits,value_add,value_bits,value_bits]
  rfl

abbrev trimProgram : Program where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Option Bool
  initial := none
  code _ := .pop () (fun _ b => b)
    (.branch (fun s => decide (s=some false))
      (.load (fun _ => none) (.goto (fun _ => ())))
      (.branch Option.isSome
        (.push () (fun _ => true) (.load (fun _ => none) .halt))
        (.load (fun _ => none) .halt)))

def trimCfg (xs : List Bool) : trimProgram.machine.Cfg := ⟨some (),none,fun _ => xs⟩
def trimDone (xs : List Bool) : trimProgram.machine.Cfg := ⟨none,none,fun _ => xs⟩

lemma trim_initial (xs : List Bool) : initList trimProgram.machine xs=trimCfg xs := by
  rw [initList_bool]
  congr 1
lemma trim_final (xs : List Bool) : haltList trimProgram.machine xs=trimDone xs := by
  rw [haltList_bool]
  congr 1
lemma trim_nil : trimProgram.machine.step (trimCfg [])=some (trimDone []) := by
  simp [FinTM2.step,trimCfg,trimDone,trimProgram,TM2.step,TM2.stepAux,unit_update]
  rfl
lemma trim_false (xs : List Bool) :
    trimProgram.machine.step (trimCfg (false::xs))=some (trimCfg xs) := by
  simp [FinTM2.step,trimCfg,trimProgram,TM2.step,TM2.stepAux,unit_update]
  rfl
lemma trim_true (xs : List Bool) :
    trimProgram.machine.step (trimCfg (true::xs))=some (trimDone (true::xs)) := by
  simp [FinTM2.step,trimCfg,trimDone,trimProgram,TM2.step,TM2.stepAux,unit_update]
  rfl

noncomputable def trim_outputs (xs : List Bool) :
    EvalsToInTime trimProgram.machine.step (trimCfg xs)
      (some (trimDone (xs.dropWhile (fun b => !b)))) (xs.length+1) := by
  induction xs with
  | nil => exact one_step trim_nil
  | cons b xs ih =>
    cases b with
    | false => simpa using step_then (trim_false xs) ih
    | true => simpa using time_mono (one_step (trim_true xs)) (by omega : 1≤(true::xs).length+1)

noncomputable def trim_computes : PolyComputes (fun xs => xs.dropWhile (fun b => !b)) where
  program := trimProgram
  time := Polynomial.X+1
  outputs xs := by
    simpa only [TM2OutputsInTime,Option.map_some,trim_initial,trim_final,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one] using trim_outputs xs

noncomputable def add_computes : PolyComputes (fun xs =>
    normalize (add false (extractPrefix xs) (discardPrefix xs))) := by
  have hh := (addReverse_computes.comp trim_computes).comp reverse_computes
  exact hh

noncomputable def addition : Turing.TM2ComputableInPolyTime
    (fun p : ℕ×ℕ => pairBits (p.1.bits,p.2.bits)) Nat.bits (fun p => p.1+p.2) :=
  add_computes.reencode _ _ (fun p => by
    simp only [pairBits,extractPrefix_pair,discardPrefix_pair,normalize_add])

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
