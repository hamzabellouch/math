import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineFiniteAlphabet
import OAI.Combinatorics.IndependentSets.Machines.GraphCounterFinish

namespace OAI

namespace LargeIndependentSets.BoundedIteration
open Turing
open IndependentSetsGames.Foundations.Complexity

variable {α β : Type}

def counted (count : α → ℕ) (enc : β → List Bool) (start : α → β) (a : α) : List Bool :=
  encodeWord (count a) ++ enc (start a)

lemma count_le (count : α → ℕ) (enc : β → List Bool) (start : α → β) (a : α) :
    count a ≤ (counted count enc start a).length := by
  simp [counted,encodeWord]

noncomputable def runtime (body length : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X*(body.comp length + 2*length + 4) + 2*length + 4

lemma runtime_eval (body length : Polynomial ℕ) (n : ℕ) :
    (runtime body length).eval n = n*(body.eval (length.eval n)+2*length.eval n+4)+2*length.eval n+4 := by
  simp [runtime]

noncomputable def certificate (enc : β → List Bool) (step : β → β) (start : α → β)
    (count : α → ℕ) (body : TM2ComputableInPolyTime enc enc step) (length : Polynomial ℕ)
    (growth : ∀ a i, i≤count a → (enc (step^[i] (start a))).length ≤
      length.eval (counted count enc start a).length) :
    TM2ComputableInPolyTime (counted count enc start) enc
      (fun a => step^[count a] (start a)) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtime body.time length
  outputsFun a := by
    let words : ℕ → List Bool := fun i => enc (step^[i] (start a))
    let budgets : ℕ → ℕ := fun i => body.time.eval (words i).length
    have runs (i : ℕ) (_hi : i<count a) :
        TM2OutputsInTime body.tm ((words i).map body.inputAlphabet.symm)
          (some ((words (i+1)).map body.outputAlphabet.symm)) (budgets i) := by
      simpa only [words,budgets,Function.iterate_succ_apply',Equiv.symm,Equiv.coe_fn_mk] using
        body.outputsFun (step^[i] (start a))
    let run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      (count a) words budgets runs
    have start_eq : encodeWord (count a) ++ words 0 = counted count enc start a := rfl
    rw [start_eq] at run
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    let N := (counted count enc start a).length
    let L := length.eval N
    let B := body.time.eval L
    have hl (i : ℕ) (hi : i≤count a) : (words i).length≤L := growth a i hi
    have hb (i : ℕ) (hi : i<count a) : budgets i≤B :=
      MachineComposition.natPolynomial_eval_mono body.time (hl i hi.le)
    have hloop := MachineRepeat.loopBudget_le (count a) words budgets B L hb hl
    have hc : count a≤N := count_le count enc start a
    rw [runtime_eval]
    calc
      run.steps ≤ count a+1+MachineRepeat.loopBudget (count a) words budgets := run.steps_le_m
      _ ≤ count a+1+(count a*(B+2*L+3)+2*L+3) := Nat.add_le_add_left hloop _
      _ = count a*(B+2*L+4)+2*L+4 := by ring
      _ ≤ N*(B+2*L+4)+2*L+4 := by gcongr

lemma certificate_finiteAlphabet (enc : β → List Bool) (step : β → β) (start : α → β)
    (count : α → ℕ) (body : TM2ComputableInPolyTime enc enc step) (length : Polynomial ℕ)
    (growth) (hbody : MachineFiniteAlphabet.FiniteAlphabet body.tm)
    (k : (certificate enc step start count body length growth).tm.K) :
    Finite ((certificate enc step start count body length growth).tm.Γ k) :=
  MachineFiniteAlphabet.repeat_machine body.tm body.inputAlphabet body.outputAlphabet hbody k
end LargeIndependentSets.BoundedIteration

end OAI
