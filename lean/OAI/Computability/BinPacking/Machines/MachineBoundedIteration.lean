import OAI.Computability.BinPacking.Computation.MachineFiniteAlphabet

namespace OAI

namespace BinPackingGap.MachineBoundedIteration

open Turing BinPackingGames.Foundations.Complexity

def inputBits {α : Type} (encode : α → List Bool) (p : Nat × α) : List Bool :=
  encodeWord p.1 ++ encode p.2

@[simp] theorem inputBits_length {α : Type} (encode : α → List Bool) (p : Nat × α) :
    (inputBits encode p).length = p.1 + 1 + (encode p.2).length := by
  simp [inputBits, encodeWord_length]

def iterate {α : Type} (step : α → α) (p : Nat × α) : α := step^[p.1] p.2

noncomputable def timeBound (body growth : Polynomial Nat) : Polynomial Nat :=
  Polynomial.X + 1 +
    Polynomial.X * (body.comp growth + Polynomial.C 2 * growth + Polynomial.C 3) +
    Polynomial.C 2 * growth + Polynomial.C 3

theorem timeBound_eval (body growth : Polynomial Nat) (n : Nat) :
    (timeBound body growth).eval n =
      n + 1 + n * (body.eval (growth.eval n) + 2 * growth.eval n + 3) +
        2 * growth.eval n + 3 := by
  simp [timeBound, Polynomial.eval_comp]

def GrowthBound {α : Type} (encode : α → List Bool) (step : α → α)
    (growth : Polynomial Nat) : Prop :=
  ∀ (p : Nat × α) (i : Nat), i ≤ p.1 →
    (encode (step^[i] p.2)).length ≤ growth.eval (inputBits encode p).length

noncomputable def computation {α : Type} (encode : α → List Bool) (step : α → α)
    (body : TM2ComputableInPolyTime encode encode step)
    (growth : Polynomial Nat) (bounded : GrowthBound encode step growth) :
    TM2ComputableInPolyTime (inputBits encode) encode (iterate step) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := timeBound body.time growth
  outputsFun p := by
    let words : Nat → List Bool := fun i => encode (step^[i] p.2)
    let budgets : Nat → Nat := fun i => body.time.eval (words i).length
    have runs : ∀ i, i < p.1 →
        TM2OutputsInTime body.tm ((words i).map body.inputAlphabet.symm)
          (some ((words (i + 1)).map body.outputAlphabet.symm)) (budgets i) := by
      intro i _
      simpa only [words, budgets, Function.iterate_succ_apply', Equiv.invFun_as_coe] using
        body.outputsFun (step^[i] p.2)
    have run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      p.1 words budgets runs
    have countBound : p.1 ≤ (inputBits encode p).length := by
      rw [inputBits_length]
      omega
    have bodyBound : ∀ i, i < p.1 →
        budgets i ≤ body.time.eval (growth.eval (inputBits encode p).length) := by
      intro i hi
      exact MachineComposition.natPolynomial_eval_mono body.time
        (bounded p i (Nat.le_of_lt hi))
    have lengthBound : ∀ i, i ≤ p.1 →
        (words i).length ≤ growth.eval (inputBits encode p).length := by
      intro i hi
      exact bounded p i hi
    have loopBound := MachineRepeat.loopBudget_le p.1 words budgets
      (body.time.eval (growth.eval (inputBits encode p).length))
      (growth.eval (inputBits encode p).length) bodyBound lengthBound
    have productBound := Nat.mul_le_mul_right
      (body.time.eval (growth.eval (inputBits encode p).length) +
        2 * growth.eval (inputBits encode p).length + 3) countBound
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    have actualBound := run.steps_le_m
    rw [timeBound_eval]
    omega

theorem computation_finiteAlphabet {α : Type} (encode : α → List Bool) (step : α → α)
    (body : TM2ComputableInPolyTime encode encode step)
    (growth : Polynomial Nat) (bounded : GrowthBound encode step growth)
    (finite : MachineFiniteAlphabet.FiniteAlphabet body.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation encode step body growth bounded).tm :=
  MachineFiniteAlphabet.repeat_machine body.tm body.inputAlphabet body.outputAlphabet finite

end BinPackingGap.MachineBoundedIteration

end OAI
