import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeMachine

namespace OAI

namespace KS.W30.RationalReciprocal
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

def transfer (source target scratch : Fin 13) : Program 13 :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

def transferred (before : Fin 13 → List Bool) (source target : Fin 13) : Fin 13 → List Bool :=
  fun j => if j = source then [] else if j = target then before source else before j

theorem transfer_spec (source target scratch : Fin 13)
    (hst : source ≠ target) (hsc : source ≠ scratch) (hct : scratch ≠ target)
    (before : Fin 13 → List Bool) (ht : before target = []) (hc : before scratch = []) :
    RunSpec (transfer source target scratch) before (transferred before source target)
      (2 * (before source).length + 2) := by
  let mid : Fin 13 → List Bool := fun j =>
    if j = source then [] else if j = scratch then (before source).reverse else before j
  have hfirst : RunSpec (KS.W04.BinaryStackMoves.moveProgram source scratch)
      before mid ((before source).length + 1) := by
    intro bits hlen
    have h := KS.W04.BinaryStackMoves.run_move_stacks source scratch hsc before bits hlen
    refine (KS.W19.MachineTransport.run_ofMachine
      (KS.W04.BinaryStackMoves.moveMachine source scratch) _ bits).trans ?_
    refine h.trans ?_
    apply config_ext
    · rfl
    · intro j
      simp only [KS.W04.BinaryStackMoves.twoConfig, hc, List.append_nil, mid]
  have hsecond : RunSpec (KS.W04.BinaryStackMoves.moveProgram scratch target)
      mid (transferred before source target) ((before source).length + 1) := by
    intro bits hlen
    have hmid : mid scratch = (before source).reverse := by simp [mid, Ne.symm hsc]
    have h := KS.W04.BinaryStackMoves.run_move_stacks scratch target hct mid bits
      (by simpa only [hmid, List.length_reverse] using hlen)
    refine (KS.W19.MachineTransport.run_ofMachine
      (KS.W04.BinaryStackMoves.moveMachine scratch target) _ bits).trans ?_
    refine h.trans ?_
    apply config_ext
    · rfl
    · intro j
      by_cases hs : j = source
      · subst j
        simp [KS.W04.BinaryStackMoves.twoConfig, transferred, mid, hst, hsc]
      · by_cases hj : j = target
        · subst j
          simp [KS.W04.BinaryStackMoves.twoConfig, transferred, mid, Ne.symm hst,
            Ne.symm hsc, Ne.symm hct, ht]
        · by_cases hk : j = scratch
          · subst j
            simp [KS.W04.BinaryStackMoves.twoConfig, transferred, mid, Ne.symm hsc, hct, hc]
          · simp [KS.W04.BinaryStackMoves.twoConfig, transferred, mid, hs, hj, hk]
  have h := hfirst.compose hsecond
  convert h using 1 <;> first | rfl | omega

def saveNumerator : Program 13 := transfer 10 9 8
def shiftDenominator : Program 13 := transfer 11 10 8
def restoreNumerator : Program 13 := transfer 9 11 8
def swap : Program 13 := compose saveNumerator (compose shiftDenominator restoreNumerator)

def savedState (n d : List Bool) (sgn : Bool) : Fin 13 → List Bool :=
  RationalMagnitudeMachine.«stacks» ![[],[],[],[],[],[],[],[],[],n] [] d sgn
def shiftedState (n d : List Bool) (sgn : Bool) : Fin 13 → List Bool :=
  RationalMagnitudeMachine.«stacks» ![[],[],[],[],[],[],[],[],[],n] d [] sgn

theorem saveNumerator_spec (n d : List Bool) (sgn : Bool) :
    RunSpec saveNumerator (RationalMagnitudeMachine.state n d sgn)
      (savedState n d sgn) (2 * n.length + 2) := by
  have h := transfer_spec 10 9 8 (by decide) (by decide) (by decide)
    (RationalMagnitudeMachine.state n d sgn) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> rfl

theorem shiftDenominator_spec (n d : List Bool) (sgn : Bool) :
    RunSpec shiftDenominator (savedState n d sgn) (shiftedState n d sgn) (2 * d.length + 2) := by
  have h := transfer_spec 11 10 8 (by decide) (by decide) (by decide)
    (savedState n d sgn) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> rfl

theorem restoreNumerator_spec (n d : List Bool) (sgn : Bool) :
    RunSpec restoreNumerator (shiftedState n d sgn)
      (RationalMagnitudeMachine.state d n sgn) (2 * n.length + 2) := by
  have h := transfer_spec 9 11 8 (by decide) (by decide) (by decide)
    (shiftedState n d sgn) rfl rfl
  convert h using 1 <;> (try rfl)
  funext j
  fin_cases j <;> rfl

theorem swap_spec (n d : List Bool) (sgn : Bool) :
    RunSpec swap (RationalMagnitudeMachine.state n d sgn)
      (RationalMagnitudeMachine.state d n sgn) (4 * n.length + 2 * d.length + 6) := by
  have h := (saveNumerator_spec n d sgn).compose
    ((shiftDenominator_spec n d sgn).compose (restoreNumerator_spec n d sgn))
  convert h using 1 <;> first | rfl | omega

end KS.W30.RationalReciprocal

end OAI
