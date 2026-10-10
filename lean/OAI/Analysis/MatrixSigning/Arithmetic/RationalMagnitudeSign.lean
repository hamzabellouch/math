import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeSetup

namespace OAI

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

private theorem sign_initial : normalizeSign.initial=(0 : Fin 2) :=rfl
private theorem one_initial : insertOne.initial=(0 : Fin 1) :=rfl

lemma sign_zero_first (d : List Bool) (sgn coin : Bool) :
    (compile (0 : Fin 2) (10 : Fin 13) 10 signDispatch).step ⟨some (0 : Fin 2), state [] d sgn⟩ coin =
      ⟨some (1 : Fin 2), Function.update (state [] d sgn) (12 : Fin 13) []⟩ := by
  erw [step_compile]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

lemma sign_zero_second (d : List Bool) (sgn coin : Bool) :
    (compile (0 : Fin 2) (10 : Fin 13) 10 signDispatch).step ⟨some (1 : Fin 2), Function.update (state [] d sgn) (12 : Fin 13) []⟩ coin =
      ⟨none, state [] d false⟩ := by
  erw [step_compile]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

lemma sign_nonzero (n d : List Bool) (hn : n ≠ []) (sgn coin : Bool) :
    (compile (0 : Fin 2) (10 : Fin 13) 10 signDispatch).step ⟨some (0 : Fin 2), state n d sgn⟩ coin = ⟨none, state n d sgn⟩ := by
  cases n with
  | nil => exact (hn rfl).elim
  | cons b bs =>
    erw [step_compile]
    cases b <;> apply config_ext
    all_goals first | rfl | (intro j; fin_cases j <;> rfl)

theorem normalizeSign_spec (n d : List Bool) (sgn : Bool) :
    RunSpec normalizeSign (state n d sgn) (state n d (if n = [] then false else sgn)) 2 := by
  intro bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (compile (0 : Fin 2) (10 : Fin 13) 10 signDispatch) _ bits).trans ?_
  rw [sign_initial]
  cases bits with
  | nil => simp at hlen
  | cons c tail =>
    by_cases hn : n = []
    · subst n
      cases tail with
      | nil => simp at hlen
      | cons c' rest =>
        have hr : rest = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hlen; omega
        subst rest
        erw [Machine.run.eq_2]
        erw [sign_zero_first d sgn c]
        erw [Machine.run.eq_2]
        erw [sign_zero_second d sgn c']
        all_goals rfl
    · erw [Machine.run.eq_2]
      erw [sign_nonzero n d hn sgn c]
      rw [Machine.run_halted _ _ rfl]
      all_goals (simp only [ite_eq_right hn]; rfl)

theorem zeroNumerator_spec (n : List Bool) (sgn : Bool) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram (10 : Fin 13))
      (state n [] sgn) (state [] [] sgn) (n.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (10 : Fin 13) (state n [] sgn) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.clearMachine (10 : Fin 13)) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

private theorem insertOne_layout (sgn : Bool) :
    Function.update (state [] [] sgn) (11 : Fin 13) [true]=state [] [true] sgn :=by
  funext j
  fin_cases j <;> simp [state,«stacks»]

theorem insertOne_spec (sgn : Bool) :
    RunSpec insertOne (state [] [] sgn) (state [] [true] sgn) 1 := by
  intro bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (compile (0 : Fin 1) (10 : Fin 13) 10 oneDispatch) _ bits).trans ?_
  rw [one_initial]
  cases bits with
  | nil => simp at hlen
  | cons coin tail =>
    have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hlen; omega
    subst tail
    erw [Machine.run.eq_2]
    erw [step_compile (0 : Fin 1) (10 : Fin 13) 10 oneDispatch
      (0 : Fin 1) (state [] [] sgn) coin]
    apply config_ext
    · rfl
    · intro j
      fin_cases j <;> rfl

theorem zeroBranch_spec (n : List Bool) (sgn : Bool) :
    RunSpec zeroBranch (state n [] sgn) (state [] [true] false) (n.length + 4) := by
  have h := (zeroNumerator_spec n sgn).compose
    ((insertOne_spec sgn).compose (normalizeSign_spec [] [true] sgn))
  convert h using 1 <;> rfl

theorem clearGCD_spec (g n d : List Bool) (sgn : Bool) :
    RunSpec clearGCD (divisorState g n d sgn) (state n d sgn) (g.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (2 : Fin 13) (divisorState g n d sgn) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.clearMachine (2 : Fin 13)) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

end KS.W30.RationalMagnitudeMachine

end OAI
