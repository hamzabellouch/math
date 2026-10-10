import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.PivotControllerBody

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def controllerGuard (heads : Fin 35 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 35 :=
  if (heads 23).val ≠ 0 then ⟨.halt,Vector.ofFn (fun _ => .stay)⟩
  else if (heads 26).val ≠ 0 then ⟨.call,Vector.ofFn (fun _ => .stay)⟩
  else if (heads 32).val ≠ 0 then ⟨.restart,Vector.ofFn (fun j => if j=32 then .pop else .stay)⟩
  else ⟨.halt,Vector.ofFn (fun _ => .stay)⟩
def controllerProgram : Program 35 := KS.W29.FixedLoop.loop controllerBody controllerGuard

def controllerConfig (s : Fin 35 → List Bool) : Config 35 controllerProgram.states :=
  ⟨some controllerProgram.initial,s⟩

theorem controller_step_clear (saved : List Bool) (b coin : Bool) :
    controllerProgram.toMachine.step (controllerConfig (state (b::saved) [] [] [] [])) coin =
      controllerConfig (state saved [] [] [] []) := by
  change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState controllerBody),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases b <;> apply congrArg₂ Config.mk
  all_goals
    simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,state,observedHeads,
      KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]
    first | rfl | (funext j; by_cases hj : j = 32 <;> simp [state, hj])

theorem controller_step_empty (coin : Bool) :
    controllerProgram.toMachine.step (controllerConfig (state [] [] [] [] [])) coin =
      ⟨none,state [] [] [] [] []⟩ := by
  change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState controllerBody),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,state,observedHeads,KS.W29.topCode]
    rfl
  · funext j
    simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,state,observedHeads,
      KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]

theorem controller_run_clear (saved bits : List Bool) (hlen : saved.length+1 ≤ bits.length) :
    controllerProgram.toMachine.run (controllerConfig (state saved [] [] [] [])) bits =
      ⟨none,state [] [] [] [] []⟩ := by
  induction saved generalizing bits with
  | nil =>
    cases bits with
    | nil => simp at hlen
    | cons coin bs => erw [Machine.run.eq_2,controller_step_empty,Machine.run_halted _ _ rfl]
  | cons b saved ih =>
    cases bits with
    | nil => simp at hlen
    | cons coin bs =>
      erw [Machine.run.eq_2,controller_step_clear]
      exact ih bs (by simp only [List.length_cons] at hlen; omega)

theorem controller_step_finished (wire : List Bool) (hne : wire ≠ []) (coin : Bool) :
    controllerProgram.toMachine.step (controllerConfig (state [] [] [] [] wire)) coin =
      ⟨none,state [] [] [] [] wire⟩ := by
  change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState controllerBody),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases wire with
  | nil => exact (hne rfl).elim
  | cons b bs =>
    cases b <;> apply congrArg₂ Config.mk
    all_goals
      simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,state,observedHeads,
        KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply]
      rfl

theorem controller_step_call {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (coin : Bool) :
    controllerProgram.toMachine.step (controllerConfig (matrixState saved M)) coin =
      KS.W29.FixedLoop.liftBody controllerBody ⟨some controllerBody.initial,matrixState saved M⟩ := by
  have hne : Computability.encodeNat (n+1) ≠ [] := by
    intro he
    have hz := (KS.W06.RationalSignClassifier.encodeNat_eq_nil (n+1)).mp he
    omega
  change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState controllerBody),_⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases he : Computability.encodeNat (n+1) with
  | nil => exact (hne he).elim
  | cons b bs =>
    cases b <;> apply congrArg₂ Config.mk
    all_goals
      simp [KS.W29.FixedLoop.guardInstruction,controllerGuard,matrixState,state,he,observedHeads,
        KS.W29.topCode,Instruction.action,KS.W29.StackAction.apply] <;>
        first | rfl | (funext j; simp [state])

def localBits {n : ℕ} (M : DenseRatMatrix n) : ℕ := (KS.W08.denseMatrixTape M).length

def controllerTicks : {n N : ℕ} → PivotHistory n N → DenseRatMatrix n → ℕ
  | 0, _, h, _ => (historyTape h).length+1
  | n+1, _, h, M =>
    let b := localBits M
    if DenseRatMatrix.decode M 0 0 < 0 then
      1 + (PivotDecision.ticks M b+(((2+unitTicks n)+1+finishTicks h M (Pi.single 0 1))+1)) + 1
    else if DenseRatMatrix.decode M 0 0 = 0 then
      match firstNonzeroOffDiagonal (DenseRatMatrix.decode M) with
      | some j =>
        1 + (PivotDecision.ticks M b+
          (((2+KS.W19.TerminalWitnessMachine.ticks (historyTape h) M b j.succ)+1+
            finishTicks h M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))+1)) + 1
      | none =>
        1+(PivotDecision.ticks M b+(descentTicks M b+1))+
          controllerTicks (.push (DenseRatMatrix.decode M) h) (child M)
    else
      1+(PivotDecision.ticks M b+(descentTicks M b+1))+
        controllerTicks (.push (DenseRatMatrix.decode M) h) (child M)

theorem controllerTicks_descend {n N : ℕ} (h : PivotHistory (n+1) N) (M : DenseRatMatrix (n+1))
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    controllerTicks h M = 1+(PivotDecision.ticks M (localBits M)+(descentTicks M (localBits M)+1))+
      controllerTicks (.push (DenseRatMatrix.decode M) h) (child M) := by
  rcases pivotTerminal_none_cases (DenseRatMatrix.decode M) ht with ⟨hz,hr⟩ | hp
  · simp [controllerTicks,hz,hr]
  · simp [controllerTicks,hp.ne',not_lt.mpr hp.le]

theorem vectorTape_nonempty {N : ℕ} (hN : 0<N) (q : Fin N → ℚ) : KS.W12.RowDot.vectorTape q ≠ [] := by
  cases N with
  | zero => omega
  | succ N =>
    intro he
    have hl := congrArg List.length he
    simp [KS.W12.RowDot.vectorTape,List.ofFn_succ,KS.W01.length_frame] at hl

end KS.W17.FixedPSD

end OAI
