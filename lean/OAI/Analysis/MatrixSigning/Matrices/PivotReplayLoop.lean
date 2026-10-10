import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.UniformElimination
import OAI.Analysis.MatrixSigning.Optimization.PivotWitnessMachine

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def historyTape : {n N : ℕ} → PivotHistory n N → List Bool
  | _, _, .nil _ => []
  | n, _, .push M rest =>
      savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape (DenseRatMatrix.ofMatrix M)) ++
        historyTape rest

def replayGuard (heads : Fin 35 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 35 :=
  ⟨if (heads 32).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩
def restoreAllProgram : Program 35 := KS.W29.FixedLoop.loop popReplayProgram replayGuard

def restoreConfig (s : Fin 35 → List Bool) : Config 35 restoreAllProgram.states :=
  ⟨some restoreAllProgram.initial, s⟩

def restoreTicks : {n N : ℕ} → (h : PivotHistory n N) → (Fin n → ℚ) → ℕ
  | _, _, .nil _, _ => 1
  | n, _, .push M rest, y =>
      1 + (9 * (Computability.encodeNat (n+1)).length +
        3 * (KS.W08.denseMatrixTape (DenseRatMatrix.ofMatrix M)).length + 7 +
        replayTicks (DenseRatMatrix.ofMatrix M) y) +
        restoreTicks rest (schurWitnessLift M y)

theorem restore_step_empty (wire : List Bool) (coin : Bool) :
    restoreAllProgram.toMachine.step (restoreConfig (state [] [] [] [] wire)) coin =
      ⟨none, state [] [] [] [] wire⟩ := by
  change (KS.W29.FixedLoop.loop popReplayProgram replayGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState popReplayProgram), _⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply congrArg₂ Config.mk
  · simp [KS.W29.FixedLoop.guardInstruction, replayGuard, state, observedHeads, KS.W29.topCode]
    rfl
  · funext j
    simp [KS.W29.FixedLoop.guardInstruction, replayGuard, Instruction.action, KS.W29.StackAction.apply]

theorem restore_step_nonempty (saved wire : List Bool) (hne : saved ≠ []) (coin : Bool) :
    restoreAllProgram.toMachine.step (restoreConfig (state saved [] [] [] wire)) coin =
      KS.W29.FixedLoop.liftBody popReplayProgram
        ⟨some popReplayProgram.initial, state saved [] [] [] wire⟩ := by
  change (KS.W29.FixedLoop.loop popReplayProgram replayGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState popReplayProgram), _⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases saved with
  | nil => exact (hne rfl).elim
  | cons b bs =>
    cases b <;> apply congrArg₂ Config.mk
    all_goals
      simp [KS.W29.FixedLoop.guardInstruction, replayGuard, state, observedHeads, KS.W29.topCode,
        Instruction.action, KS.W29.StackAction.apply] <;> rfl

theorem run_restoreAll {n N : ℕ} (h : PivotHistory n N) (y : Fin n → ℚ)
    (bits : List Bool) (hlen : restoreTicks h y ≤ bits.length) :
    restoreAllProgram.toMachine.run
      (restoreConfig (state (historyTape h) [] [] [] (KS.W12.RowDot.vectorTape y))) bits =
      ⟨none, state [] [] [] [] (KS.W12.RowDot.vectorTape (h.restore y))⟩ := by
  induction h generalizing bits with
  | nil n =>
    cases bits with
    | nil => simp [restoreTicks] at hlen
    | cons coin bs =>
      simp only [historyTape]
      erw [Machine.run.eq_2, restore_step_empty, Machine.run_halted _ _ rfl]
      rfl
  | @push n N M rest ih =>
    let A := DenseRatMatrix.ofMatrix M
    have hb := popReplay_spec (historyTape rest) A y
    have he : liftedTape A y = KS.W12.RowDot.vectorTape (schurWitnessLift M y) := by
      simp [liftedTape, A]
    rw [he] at hb
    have hne : historyTape (PivotHistory.push M rest) ≠ [] := by
      intro hnil
      have hh := congrArg List.length hnil
      simp only [historyTape, List.length_append, savedFrame, KS.W01.length_frame, List.length_nil] at hh
      omega
    cases bits with
    | nil => simp [restoreTicks] at hlen
    | cons coin bs =>
      have hbody : (9 * (Computability.encodeNat (n+1)).length +
          3 * (KS.W08.denseMatrixTape A).length + 7) + replayTicks A y ≤ bs.length := by
        simp only [restoreTicks, List.length_cons] at hlen
        change 1 + _ + _ ≤ _ at hlen
        dsimp only [A]
        omega
      obtain ⟨remaining, hremaining, hreturn⟩ := hb.loop_body_then replayGuard bs hbody
      dsimp only [A] at hremaining
      erw [Machine.run.eq_2, restore_step_nonempty _ _ hne]
      change (KS.W29.FixedLoop.loop popReplayProgram replayGuard).toMachine.run _ bs = _
      dsimp only [A] at hreturn
      simp only [historyTape]
      erw [hreturn]
      have hr : restoreTicks rest (schurWitnessLift M y) ≤ remaining.length := by
        simp only [restoreTicks, List.length_cons] at hlen
        omega
      exact ih (schurWitnessLift M y) remaining hr

theorem restoreAll_spec {n N : ℕ} (h : PivotHistory n N) (y : Fin n → ℚ) :
    RunSpec restoreAllProgram (state (historyTape h) [] [] [] (KS.W12.RowDot.vectorTape y))
      (state [] [] [] [] (KS.W12.RowDot.vectorTape (h.restore y))) (restoreTicks h y) := by
  intro bits hb
  exact run_restoreAll h y bits hb.ge

end KS.W17.FixedPSD

end OAI
