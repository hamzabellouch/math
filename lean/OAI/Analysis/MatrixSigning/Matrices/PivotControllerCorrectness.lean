import Mathlib
import OAI.Analysis.MatrixSigning.Machines.TerminalInputBounds
import OAI.Analysis.MatrixSigning.Matrices.PivotControllerLoop

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def witnessState {N : ℕ} (q : Option (Fin N → ℚ)) : Fin 35 → List Bool :=
  state [] [] [] [] (q.elim [] KS.W12.RowDot.vectorTape)

theorem run_controller {n N : ℕ} (h : PivotHistory n N) (M : DenseRatMatrix n)
    (bits : List Bool) (hlen : controllerTicks h M ≤ bits.length) :
    controllerProgram.toMachine.run (controllerConfig (matrixState (historyTape h) M)) bits =
      ⟨none,witnessState ((uniformNegativeWitness n (DenseRatMatrix.decode M)).map h.restore)⟩ := by
  induction n generalizing N bits with
  | zero =>
    have hclear := controller_run_clear (historyTape h) bits hlen
    simp [matrixState,uniformNegativeWitness,witnessState,
      KS.W08.denseMatrixTape,KS.W08.denseMatrixPayloads,Computability.encodeNat] at hclear ⊢
    exact hclear
  | succ n ih =>
    have hnum : ∀ i j, (DenseRatMatrix.decode M i j).num.natAbs ≤ 2^(localBits M) :=
      fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload M i j).1
    have hden : ∀ i j, (DenseRatMatrix.decode M i j).den ≤ 2^(localBits M) :=
      fun i j => (KS.W19.TerminalWitnessMachine.entry_parts_le_payload M i j).2
    have hN : 0<N := by have hd := h.dimension_depth; omega
    have descend (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
        controllerProgram.toMachine.run (controllerConfig (matrixState (historyTape h) M)) bits =
          ⟨none,witnessState ((uniformNegativeWitness (n+1) (DenseRatMatrix.decode M)).map h.restore)⟩ := by
      have hb := body_descend_spec (historyTape h) M (localBits M) hnum hden ht
      have hbudget := controllerTicks_descend h M ht
      cases bits with
      | nil => simp only [List.length_nil] at hlen; rw [hbudget] at hlen; omega
      | cons coin bs =>
        have hbnd : PivotDecision.ticks M (localBits M)+(descentTicks M (localBits M)+1) ≤ bs.length := by
          rw [hbudget] at hlen
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨remaining,hr,hreturn⟩ := hb.loop_body_then controllerGuard bs hbnd
        erw [Machine.run.eq_2,controller_step_call]
        change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.run _ bs = _
        erw [hreturn]
        have hremain : controllerTicks (.push (DenseRatMatrix.decode M) h) (child M) ≤ remaining.length := by
          rw [hbudget] at hlen
          simp only [List.length_cons] at hlen
          omega
        have hrec := ih (N:=N) (h:=PivotHistory.push (DenseRatMatrix.decode M) h)
          (M:=child M) (bits:=remaining) hremain
        simp [historyTape,DenseRatMatrix.ofMatrix_decode,uniformNegativeWitness,ht,
          witnessState,Option.map_map,Function.comp_def,PivotHistory.restore,child] at hrec ⊢
        exact hrec
    by_cases hn : DenseRatMatrix.decode M 0 0 < 0
    · have hb := body_negative_spec h M (localBits M) hnum hden hn
      cases bits with
      | nil => simp [controllerTicks,hn] at hlen
      | cons coin bs =>
        have hbnd : PivotDecision.ticks M (localBits M)+
            (((2+unitTicks n)+1+finishTicks h M (Pi.single 0 1))+1) ≤ bs.length := by
          simp only [controllerTicks,hn,ite_true,List.length_cons] at hlen
          omega
        obtain ⟨remaining,hr,hreturn⟩ := hb.loop_body_then controllerGuard bs hbnd
        erw [Machine.run.eq_2,controller_step_call]
        change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.run _ bs = _
        erw [hreturn]
        have hremain : 1≤remaining.length := by
          simp only [controllerTicks,hn,ite_true,List.length_cons] at hlen
          omega
        cases remaining with
        | nil => simp at hremain
        | cons c cs =>
          change controllerProgram.toMachine.run
            (controllerConfig (state [] [] [] []
              (KS.W12.RowDot.vectorTape (h.restore (Pi.single 0 1))))) (c :: cs) = _
          erw [Machine.run.eq_2,controller_step_finished _ (vectorTape_nonempty hN _),Machine.run_halted _ _ rfl]
          simp [witnessState,uniformNegativeWitness,pivotTerminal,hn]
    · by_cases hz : DenseRatMatrix.decode M 0 0 = 0
      · cases hf : firstNonzeroOffDiagonal (DenseRatMatrix.decode M) with
        | none => exact descend (by simp [pivotTerminal,hz,hf])
        | some j =>
          have hb := body_sparse_spec h M (localBits M) hnum hden j hz hf
          cases bits with
          | nil => simp [controllerTicks,hz,hf] at hlen
          | cons coin bs =>
            have hbnd : PivotDecision.ticks M (localBits M)+
                (((2+KS.W19.TerminalWitnessMachine.ticks (historyTape h) M (localBits M) j.succ)+1+
                  finishTicks h M (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ))+1) ≤ bs.length := by
              simp only [controllerTicks,hz,lt_self_iff_false,ite_true,ite_false,hf,List.length_cons] at hlen
              omega
            obtain ⟨remaining,hr,hreturn⟩ := hb.loop_body_then controllerGuard bs hbnd
            erw [Machine.run.eq_2,controller_step_call]
            change (KS.W29.FixedLoop.loop controllerBody controllerGuard).toMachine.run _ bs = _
            erw [hreturn]
            have hremain : 1≤remaining.length := by
              simp only [controllerTicks,hz,lt_self_iff_false,ite_true,ite_false,hf,List.length_cons] at hlen
              omega
            cases remaining with
            | nil => simp at hremain
            | cons c cs =>
              change controllerProgram.toMachine.run
                (controllerConfig (state [] [] [] []
                  (KS.W12.RowDot.vectorTape
                    (h.restore (zeroPivotWitness (DenseRatMatrix.decode M) 0 j.succ)))))
                (c :: cs) = _
              erw [Machine.run.eq_2,controller_step_finished _ (vectorTape_nonempty hN _),Machine.run_halted _ _ rfl]
              simp [witnessState,uniformNegativeWitness,pivotTerminal,hz,hf]
      · exact descend (by simp [pivotTerminal,hn,hz])

theorem controller_spec (n : ℕ) (M : DenseRatMatrix n) :
    RunSpec controllerProgram (matrixState [] M)
      (witnessState (rationalNegativeWitness n (DenseRatMatrix.decode M)))
      (controllerTicks (.nil n) M) := by
  intro bits hb
  have h := run_controller (.nil n) M bits hb.ge
  simp [historyTape,PivotHistory.restore,uniformNegativeWitness_eq] at h ⊢
  exact h

end KS.W17.FixedPSD

end OAI
