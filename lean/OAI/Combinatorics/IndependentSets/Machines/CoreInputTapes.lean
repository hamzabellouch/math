import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.OldSelectSteps

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow
open Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]

theorem coreCleaned_memory (graph : List Bool) (x v i k o m : Nat)
    (rotor output query scan flat localIndex returnPort selected : List Bool) :
    coreCleaned (coreMemory graph x v i k o m rotor output query scan flat
      localIndex returnPort selected) =
      coreMemory graph x v i k o m rotor output [] [] [] [] [] [] := by
  funext z
  fin_cases z <;> rfl

theorem coreCleanupSteps_memory (graph : List Bool) (x v i k o m : Nat)
    (rotor output scan : List Bool) (j r z : Nat) :
    coreCleanupSteps (coreMemory graph x v i k o m rotor output
      (encodeWord 0) scan (encodeWord 0) (encodeWord j) (encodeWord r) (encodeWord z)) =
      scan.length + j + r + z + 15 := by
  change (encodeWord 0).length + scan.length + (encodeWord 0).length +
    (encodeWord j).length + (encodeWord r).length + (encodeWord z).length +
    ([] : List Bool).length + ([] : List Bool).length + ([] : List Bool).length +
    ([] : List Bool).length + 10 = _
  simp only [encodeWord_length, List.length_nil]
  omega

theorem coreRotorFinalFrame {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (graph : List Bool) (x v k o m : Nat) (output : List Bool) :
    rotorFinalTapes table i p coreRotorTapes
      (coreMemory graph x v i.val k o m
        (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []) =
    coreMemory graph x v i.val k o m
      (encodeWords (ExpanderTableWords.rotationWords table)) output (encodeWord 0)
      (encodeWords ((ExpanderTableWords.rotationWords table).drop (q * i.val + p.val + 1)))
      (encodeWord 0) (encodeWord (ExpanderTables.lookup table (i, p)).1.val)
      (encodeWord (ExpanderTables.lookup table (i, p)).2.val) [] := by
  funext z
  fin_cases z <;>
    simp [rotorFinalTapes, coreRotorTapes, rotorLookupTapes, coreMemory,
      MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes, MachineCopy.forkTapes,
      MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes, MachineLookup.tapes]

theorem coreRotorTrace {n q : Nat} (positive : 0 < q) (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (graph : List Bool) (x v k o m : Nat) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[rotorSteps table i p]
      (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
        coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []⟩) =
      some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
        coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output (encodeWord 0)
          (encodeWords ((ExpanderTableWords.rotationWords table).drop (q * i.val + p.val + 1)))
          (encodeWord 0) (encodeWord (ExpanderTables.lookup table (i, p)).1.val)
          (encodeWord (ExpanderTables.lookup table (i, p)).2.val) []⟩ := by
  let e := coreRotorStateEquiv σ q
  let backwards := MachineStateEquiv.program e.symm program
  have atRotor (l : RotorLabel q) :
      backwards (labels (.rotor l)) = rotorInstruction q positive p coreRotorTapes
        (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan))))) l := by
    change MachineStateEquiv.statement e.symm (program (labels (.rotor l))) = _
    rw [code]
    exact MachineStateEquiv.statement_symm_statement e _
  have run := rotorTrace positive table i p coreRotorTapes coreRotorTapes_injective
    (fun l => labels (.rotor l)) (some (labels (.select (.inr (.compare .scan)))))
    backwards atRotor
    (coreMemory graph x v i.val k o m
      (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] [])
    rfl rfl rfl rfl rfl rfl
    ((ambient, MachineFixedBlockMap.emptyBuffer 4096), (false, MachineCloudSelect.Phase.checking)) none
  have h := MachineStateEquiv.trace e backwards _ _ _ run
  have backForward : MachineStateEquiv.program e backwards = program := by
    have hp := MachineStateEquiv.program_symm_program e.symm program
    simpa only [Equiv.symm_symm, backwards] using hp
  rw [backForward] at h
  change (advance (TM2.step program))^[rotorSteps table i p]
    (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
      coreMemory graph x v i.val k o m
        (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] []⟩) =
    some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
      rotorFinalTapes table i p coreRotorTapes
        (coreMemory graph x v i.val k o m
          (encodeWords (ExpanderTableWords.rotationWords table)) output [] [] [] [] [] [])⟩ at h
  rw [coreRotorFinalFrame] at h
  exact h

theorem coreSelectFrame (graph : List Bool) (x v i k o m j : Nat)
    (rotor output query scan flat returnPort selected : List Bool) :
    MachineCloudPadding.Placement.tapes coreSelectView
      (selectMemory graph j v k o m [] selected [] [] [] [])
      (coreMemory graph x v i k o m rotor output query scan flat (encodeWord j) returnPort []) =
      coreMemory graph x v i k o m rotor output query scan flat (encodeWord j) returnPort selected := by
  funext z
  fin_cases z <;> rfl

theorem coreSelectionTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (j : Fin (PreprocessingCloudIndex.cloudSize t v + padding v))
    (x i : Nat) (rotor output query scan flat returnPort : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[selectionSteps t padding v j]
      (some ⟨some (labels (.select (.inr (.compare .scan)))), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) x v.val i (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
          (encodeWord j.val) returnPort []⟩) =
      some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
        coreMemory (GraphTables.tableBits t) x v.val i (PreprocessingCloudIndex.cloudSize t v)
          (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
          (encodeWord j.val) returnPort
          (encodeWord (PreprocessingInternalRows.selectedIndex t padding v j))⟩ := by
  let e := coreSelectStateEquiv σ q
  let state := (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    MachineFixedDivMod.residue q positive 0))
  have sourceRun := selectionTrace t padding v j state none
  have moved := MachineStateEquiv.trace e selectProgram _ _ _ sourceRun
  let base := coreMemory (GraphTables.tableBits t) x v.val i
    (PreprocessingCloudIndex.cloudSize t v)
    (PreprocessingPaddingOffsets.offset padding v.val) t.darts rotor output query scan flat
    (encodeWord j.val) returnPort []
  have placed := MachineCloudPadding.Placement.trace coreSelectTape coreSelectView
    coreSelectView_left coreSelectView_right (fun l => labels (.select l))
    (some (labels (.finish .seedReturn))) base
    (MachineStateEquiv.program e selectProgram) program (fun l => code (.select l))
    _ _ _ moved
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    MachineStateEquiv.configuration, base, coreSelectFrame] at placed
  convert placed using 1 <;> rfl

theorem coreFinishTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (graph : List Bool) (x v i k o m j r z : Nat)
    (rotor output query scan flat : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[finishSteps q x z r output.length]
      (some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor output query scan flat
          (encodeWord j) (encodeWord r) (encodeWord z)⟩) =
      some ⟨some (labels (.cleanup 0)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor (output ++ emittedBits q x z r) query scan flat
          (encodeWord j) (encodeWord r) (encodeWord z)⟩ := by
  have h := finishTrace q coreFinishTapes coreFinishTapes_injective
    (fun l => labels (.finish l)) (some (labels (.cleanup 0))) program
    (fun l => code (.finish l))
    (coreMemory graph x v i k o m rotor output query scan flat
      (encodeWord j) (encodeWord r) (encodeWord z))
    x z r rfl rfl rfl rfl rfl rfl rfl
    (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
      (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking)))) none
  change (advance (TM2.step program))^[finishSteps q x z r output.length]
    (some ⟨some (labels (.finish .seedReturn)), coreInitialState q positive ambient,
      coreMemory graph x v i k o m rotor output query scan flat
        (encodeWord j) (encodeWord r) (encodeWord z)⟩) =
    some ⟨some (labels (.cleanup 0)), coreInitialState q positive ambient,
      Function.update (coreMemory graph x v i k o m rotor output query scan flat
        (encodeWord j) (encodeWord r) (encodeWord z)) (8 : CoreTape)
        (output ++ emittedBits q x z r)⟩ at h
  rw [coreMemory_update_output] at h
  exact h

def coreInputTapes (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (output : List Bool) : CoreTape → List Bool :=
  coreMemory (GraphTables.tableBits t)
    (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
    (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
    (PreprocessingCloudIndex.cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables v))) output [] [] [] [] [] []

def coreSteps (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (p : Fin q) (outputLength : Nat) : Nat :=
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let selected := PreprocessingInternalRows.selectedIndex t padding v step.1
  let suffixBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  rotorSteps (tables v) rank p + selectionSteps t padding v step.1 +
    finishSteps q (PreprocessingRegularTables.vertexOrder t padding x.val).val
      selected step.2.val outputLength +
    (suffixBits.length + step.1.val + step.2.val + selected + 15)

theorem coreTrace (q : Nat) (positive : 0 < q) (p : Fin q)
    (labels : CoreLabel q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = coreInstruction q positive p labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[coreSteps t padding tables v x p output.length]
      (some ⟨some (labels (coreEntry q)), coreInitialState q positive ambient,
        coreInputTapes t padding tables v x output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v x
          (output ++ encodeWords (GraphTables.rowWords
            (PreprocessingInternalRows.row t padding tables v x p)))⟩ := by
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let z := PreprocessingInternalRows.selectedIndex t padding v step.1
  let X := (PreprocessingRegularTables.vertexOrder t padding x.val).val
  let o := PreprocessingPaddingOffsets.offset padding v.val
  let bits := encodeWords (ExpanderTableWords.rotationWords (tables v))
  let tailBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  let graph := GraphTables.tableBits t
  let k := PreprocessingCloudIndex.cloudSize t v
  have hr := coreRotorTrace positive (tables v) rank p labels exit program code
    graph X v.val k o t.darts output ambient
  have hs := coreSelectionTrace q positive p labels exit program code t padding v step.1
    X rank.val bits output (encodeWord 0) tailBits (encodeWord 0) (encodeWord step.2.val) ambient
  have hf := coreFinishTrace q positive p labels exit program code
    graph X v.val rank.val k o t.darts step.1.val step.2.val z bits output
    (encodeWord 0) tailBits (encodeWord 0) ambient
  have hc := coreCleanupTrace q positive p labels exit program code
    (coreMemory graph X v.val rank.val k o t.darts bits
      (output ++ emittedBits q X z step.2.val)
      (encodeWord 0) tailBits (encodeWord 0) (encodeWord step.1.val)
      (encodeWord step.2.val) (encodeWord z))
    (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
      (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking))))
  rw [coreCleanupSteps_memory, coreCleaned_memory] at hc
  have h := joinTrace (joinTrace (joinTrace hr hs) hf) hc
  have hbits : emittedBits q X z step.2.val =
      encodeWords (GraphTables.rowWords (PreprocessingInternalRows.row t padding tables v x p)) :=
    emittedBits_eq_row t padding tables v x p
  rw [hbits] at h
  exact h

theorem selectedIndex_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) :
    PreprocessingInternalRows.selectedIndex t padding v i ≤
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + i.val := by
  unfold PreprocessingInternalRows.selectedIndex
  split
  · rename_i hi
    have h := (PreprocessingCloudIndex.cloudSelect t v ⟨i.val, hi⟩).val.isLt
    omega
  · omega

theorem encodedDrop_length_le (values : List Nat) (n : Nat) :
    (encodeWords (values.drop n)).length ≤ (encodeWords values).length := by
  have h : (encodeWords (values.take n)).length + (encodeWords (values.drop n)).length =
      (encodeWords values).length := by
    rw [← List.length_append, ← encodeWords_append, List.take_append_drop]
  omega

theorem rotorSize_le_encodedLength {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) :
    n ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
  have h : n * q ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  exact (Nat.le_mul_of_pos_right n positive).trans h

def coreTimeBound (q graphLength rotorLength x v i k o m outputLength : Nat) : Nat :=
  (5 * q + 32) * rotorLength + 10 * graphLength + 2 * i + 13 * v + 5 * k +
    (5 * q + 10) * (m + o) + 4 * x + 2 * outputLength + 8 * q + 41066

theorem coreSteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (p : Fin q) (outputLength : Nat) :
    coreSteps t padding tables v x p outputLength ≤
      coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
        (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
        (PreprocessingCloudIndex.cloudSize t v)
        (PreprocessingPaddingOffsets.offset padding v.val) t.darts outputLength := by
  let rank := PreprocessingCloudIndex.paddedCloudRank t padding v x
  let step := ExpanderTables.lookup (tables v) (rank, p)
  let z := PreprocessingInternalRows.selectedIndex t padding v step.1
  let X := (PreprocessingRegularTables.vertexOrder t padding x.val).val
  let o := PreprocessingPaddingOffsets.offset padding v.val
  let L := (GraphTables.tableBits t).length
  let R := (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
  let k := PreprocessingCloudIndex.cloudSize t v
  let tailBits := encodeWords ((ExpanderTableWords.rotationWords (tables v)).drop
    (q * rank.val + p.val + 1))
  have hN : k + padding v ≤ R := rotorSize_le_encodedLength positive (tables v)
  have hj : step.1.val ≤ R := step.1.isLt.le.trans hN
  have hr : step.2.val ≤ q := step.2.isLt.le
  have hz : z ≤ t.darts + o + R := by
    have h := selectedIndex_le t padding v step.1
    change z ≤ t.darts + o + step.1.val at h
    omega
  have hsize : (k + padding v) * q ≤ R := by
    dsimp only [R, k]
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  have hrotor : rotorSteps (tables v) rank p ≤ 2 * rank.val + 6 * R + 8 := by
    have h := rotorSteps_le (tables v) rank p
    change rotorSteps (tables v) rank p ≤ 2 * rank.val + 5 * R + (k + padding v) * q + 8 at h
    omega
  have hselect : selectionSteps t padding v step.1 ≤
      10 * L + 16 * R + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57 := by
    have h := selectionSteps_le t padding v step.1
    change selectionSteps t padding v step.1 ≤
      10 * L + 16 * step.1.val + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57 at h
    omega
  have hfinish : finishSteps q X z step.2.val outputLength ≤
      (5 * q + 7) * (t.darts + o + R) + 7 * q + 4 * X + 2 * outputLength + 40986 := by
    have h := finishSteps_le q X z step.2.val outputLength
    have hm := Nat.mul_le_mul_left (5 * q + 7) hz
    omega
  have htail : tailBits.length ≤ R := encodedDrop_length_le
    (ExpanderTableWords.rotationWords (tables v)) (q * rank.val + p.val + 1)
  have hcleanup : tailBits.length + step.1.val + step.2.val + z + 15 ≤
      R + R + q + (t.darts + o + R) + 15 := by omega
  calc
    coreSteps t padding tables v x p outputLength
        ≤ (2 * rank.val + 6 * R + 8) +
          (10 * L + 16 * R + 13 * v.val + 5 * k + 2 * o + 2 * t.darts + 57) +
          ((5 * q + 7) * (t.darts + o + R) + 7 * q + 4 * X + 2 * outputLength + 40986) +
          (R + R + q + (t.darts + o + R) + 15) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hrotor hselect) hfinish) hcleanup
    _ = _ := by
      change _ = coreTimeBound q L R X v.val rank.val k o t.darts outputLength
      unfold coreTimeBound
      ring

def coreMachineInTime (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PreprocessingCloudIndex.PaddedCloud t padding v)
    (p : Fin q) (output : List Bool) :
    StateTransition.EvalsToInTime (coreMachine q positive p).step
      ⟨some (coreEntry q), coreInitialState q positive (), coreInputTapes t padding tables v x output⟩
      (some ⟨none, coreInitialState q positive (), coreInputTapes t padding tables v x
        (output ++ encodeWords (GraphTables.rowWords (PreprocessingInternalRows.row t padding tables v x p)))⟩)
      (coreTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (PreprocessingRegularTables.vertexOrder t padding x.val).val v.val
        (PreprocessingCloudIndex.paddedCloudRank t padding v x).val
        (PreprocessingCloudIndex.cloudSize t v)
        (PreprocessingPaddingOffsets.offset padding v.val) t.darts output.length) where
  steps := coreSteps t padding tables v x p output.length
  evals_in_steps := coreTrace q positive p id none (coreMachine q positive p).m
    (fun _ => rfl) t padding tables v x output ()
  steps_le_m := coreSteps_le q positive t padding tables v x p output.length

end IndependentSetsGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
