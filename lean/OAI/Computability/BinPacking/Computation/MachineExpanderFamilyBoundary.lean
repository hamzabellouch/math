import OAI.Computability.BinPacking.Computation.MachineExpanderFamilyAffine

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem caller_initialState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) : caller (initialState positive H ambient) = ambient := rfl

@[simp] theorem caller_normalizeState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (normalizeState positive H state) = caller state := rfl

@[simp] theorem clearRegister_initialState (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) :
    clearRegister (initialState positive H ambient) = initialState positive H ambient := rfl

theorem boundaryTapes_update_level (remaining current next : Nat)
    (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      (.inr .remainingLevel) (encodeWord next ++ suffix) =
      boundaryTapes next current word suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
    · cases extra <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraFrame, MachineEmbedding.tapes, Function.update]

theorem initialTapes_initialize (level : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (initialTapes level suffix) tableTape (initialEncoding d))
      (.inr .currentSize) (encodeWord 1) =
      boundaryTapes level 1 (initialEncoding d) suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
    · cases extra <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
  · cases extra <;> simp [initialTapes, boundaryTapes, extraFrame,
      MachineEmbedding.tapes, Function.update, tableTape]

variable [Fintype ρ]

theorem actualStep_of_boolStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : TM2.step (boolView positive H growth) start = some finish) :
    TM2.step (program positive H growth)
      (MachineAlphabetTransport.configuration alphabet_eq.symm start) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.step_simulation alphabet_eq.symm
    (boolView positive H growth) start
  rw [run] at h
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip,
    Option.map_some] using h

theorem bool_initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .initialize), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .initialize)) state base) = _
  rw [boolView_outer]
  simp only [boolOuterStatement, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, TM2.stepAux]
  rfl

theorem bool_levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord, List.replicate_succ]

theorem bool_levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord]

theorem bool_doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .done)) state base) = _
  rw [boolView_outer]
  rfl

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .initialize), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_initializeStep positive H growth (toBoolTapes base) state)
  simp only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool] at h
  exact h

theorem levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_succStep positive H growth (toBoolTapes base) state
      remaining suffix counter)
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    boolWord] using h

theorem levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_zeroStep positive H growth (toBoolTapes base) state suffix counter)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_doneStep positive H growth (toBoolTapes base) state)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) (suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .initialize), state, initialTapes level suffix⟩ =
      some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        boundaryTapes level 1 (initialEncoding d) suffix⟩ := by
  have h := initializeStep positive H growth (initialTapes level suffix) state
  have ht : initialTapes level suffix (.inl (.inl .table)) = [] := rfl
  have hc : initialTapes level suffix (.inr .currentSize) = [] := rfl
  simp only [ht, hc, List.append_nil, normalizeState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize level suffix))

theorem levelGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (remaining current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes (remaining + 1) current word suffix⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        boundaryTapes remaining current word suffix⟩ := by
  simpa only [boundaryTapes_update_level] using
    levelGuard_succStep positive H growth
      (boundaryTapes (remaining + 1) current word suffix) state remaining suffix rfl

theorem levelGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes 0 current word suffix⟩ =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes 0 current word suffix⟩ :=
  levelGuard_zeroStep positive H growth
    (boundaryTapes 0 current word suffix) state suffix rfl

end BinPackingGames.Foundations.Complexity.MachineExpanderFamily

end OAI
