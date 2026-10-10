import OAI.Computability.BinPacking.Computation.MachineFiniteAlphabet

namespace OAI

namespace BinPackingGap.MachineKeepDecision

section

open Turing BinPackingGames.Foundations
open Complexity

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: rest => true :: bit :: frame rest

@[simp] theorem frame_length (word : List Bool) :
    (frame word).length = 2 * word.length + 1 := by
  induction word with
  | nil => rfl
  | cons bit rest ih => simp only [frame, List.length_cons, ih]; omega

def inputBits (p : List Bool × List Bool) : List Bool := frame p.1 ++ p.2

def outputBits (p : List Bool × Bool) : List Bool := p.2 :: p.1

def keep (decide : List Bool → Bool) (p : List Bool × List Bool) : List Bool × Bool :=
  (p.1, decide p.2)

@[simp] theorem inputBits_length (p : List Bool × List Bool) :
    (inputBits p).length = 2 * p.1.length + 1 + p.2.length := by
  simp [inputBits]

inductive ExtraTape
  | saved | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.saved, .output]

protected theorem ExtraTape.enumList_getElem?_ctorIdx_eq (x : ExtraTape) :
    ExtraTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Phase
  | parse | transfer | finish
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .transfer, .finish]

protected theorem Phase.enumList_getElem?_ctorIdx_eq (x : Phase) :
    Phase.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Symbols (M : FinTM2) :=
  MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (saved output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .saved => saved
  | .output => output

def auxProgram (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : Phase → TM2.Stmt (Symbols M) (Label M) (State M)
  | .parse => .pop (.inl M.k₀) (fun s bit => (s.1, bit))
      (.branch (fun s => input (s.2.getD (input.symm false)))
        (.pop (.inl M.k₀) (fun s bit => (s.1, bit))
          (.push (.inr .saved) (fun s => s.2.getD (input.symm false))
            (.load (fun s => (s.1, none)) (.goto (fun _ => .inr .parse)))))
        (.load (fun s => (s.1, none)) (.goto (fun _ => .inl M.main))))
  | .transfer => BinPackingGames.Reduction.MachineTransfer.loopAt
      (K := Tape M) (Λ := Label M) (σ := M.σ) (Γ := Symbols M) (.inr .saved) (.inr .output)
      id (input.symm false) (.inr .transfer) (some (.inr .finish))
  | .finish => .pop (.inl M.k₁)
      (fun s bit => (s.1, bit.map (fun b => input.symm (output b))))
      (.push (.inr .output) (fun s => s.2.getD (input.symm false))
        (.load (fun _ => (M.initialState, none)) .halt))

def program (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : Label M → TM2.Stmt (Symbols M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr .transfer)) M.m (auxProgram M input output)

def machine (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : FinTM2 where
  K := Tape M
  kFin := by letI := M.kFin; exact inferInstanceAs (Fintype (Tape M))
  k₀ := .inl M.k₀
  k₁ := .inr .output
  Γ := Symbols M
  Λ := Label M
  ΛFin := by letI := M.ΛFin; exact inferInstanceAs (Fintype (Label M))
  main := .inr .parse
  σ := State M
  σFin := by
    letI := M.σFin
    letI := M.Γk₀Fin
    exact inferInstanceAs (Fintype (State M))
  initialState := (M.initialState, none)
  Γk₀Fin := M.Γk₀Fin
  m := program M input output

def inputTapes (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    (k : Tape M) → List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M saved [])

@[simp] theorem inputTapes_input (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    inputTapes M word saved (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_saved (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    inputTapes M word saved (.inr .saved) = saved := rfl

def inputConfig (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr .parse), (M.initialState, none), inputTapes M word saved⟩

def embedded (M : FinTM2) (saved : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .transfer))
    (none : Option (M.Γ M.k₀)) (extraTapes M saved []) c

def returnTapes (M : FinTM2) (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    (k : Tape M) → List (Symbols M k) :=
  MachineEmbedding.tapes (haltList M [answer]).stk (extraTapes M [] word)

def returnConfig (M : FinTM2) (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr .finish), (M.initialState, none), returnTapes M answer word⟩

private theorem inputTapes_update_input (M : FinTM2)
    (word saved replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word saved) (.inl M.k₀) replacement =
      inputTapes M replacement saved := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

private theorem inputTapes_update_saved (M : FinTM2)
    (word saved replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word saved) (.inr .saved) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

private def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseStep_digit (bit : Bool) (word saved : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M (input.symm true :: input.symm bit :: word) saved) =
    some (inputConfig M word (input.symm bit :: saved)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState, none)
    (inputTapes M (input.symm true :: input.symm bit :: word) saved)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_saved,
    inputConfig]

theorem parseStep_end (word saved : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M (input.symm false :: word) saved) =
    some (embedded M saved (initList M word)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState, none) (inputTapes M (input.symm false :: word) saved)) = _
  simp only [auxProgram, TM2.stepAux, inputTapes_input, List.head?_cons,
    Option.getD_some, Equiv.apply_symm_apply, Bool.cond_false, List.tail_cons,
    inputTapes_update_input]
  rfl

theorem parseTrace (state : List Bool) (query saved : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[state.length + 1]
      (some (inputConfig M ((frame state).map input.symm ++ query) saved)) =
    some (embedded M (state.reverse.map input.symm ++ saved) (initList M query)) := by
  induction state generalizing saved with
  | nil =>
    simpa only [frame, List.map_singleton, List.singleton_append, List.length_nil,
      Nat.zero_add, List.reverse_nil, List.map_nil, List.nil_append,
      Function.iterate_one, MachineComposition.advance_some] using!
      parseStep_end M input output query saved
  | cons bit state ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[state.length + 1]
      ((machine M input output).step
        (inputConfig M ((frame (bit :: state)).map input.symm ++ query) saved)) = _
    simp only [frame, List.map_cons, List.cons_append]
    rw [parseStep_digit]
    simpa only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append] using! ih (input.symm bit :: saved)

private theorem inputConfig_init (word : List (M.Γ M.k₀)) :
    inputConfig M word [] = initList (machine M input output) word := by
  unfold inputConfig initList
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList, machine]; rfl
    · simp [inputTapes, initList, machine, h]
  | inr k => cases k <;> simp [inputTapes, initList, machine, extraTapes]

def decisionExecution (saved query : List (M.Γ M.k₀))
    (answer : M.Γ M.k₁) (budget : Nat)
    (run : TM2OutputsInTime M query (some [answer]) budget) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M saved (initList M query))
      (some (embedded M saved (haltList M [answer]))) budget :=
  MachineComposition.embeddedExecution (some (.inr .transfer : Label M))
    (none : Option (M.Γ M.k₀)) (extraTapes M saved []) M.m
    (auxProgram M input output) run

private theorem returnTransfer_tapes (saved : List (M.Γ M.k₀)) (answer : M.Γ M.k₁) :
    BinPackingGames.Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .saved) (.inr .output)
      (embedded M saved (haltList M [answer])).stk [] saved.reverse =
    returnTapes M answer saved.reverse := by
  funext k
  cases k with
  | inl k => simp [BinPackingGames.Reduction.MachineTransfer.tapesAt, embedded,
      MachineEmbedding.configuration, returnTapes]
  | inr k => cases k <;> simp [BinPackingGames.Reduction.MachineTransfer.tapesAt, embedded,
      MachineEmbedding.configuration, returnTapes, extraTapes]

def returnTransfer (saved : List (M.Γ M.k₀)) (answer : M.Γ M.k₁) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M saved (haltList M [answer]))
      (some (returnConfig M answer saved.reverse)) (saved.length + 1) := by
  have run := BinPackingGames.Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .saved) (.inr .output) (by intro h; cases h)
    id (input.symm false) (.inr .transfer) (some (.inr .finish))
    (program M input output) rfl
    (embedded M saved (haltList M [answer])).stk M.initialState none
  have hs : (embedded M saved (haltList M [answer])).stk (.inr .saved) = saved := rfl
  have hd : (embedded M saved (haltList M [answer])).stk (.inr .output) = [] := rfl
  rw [hs, hd, List.map_id, List.append_nil, returnTransfer_tapes] at run
  exact run

private theorem finish_tapes (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    Function.update
      (Function.update (returnTapes M answer word) (.inl M.k₁) [])
      (.inr .output) (input.symm (output answer) :: word) =
    (haltList (machine M input output) (input.symm (output answer) :: word)).stk := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [returnTapes, haltList, machine]
    · simp [returnTapes, haltList, machine, h]
  | inr k =>
    cases k <;> simp [returnTapes, haltList, machine, extraTapes]
    rfl

theorem finishStep (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    (machine M input output).step (returnConfig M answer word) =
    some (haltList (machine M input output) (input.symm (output answer) :: word)) := by
  have ha : returnTapes M answer word (.inl M.k₁) = [answer] := by
    simp [returnTapes, haltList]
  have hw : returnTapes M answer word (.inr .output) = word := rfl
  change some (TM2.stepAux (auxProgram M input output .finish)
    (M.initialState, none) (returnTapes M answer word)) = _
  simp only [auxProgram, TM2.stepAux, ha, List.head?_cons, List.tail_cons,
    Option.map_some, Option.getD_some]
  have hw' : (Function.update (returnTapes M answer word) (.inl M.k₁) [])
      (.inr .output) = word := by simp [hw]
  rw [hw', finish_tapes]
  rfl

def outputsInTime (state query : List Bool) (answer : Bool) (budget : Nat)
    (run : TM2OutputsInTime M (query.map input.symm)
      (some [output.symm answer]) budget) :
    TM2OutputsInTime (machine M input output)
      ((frame state ++ query).map input.symm)
      (some ((answer :: state).map input.symm))
      (budget + 2 * state.length + 3) := by
  let parsed : StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M ((frame state).map input.symm ++ query.map input.symm) [])
      (some (embedded M (state.reverse.map input.symm)
        (initList M (query.map input.symm)))) (state.length + 1) := {
    steps := state.length + 1
    evals_in_steps := by
      change (MachineComposition.advance (machine M input output).step)^[state.length + 1] _ = _
      simpa only [List.append_nil] using!
        parseTrace M input output state (query.map input.symm) []
    steps_le_m := le_refl _ }
  have decision := decisionExecution M input output (state.reverse.map input.symm)
    (query.map input.symm) (output.symm answer) budget run
  have transfer := returnTransfer M input output (state.reverse.map input.symm)
    (output.symm answer)
  have restored : (state.reverse.map input.symm).reverse = state.map input.symm := by
    rw [List.map_reverse, List.reverse_reverse]
  rw [restored, List.length_map, List.length_reverse] at transfer
  have finish := oneStep _ _ _ (finishStep M input output
    (output.symm answer) (state.map input.symm))
  simp only [Equiv.apply_symm_apply] at finish
  have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parsed decision
  have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first transfer
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second finish
  rw [inputConfig_init] at full
  simp only [← List.map_append] at full
  refine { toEvalsTo := full.toEvalsTo, steps_le_m := ?_ }
  have h := full.steps_le_m
  omega

theorem machine_finiteAlphabet (finite : MachineFiniteAlphabet.FiniteAlphabet M) :
    MachineFiniteAlphabet.FiniteAlphabet (machine M input output) := by
  intro k
  cases k with
  | inl k => exact finite k
  | inr _ => exact MachineFiniteAlphabet.input_finite M

noncomputable def computation (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide) :
    TM2ComputableInPolyTime inputBits outputBits (keep decide) where
  tm := machine certificate.tm certificate.inputAlphabet certificate.outputAlphabet
  inputAlphabet := certificate.inputAlphabet
  outputAlphabet := certificate.inputAlphabet
  time := certificate.time + Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun pair := by
    have run := outputsInTime certificate.tm certificate.inputAlphabet
      certificate.outputAlphabet pair.1 pair.2 (decide pair.2)
      (certificate.time.eval pair.2.length) (certificate.outputsFun pair.2)
    have hq : pair.2.length ≤ (inputBits pair).length := by
      rw [inputBits_length]; omega
    have hs : pair.1.length ≤ (inputBits pair).length := by
      rw [inputBits_length]; omega
    have ht := MachineComposition.natPolynomial_eval_mono certificate.time hq
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    have hr := run.steps_le_m
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

theorem computation_finiteAlphabet (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide)
    (finite : MachineFiniteAlphabet.FiniteAlphabet certificate.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation decide certificate).tm :=
  machine_finiteAlphabet certificate.tm certificate.inputAlphabet certificate.outputAlphabet finite

end

open Turing BinPackingGames.Foundations.Complexity

def typedInputBits {α : Type} (encode : α → List Bool) (p : α × List Bool) : List Bool :=
  inputBits (encode p.1, p.2)

def typedOutputBits {α : Type} (encode : α → List Bool) (p : α × Bool) : List Bool :=
  p.2 :: encode p.1

def typedKeep {α : Type} (decide : List Bool → Bool) (p : α × List Bool) : α × Bool :=
  (p.1, decide p.2)

noncomputable def computationWithSavedCodec {α : Type} (encode : α → List Bool)
    (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide) :
    TM2ComputableInPolyTime (typedInputBits encode) (typedOutputBits encode)
      (typedKeep decide) where
  tm := (computation decide certificate).tm
  inputAlphabet := (computation decide certificate).inputAlphabet
  outputAlphabet := (computation decide certificate).outputAlphabet
  time := (computation decide certificate).time
  outputsFun p := (computation decide certificate).outputsFun (encode p.1, p.2)

theorem computationWithSavedCodec_finiteAlphabet {α : Type} (encode : α → List Bool)
    (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide)
    (finite : MachineFiniteAlphabet.FiniteAlphabet certificate.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computationWithSavedCodec encode decide certificate).tm :=
  computation_finiteAlphabet decide certificate finite

end BinPackingGap.MachineKeepDecision

end OAI
