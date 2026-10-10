import OAI.Computability.BinPacking.Search.SearchInitialItemsMachine

namespace OAI

namespace BinPackingGap.ExtensionValidationMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

def validRows (bins : Nat) : RawInstance → List Nat → Bool
  | [], [] => true
  | (numerator, denominator) :: items, label :: assignments =>
      decide (0 < numerator) && (decide (numerator ≤ denominator) &&
        (decide (label < bins) && validRows bins items assignments))
  | _, _ => false

theorem validRows_eq (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    validRows bins items assignments =
      (ExtensionCertificate.validItems items &&
        (decide (assignments.length = items.length) &&
          assignments.all (fun label => decide (label < bins)))) := by
  induction items generalizing assignments with
  | nil => cases assignments <;> simp [validRows, ExtensionCertificate.validItems]
  | cons item items ih =>
      rcases item with ⟨numerator, denominator⟩
      cases assignments <;>
        simp [validRows, ExtensionCertificate.validItems, ih, Bool.and_assoc,
          Bool.and_comm, Bool.and_left_comm]

inductive ScanCall
  | bins | numerator | denominator | assigned
  deriving DecidableEq

protected abbrev ScanCall.enumList : List ScanCall := [.bins, .numerator, .denominator, .assigned]

protected theorem ScanCall.enumList_getElem?_ctorIdx_eq (x : ScanCall) :
    ScanCall.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem ScanCall.enumList_nodup : ScanCall.enumList.Nodup := by decide

instance : Fintype ScanCall where
  elems := ⟨ScanCall.enumList, ScanCall.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev ScanPhase := ExtensionNatMachine.Label

inductive OrderCall
  | fraction | bound
  deriving DecidableEq

protected abbrev OrderCall.enumList : List OrderCall := [.fraction, .bound]

protected theorem OrderCall.enumList_getElem?_ctorIdx_eq (x : OrderCall) :
    OrderCall.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem OrderCall.enumList_nodup : OrderCall.enumList.Nodup := by decide

instance : Fintype OrderCall where
  elems := ⟨OrderCall.enumList, OrderCall.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Control
  | boundEnd | marker | positive | clearNumerator | clearDenominator | clearAssigned
  | endCheck | accept | reject
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.boundEnd, .marker, .positive,
  .clearNumerator, .clearDenominator, .clearAssigned, .endCheck, .accept, .reject]

protected theorem Control.enumList_getElem?_ctorIdx_eq (x : Control) :
    Control.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | control (phase : Control)
  | number (call : ScanCall) (phase : ScanPhase)
  | order (call : OrderCall) (phase : BinaryOrderMachine.PreserveLabel)
  deriving DecidableEq, Fintype

abbrev Tape := Fin 10
abbrev Alphabet (_ : Tape) := Bool
abbrev State := BinaryAddMachine.State (Unit × Ordering)

def clean : State := BinaryAddMachine.clean ((), .eq)

def scanSource : ScanCall → Tape
  | .bins => 0
  | .numerator | .denominator => 1
  | .assigned => 2

def scanOutput : ScanCall → Tape
  | .bins => 3
  | .numerator => 4
  | .denominator => 5
  | .assigned => 6

def scanTape (call : ScanCall) : Fin 3 → Tape
  | 0 => scanSource call
  | 1 => scanOutput call
  | _ => 7

def scanPorts (call : ScanCall) : Fin 3 ↪ Tape :=
  ⟨scanTape call, by
    intro i j h
    cases call <;> fin_cases i <;> fin_cases j <;>
      simp_all [scanTape, scanSource, scanOutput]⟩

@[simp] private theorem scanPorts_apply (call : ScanCall) (i : Fin 3) :
    scanPorts call i = scanTape call i := by
  simp only [scanPorts]
  rfl

def orderTape (call : OrderCall) : Fin 5 → Tape
  | 0 => match call with | .fraction => 4 | .bound => 6
  | 1 => match call with | .fraction => 5 | .bound => 3
  | 2 => 8
  | 3 => 9
  | _ => 7

def orderPorts (call : OrderCall) : Fin 5 ↪ Tape :=
  ⟨orderTape call, by
    intro i j h
    cases call <;> fin_cases i <;> fin_cases j <;> simp_all [orderTape]⟩

def scanSuccess : ScanCall → Label
  | .bins => .control .boundEnd
  | .numerator => .control .positive
  | .denominator => .order .fraction .leftOut
  | .assigned => .order .bound .leftOut

def orderExit : OrderCall → Ordering → Option Label
  | .fraction, .lt | .fraction, .eq => some (.number .assigned .scan)
  | .fraction, .gt => some (.control .reject)
  | .bound, .lt => some (.control .clearNumerator)
  | .bound, .eq | .bound, .gt => some (.control .reject)

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => clean) (.goto fun _ => label)

def controlInstruction : Control → TM2.Stmt Alphabet Label State
  | .boundEnd => .pop 0 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isNone)
        (jump (.control .marker)) (jump (.control .reject)))
  | .marker => .pop 1 (fun state head => ((state.1.1, head), state.2))
      (.pop 2 (fun state head => (state.1, head))
        (.branch (fun state => state.1.2.isSome && state.2.isSome)
          (.branch (fun state => decide (state.1.2 = state.2))
            (.branch (fun state => state.2.getD false)
              (jump (.number .numerator .scan)) (jump (.control .endCheck)))
            (jump (.control .reject)))
          (jump (.control .reject))))
  | .positive => .pop 4 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.push 4 (fun state => state.2.getD false) (jump (.number .denominator .scan)))
        (jump (.control .reject)))
  | .clearNumerator => MachineDrain.drain 4 (.control .clearNumerator)
      (some (.control .clearDenominator))
  | .clearDenominator => MachineDrain.drain 5 (.control .clearDenominator)
      (some (.control .clearAssigned))
  | .clearAssigned => MachineDrain.drain 6 (.control .clearAssigned)
      (some (.control .marker))
  | .endCheck => .pop 1 (fun state head => ((state.1.1, head), state.2))
      (.pop 2 (fun state head => (state.1, head))
        (.branch (fun state => state.1.2.isNone && state.2.isNone)
          (jump (.control .accept)) (jump (.control .reject))))
  | .accept => .push 0 (fun _ => true) .halt
  | .reject => .push 0 (fun _ => false) .halt

def program : Label → TM2.Stmt Alphabet Label State
  | .control phase => controlInstruction phase
  | .number call phase => ExtensionNatMachine.statement (scanPorts call)
      (Label.number call) (some (scanSuccess call)) (some (.control .reject)) phase
  | .order call phase => ExtensionNatMachine.orderStatement (orderPorts call)
      (Label.order call) (orderExit call) phase

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := .number .bins .scan
  σ := State
  initialState := clean
  m := program

def cfg (label : Label) (base : Tape → List Bool) : machine.Cfg :=
  ⟨some label, clean, base⟩

def work (bound items assignments numerator denominator assigned : List Bool) : Tape → List Bool
  | 0 => []
  | 1 => items
  | 2 => assignments
  | 3 => bound
  | 4 => numerator
  | 5 => denominator
  | 6 => assigned
  | _ => []

def ready (bins : Nat) (items : RawInstance) (assignments : List Nat) : Tape → List Bool :=
  work bins.bits (BinaryEncoding.rawInstanceBits items)
    (BinaryEncoding.assignmentBits assignments) [] [] []

private theorem update_items (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 1 replacement = work b replacement a n d j := by
  funext k; fin_cases k <;> rfl

private theorem update_assignments (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 2 replacement = work b i replacement n d j := by
  funext k; fin_cases k <;> rfl

private theorem update_numerator (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 4 replacement = work b i a replacement d j := by
  funext k; fin_cases k <;> rfl

private theorem update_denominator (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 5 replacement = work b i a n replacement j := by
  funext k; fin_cases k <;> rfl

private theorem update_assigned (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 6 replacement = work b i a n d replacement := by
  funext k; fin_cases k <;> rfl

def oneStep {start finish : machine.Cfg}
    (step : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    change machine.step start = some finish
    exact step
  steps_le_m := Nat.le_refl _

def join {start middle finish : machine.Cfg} {firstTime secondTime : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) firstTime)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) secondTime) :
    StateTransition.EvalsToInTime machine.step start (some finish) (firstTime + secondTime) := by
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans machine.step firstTime secondTime
      start middle (some finish) first second

def enlarge {start finish : machine.Cfg} {time budget : Nat}
    (run : StateTransition.EvalsToInTime machine.step start (some finish) time)
    (bounded : time ≤ budget) :
    StateTransition.EvalsToInTime machine.step start (some finish) budget where
  toEvalsTo := run.toEvalsTo
  steps_le_m := Nat.le_trans run.steps_le_m bounded

def scanInTime (call : ScanCall) (base : Tape → List Bool) (n : Nat) (suffix : List Bool)
    (input : base (scanSource call) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base 7 = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number call .scan) base)
      (some (cfg (scanSuccess call)
        (ExtensionNatMachine.resultTapes (scanPorts call) base n suffix)))
      (2 * n.size + 2) :=
  ExtensionNatMachine.natInTime (scanPorts call) (Label.number call)
    (some (scanSuccess call)) (some (.control .reject)) program (fun _ => rfl)
    base n suffix input scratchEmpty ((), .eq)

def orderInTime (call : OrderCall) (base : Tape → List Bool) (a b : Nat)
    (leftWord : base (orderPorts call 0) = a.bits)
    (rightWord : base (orderPorts call 1) = b.bits)
    (leftEmpty : base 8 = []) (rightEmpty : base 9 = []) (scratchEmpty : base 7 = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.order call .leftOut) base)
      (some ⟨orderExit call (BinaryOrderMachine.orderNat a b .eq), clean, base⟩)
      (BinaryOrderMachine.preservingSteps a.size b.size) :=
  ExtensionNatMachine.preservingOrderInTime (orderPorts call) (Label.order call)
    (orderExit call) program (fun _ => rfl) base a b leftWord rightWord
    leftEmpty rightEmpty scratchEmpty ()

theorem markerStep (left right : Bool) (b i a n d j : List Bool) :
    machine.step (cfg (.control .marker) (work b (left :: i) (right :: a) n d j)) =
      some (cfg (if left = right then
        if left then .number .numerator .scan else .control .endCheck
        else .control .reject) (work b i a n d j)) := by
  cases left <;> cases right <;>
    change some (TM2.stepAux (program (.control .marker)) _ _) = _ <;>
    simp [program, controlInstruction, jump, cfg, clean, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, update_items, update_assignments, work]
  all_goals rfl

theorem boundEndStep (b i a n d j : List Bool) :
    machine.step (cfg (.control .boundEnd) (work b i a n d j)) =
      some (cfg (.control .marker) (work b i a n d j)) := by
  change some (TM2.stepAux (program (.control .boundEnd)) _ _) = _
  simp [program, controlInstruction, jump, cfg, clean, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, work]
  congr 1
  congr 1
  funext k
  fin_cases k <;> simp [work]

theorem positiveStep (b i a n d j : List Bool) :
    machine.step (cfg (.control .positive) (work b i a n d j)) =
      some (cfg (if n = [] then .control .reject else .number .denominator .scan)
        (work b i a n d j)) := by
  cases n <;>
    change some (TM2.stepAux (program (.control .positive)) _ _) = _ <;>
    simp [program, controlInstruction, jump, cfg, clean, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, update_numerator, work]
  all_goals rfl

theorem endStep (b n d j : List Bool) :
    machine.step (cfg (.control .endCheck) (work b [] [] n d j)) =
      some (cfg (.control .accept) (work b [] [] n d j)) := by
  change some (TM2.stepAux (program (.control .endCheck)) _ _) = _
  simp [program, controlInstruction, jump, cfg, clean, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, update_items, update_assignments, work]
  all_goals rfl

def clearInTime (b i a n d j : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.control .clearNumerator) (work b i a n d j))
      (some (cfg (.control .marker) (work b i a [] [] [])))
      ((n.length + 1) + (d.length + 1) + (j.length + 1)) := by
  have first := MachineDrain.drainInTime (4 : Tape) (.control .clearNumerator)
    (some (.control .clearDenominator)) program rfl (work b i a n d j)
    ((((), Ordering.eq), false), none) none
  have second := MachineDrain.drainInTime (5 : Tape) (.control .clearDenominator)
    (some (.control .clearAssigned)) program rfl (work b i a [] d j)
    ((((), Ordering.eq), false), none) none
  have third := MachineDrain.drainInTime (6 : Tape) (.control .clearAssigned)
    (some (.control .marker)) program rfl (work b i a [] [] j)
    ((((), Ordering.eq), false), none) none
  simp only [update_numerator, work] at first
  simp only [update_denominator, work] at second
  simp only [update_assigned, work] at third
  exact join (join first second) third

def numeratorInTime (b suffix assignments : List Bool) (n : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number .numerator .scan)
        (work b (BinaryEncoding.natBits n ++ suffix) assignments [] [] []))
      (some (cfg (.control .positive) (work b suffix assignments n.bits [] [])))
      (2 * n.size + 2) := by
  simpa only [scanPorts_apply, scanTape, scanSource, scanOutput, Function.Embedding.coeFn_mk,
    ExtensionNatMachine.resultTapes, update_items, update_numerator, work,
    List.append_nil, scanSuccess] using!
    scanInTime .numerator (work b (BinaryEncoding.natBits n ++ suffix) assignments [] [] [])
      n suffix rfl rfl

def denominatorInTime (b suffix assignments : List Bool) (n d : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number .denominator .scan)
        (work b (BinaryEncoding.natBits d ++ suffix) assignments n.bits [] []))
      (some (cfg (.order .fraction .leftOut) (work b suffix assignments n.bits d.bits [])))
      (2 * d.size + 2) := by
  simpa only [scanPorts_apply, scanTape, scanSource, scanOutput, Function.Embedding.coeFn_mk,
    ExtensionNatMachine.resultTapes, update_items, update_denominator, work,
    List.append_nil, scanSuccess] using!
    scanInTime .denominator
      (work b (BinaryEncoding.natBits d ++ suffix) assignments n.bits [] []) d suffix rfl rfl

def assignedInTime (b items suffix : List Bool) (n d j : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number .assigned .scan)
        (work b items (BinaryEncoding.natBits j ++ suffix) n.bits d.bits []))
      (some (cfg (.order .bound .leftOut) (work b items suffix n.bits d.bits j.bits)))
      (2 * j.size + 2) := by
  simpa only [scanPorts_apply, scanTape, scanSource, scanOutput, Function.Embedding.coeFn_mk,
    ExtensionNatMachine.resultTapes, update_assignments, update_assigned, work,
    List.append_nil, scanSuccess] using!
    scanInTime .assigned
      (work b items (BinaryEncoding.natBits j ++ suffix) n.bits d.bits []) j suffix rfl rfl

theorem fractionExit (a d : Nat) :
    orderExit .fraction (BinaryOrderMachine.orderNat a d .eq) =
      some (if a ≤ d then .number .assigned .scan else .control .reject) := by
  unfold BinaryOrderMachine.orderNat
  split_ifs <;> simp_all [orderExit] <;> omega

theorem boundExit (j bins : Nat) :
    orderExit .bound (BinaryOrderMachine.orderNat j bins .eq) =
      some (if j < bins then .control .clearNumerator else .control .reject) := by
  unfold BinaryOrderMachine.orderNat
  split_ifs <;> simp_all [orderExit]

theorem bits_eq_nil_iff (n : Nat) : n.bits = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg BinPackingCompleteness.BinaryEncoding.bitsValue h
    simpa only [BinPackingCompleteness.BinaryEncoding.bitsValue_bits,
      BinPackingCompleteness.BinaryEncoding.bitsValue] using hv
  · rintro rfl
    rfl

def rowBudget (bins a d j : Nat) : Nat :=
  6 * (a.size + d.size + j.size) + 3 * bins.size + 23

def loopTime (bins : Nat) : RawInstance → List Nat → Nat
  | (a, d) :: items, j :: assignments => rowBudget bins a d j + loopTime bins items assignments
  | _, _ => 2

structure LoopRun (bins : Nat) (items : RawInstance) (assignments : List Nat) where
  finish : Tape → List Bool
  bound_preserved : finish 3 = bins.bits
  input_empty : finish 0 = []
  accepted_clean : validRows bins items assignments = true →
    finish = work bins.bits [] [] [] [] []
  execution : StateTransition.EvalsToInTime machine.step
    (cfg (.control .marker) (ready bins items assignments))
    (some (cfg (.control (if validRows bins items assignments then .accept else .reject)) finish))
    (loopTime bins items assignments)

def rowsInTime (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    LoopRun bins items assignments := by
  induction items generalizing assignments with
  | nil =>
      cases assignments with
      | nil =>
          refine ⟨work bins.bits [] [] [] [] [], rfl, rfl, (fun _ => rfl), ?_⟩
          have first := oneStep (markerStep false false bins.bits [] [] [] [] [])
          have second := oneStep (endStep bins.bits [] [] [])
          simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, validRows, loopTime, Bool.false_eq_true,
            ↓reduceIte] using join first second
      | cons j assignments =>
          let tail := BinaryEncoding.natBits j ++ BinaryEncoding.assignmentBits assignments
          refine ⟨work bins.bits [] tail [] [] [], rfl, rfl, by simp [validRows], ?_⟩
          have step := oneStep (markerStep false true bins.bits [] tail [] [] [])
          simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, validRows, loopTime, tail, Bool.false_eq_true,
            ↓reduceIte] using enlarge step (by omega : 1 ≤ 2)
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      cases assignments with
      | nil =>
          let tail := BinaryEncoding.natBits a ++
            (BinaryEncoding.natBits d ++ BinaryEncoding.rawInstanceBits items)
          refine ⟨work bins.bits tail [] [] [] [], rfl, rfl, by simp [validRows], ?_⟩
          have step := oneStep (markerStep true false bins.bits tail [] [] [] [])
          simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, BinaryEncoding.pairBits, validRows, loopTime, tail,
            Bool.false_eq_true, ↓reduceIte, List.append_assoc] using
            enlarge step (by omega : 1 ≤ 2)
      | cons j assignments =>
          let itemTail := BinaryEncoding.rawInstanceBits items
          let labelTail := BinaryEncoding.assignmentBits assignments
          let dstream := BinaryEncoding.natBits d ++ itemTail
          let jstream := BinaryEncoding.natBits j ++ labelTail
          have marker : StateTransition.EvalsToInTime machine.step
              (cfg (.control .marker) (ready bins ((a, d) :: items) (j :: assignments)))
              (some (cfg (.number .numerator .scan)
                (work bins.bits (BinaryEncoding.natBits a ++ dstream) jstream [] [] []))) 1 := by
            simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
              BinaryEncoding.listBits, BinaryEncoding.pairBits, itemTail, labelTail,
              dstream, jstream, ↓reduceIte, List.append_assoc] using
              oneStep (markerStep true true bins.bits
                (BinaryEncoding.natBits a ++ dstream) jstream [] [] [])
          have numerator := numeratorInTime bins.bits dstream jstream a
          have positive := oneStep (positiveStep bins.bits dstream jstream a.bits [] [])
          simp only [bits_eq_nil_iff] at positive
          have initialRun := join (join marker numerator) positive
          by_cases zero : a = 0
          · refine ⟨work bins.bits dstream jstream a.bits [] [], rfl, rfl,
              by simp [validRows, zero], ?_⟩
            simpa only [validRows, zero, Nat.lt_irrefl, decide_false, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, cfg] using enlarge
                (budget := loopTime bins ((a, d) :: items) (j :: assignments)) initialRun
                (by simp only [loopTime, rowBudget]; omega)
          · have apos : 0 < a := Nat.pos_of_ne_zero zero
            rw [ite_eq_right zero] at initialRun
            have denominator := denominatorInTime bins.bits itemTail jstream a d
            have fraction := orderInTime .fraction
              (work bins.bits itemTail jstream a.bits d.bits []) a d rfl rfl rfl rfl rfl
            rw [fractionExit] at fraction
            have fractionPrefix := join (join initialRun denominator) fraction
            have fractionBound := BinaryOrderMachine.preservingSteps_le a.size d.size
            by_cases fits : a ≤ d
            · rw [ite_eq_left fits] at fractionPrefix
              have assigned := assignedInTime bins.bits itemTail labelTail a d j
              have bounded := orderInTime .bound
                (work bins.bits itemTail labelTail a.bits d.bits j.bits) j bins
                rfl rfl rfl rfl rfl
              rw [boundExit] at bounded
              have boundPrefix := join (join fractionPrefix assigned) bounded
              have labelBound := BinaryOrderMachine.preservingSteps_le j.size bins.size
              by_cases validLabel : j < bins
              · rw [ite_eq_left validLabel] at boundPrefix
                have clear := clearInTime bins.bits itemTail labelTail a.bits d.bits j.bits
                have clearTime : (a.bits.length + 1) + (d.bits.length + 1) +
                    (j.bits.length + 1) = a.size + d.size + j.size + 3 := by
                  simp only [← Nat.size_eq_bits_len]
                  omega
                rw [clearTime] at clear
                let later := ih assignments
                have acceptedClean : validRows bins ((a, d) :: items) (j :: assignments) = true →
                    later.finish = work bins.bits [] [] [] [] [] := by
                  intro h
                  apply later.accepted_clean
                  simpa [validRows, apos, fits, validLabel] using h
                refine ⟨later.finish, later.bound_preserved, later.input_empty, acceptedClean, ?_⟩
                have full := join (join boundPrefix clear) later.execution
                have timeBound :
                    (((((1 + (2 * a.size + 2)) + 1) + (2 * d.size + 2)) +
                      BinaryOrderMachine.preservingSteps a.size d.size) + (2 * j.size + 2)) +
                        BinaryOrderMachine.preservingSteps j.size bins.size +
                        (a.size + d.size + j.size + 3) + loopTime bins items assignments ≤
                      loopTime bins ((a, d) :: items) (j :: assignments) := by
                  simp only [loopTime, rowBudget]
                  omega
                simpa only [validRows, apos, fits, validLabel, decide_true, Bool.true_and,
                  ↓reduceIte] using enlarge full timeBound
              · refine ⟨work bins.bits itemTail labelTail a.bits d.bits j.bits, rfl, rfl,
                  by simp [validRows, apos, fits, validLabel], ?_⟩
                simpa only [validRows, apos, fits, validLabel, decide_true, decide_false,
                  Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte, cfg] using enlarge
                    (budget := loopTime bins ((a, d) :: items) (j :: assignments)) boundPrefix
                    (by simp only [loopTime, rowBudget]; omega)
            · refine ⟨work bins.bits itemTail jstream a.bits d.bits [], rfl, rfl,
                by simp [validRows, apos, fits], ?_⟩
              simpa only [validRows, apos, fits, decide_true, decide_false,
                Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte, cfg] using enlarge
                  (budget := loopTime bins ((a, d) :: items) (j :: assignments)) fractionPrefix
                  (by simp only [loopTime, rowBudget]; omega)

private theorem base_budget (b t : Nat) : 2 ≤ 10 * (b + 1) * (t + 1) := by
  have h : 1 ≤ (b + 1) * (t + 1) :=
    Nat.mul_le_mul (by omega : 1 ≤ b + 1) (by omega : 1 ≤ t + 1)
  calc
    2 ≤ 10 := by decide
    _ ≤ 10 * (b + 1) * (t + 1) := by
      simpa only [Nat.mul_one, Nat.mul_assoc] using Nat.mul_le_mul_left 10 h

private theorem row_budget (b s : Nat) :
    6 * s + 3 * b + 23 ≤ 10 * (b + 1) * (2 * s + 5) := by
  nlinarith [Nat.zero_le (b * s)]

theorem loopTime_le (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    loopTime bins items assignments ≤ 10 * (bins.size + 1) *
      ((BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length + 1) := by
  induction items generalizing assignments with
  | nil =>
      exact base_budget bins.size _
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      cases assignments with
      | nil => exact base_budget bins.size _
      | cons j assignments =>
          have hlen : (BinaryEncoding.rawInstanceBits ((a, d) :: items)).length +
                (BinaryEncoding.assignmentBits (j :: assignments)).length + 1 =
              (2 * (a.size + d.size + j.size) + 5) +
                ((BinaryEncoding.rawInstanceBits items).length +
                  (BinaryEncoding.assignmentBits assignments).length + 1) := by
            simp only [BinaryEncoding.rawInstanceBits_length,
              BinaryEncoding.assignmentBits_length, List.map_cons, List.sum_cons]
            omega
          rw [loopTime, hlen, Nat.mul_add]
          exact Nat.add_le_add
            (by simpa only [rowBudget] using
              row_budget bins.size (a.size + d.size + j.size))
            (ih assignments)

def inputTapes (bins : Nat) (items : RawInstance) (assignments : List Nat) : Tape → List Bool :=
  Function.update (work [] (BinaryEncoding.rawInstanceBits items)
    (BinaryEncoding.assignmentBits assignments) [] [] []) 0 (BinaryEncoding.natBits bins)

def initializeInTime (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number .bins .scan) (inputTapes bins items assignments))
      (some (cfg (.control .marker) (ready bins items assignments)))
      (2 * bins.size + 3) := by
  have scanned := scanInTime .bins (inputTapes bins items assignments) bins []
    (by simp [inputTapes, scanSource]) (by simp [inputTapes, work])
  have result : ExtensionNatMachine.resultTapes (scanPorts .bins)
      (inputTapes bins items assignments) bins [] = ready bins items assignments := by
    funext k
    fin_cases k <;> simp [ExtensionNatMachine.resultTapes, scanTape,
      scanSource, scanOutput, inputTapes, ready, work]
    change Function.update (β := fun _ => List Bool) _ (scanPorts .bins 1) bins.bits (scanPorts .bins 1) = bins.bits
    exact Function.update_self _ _ _
  rw [result] at scanned
  have finished := oneStep (boundEndStep bins.bits
    (BinaryEncoding.rawInstanceBits items) (BinaryEncoding.assignmentBits assignments) [] [] [])
  have full := join scanned finished
  simpa [scanSuccess, ready, Nat.add_assoc] using full

def inputLength (bins : Nat) (items : RawInstance) (assignments : List Nat) : Nat :=
  (BinaryEncoding.natBits bins).length + (BinaryEncoding.rawInstanceBits items).length +
    (BinaryEncoding.assignmentBits assignments).length

noncomputable def validationTime : Polynomial Nat := 16 * (Polynomial.X + 1) ^ 2

private theorem total_budget (b F A steps : Nat)
    (bounded : steps ≤ 10 * (b + 1) * (F + A + 1)) :
    2 * b + 3 + steps + 1 ≤ 16 * ((2 * b + 1 + F + A) + 1) ^ 2 := by
  let M := 2 * b + 1 + F + A
  have hb : b + 1 ≤ M + 1 := by dsimp [M]; omega
  have hs : F + A + 1 ≤ M + 1 := by dsimp [M]; omega
  have hp := Nat.mul_le_mul hb hs
  have hloop : steps ≤ 10 * (M + 1) ^ 2 := by
    calc
      steps ≤ 10 * (b + 1) * (F + A + 1) := bounded
      _ ≤ 10 * ((M + 1) * (M + 1)) := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hp
      _ = 10 * (M + 1) ^ 2 := by rw [pow_two]
  have hsq : M + 1 ≤ (M + 1) ^ 2 := by nlinarith [Nat.zero_le (M * M)]
  change 2 * b + 3 + steps + 1 ≤ 16 * (M + 1) ^ 2
  omega

theorem totalTime_le (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    2 * bins.size + 3 + loopTime bins items assignments + 1 ≤
      validationTime.eval (inputLength bins items assignments) := by
  simpa only [validationTime, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
    inputLength, BinaryEncoding.natBits_length] using
    total_budget bins.size (BinaryEncoding.rawInstanceBits items).length
      (BinaryEncoding.assignmentBits assignments).length (loopTime bins items assignments)
      (loopTime_le bins items assignments)

theorem flagStep (accepted : Bool) (base : Tape → List Bool) (empty : base 0 = []) :
    machine.step (cfg (.control (if accepted then .accept else .reject)) base) =
      some ⟨none, clean, Function.update base 0 [accepted]⟩ := by
  cases accepted with
  | false =>
      change some (TM2.stepAux (program (.control .reject)) clean base) = _
      simp [program, controlInstruction, TM2.stepAux, empty]
      rfl
  | true =>
      change some (TM2.stepAux (program (.control .accept)) clean base) = _
      simp [program, controlInstruction, TM2.stepAux, empty]
      rfl

structure ValidationRun (bins : Nat) (items : RawInstance) (assignments : List Nat) where
  finish : Tape → List Bool
  flag : finish 0 = [validRows bins items assignments]
  bound_preserved : finish 3 = bins.bits
  accepted_clean : validRows bins items assignments = true →
    finish = Function.update (work bins.bits [] [] [] [] []) 0 [true]
  execution : StateTransition.EvalsToInTime machine.step
    (cfg (.number .bins .scan) (inputTapes bins items assignments))
    (some ⟨none, clean, finish⟩) (validationTime.eval (inputLength bins items assignments))

noncomputable def validationInTime (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    ValidationRun bins items assignments := by
  let rows := rowsInTime bins items assignments
  let final := Function.update rows.finish 0 [validRows bins items assignments]
  refine ⟨final, by simp [final], ?_, ?_, ?_⟩
  · simpa only [final, Function.update_of_ne (by decide : (3 : Tape) ≠ 0)] using
      rows.bound_preserved
  · intro accepted
    change Function.update rows.finish 0 [validRows bins items assignments] = _
    rw [rows.accepted_clean accepted, accepted]
  · have first := initializeInTime bins items assignments
    have last := oneStep (flagStep (validRows bins items assignments) rows.finish rows.input_empty)
    exact enlarge (join (join first rows.execution) last) (totalTime_le bins items assignments)

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end BinPackingGap.ExtensionValidationMachine

end OAI
