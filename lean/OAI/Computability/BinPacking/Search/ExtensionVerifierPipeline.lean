import Mathlib.Tactic.Linarith
import OAI.Computability.BinPacking.Search.ExtensionAgreementMachine
import OAI.Computability.BinPacking.Search.ExtensionCapacityBounds
import OAI.Computability.BinPacking.Search.ExtensionMachineSpace
import OAI.Computability.BinPacking.Search.ExtensionPairMachine
import OAI.Computability.BinPacking.Search.ExtensionShapeMachine
import OAI.Computability.BinPacking.Search.ExtensionValidationMachine
import OAI.Computability.BinPacking.Search.ExtensionVerifierMachine

namespace OAI

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity

theorem workBound (B : Nat) (N D i w s a d j U V : List Bool)
    (hN : N.length ≤ B + 2) (hD : D.length ≤ B + 2)
    (hi : i.length ≤ B + 2) (hw : w.length ≤ B + 2) (hs : s.length ≤ B + 2)
    (ha : a.length ≤ B + 2) (hd : d.length ≤ B + 2) (hj : j.length ≤ B + 2)
    (hU : U.length ≤ B + 2) (hV : V.length ≤ B + 2) :
    ∀ k : Tape, (work N D i w s a d j U V [] k).length ≤ B + 2 := by
  intro k
  fin_cases k <;> simp_all [work]

theorem scan_overfull (items : RawInstance) (assignments : List Nat) (selected num den : Nat)
    (overfull : den < num) : CapacityScan.scan selected items assignments (num, den) = false := by
  cases items <;> cases assignments <;> simp [CapacityScan.scan, Nat.not_le_of_lt overfull]

structure CoreRun (items : RawInstance) (assignments : List Nat)
    (selected num den B : Nat) where
  finish : Tape → List Bool
  bounded : ∀ k, (finish k).length ≤ B + 2
  execution : StateTransition.EvalsToInTime machine.step
    (cfg (some (.core .guard)) (ready num den selected items assignments))
    (some (cfg (cleanupEntry (CapacityScan.scan selected items assignments (num, den))) finish))
    ((items.length + 1) * (1024 * (B + 1) ^ 2))

noncomputable def coreRun (items : RawInstance) (assignments : List Nat)
    (selected num den B : Nat)
    (valid : items.Valid) (sameLength : assignments.length = items.length)
    (fits : num ≤ den)
    (denBudget : den.size + FractionWidth.denominatorBits items ≤ B + 1)
    (itemBound : (BinaryEncoding.rawInstanceBits items).length ≤ B)
    (assignmentBound : (BinaryEncoding.assignmentBits assignments).length ≤ B)
    (selectedBound : selected.size ≤ B) : CoreRun items assignments selected num den B := by
  induction items generalizing assignments num den with
  | nil =>
      have assignmentsNil : assignments = [] := by
        cases assignments with
        | nil => rfl
        | cons head tail => simp at sameLength
      subst assignments
      have hden : den.size ≤ B + 1 := by simpa using denBudget
      have hnum : num.size ≤ B + 1 := (FractionWidth.size_mono fits).trans hden
      refine ⟨work num.bits den.bits [] [] selected.bits [] [] [] [] [], ?_, ?_⟩
      · apply workBound <;> simp only [List.length_nil, Nat.size_eq_bits_len] <;> omega
      · have step := oneStep (guard_nil_step num.bits den.bits selected.bits)
        have time : 1 ≤ (0 + 1) * (1024 * (B + 1) ^ 2) := by
          have positive : 0 < 1024 * (B + 1) ^ 2 := by positivity
          simpa only [Nat.zero_add, Nat.one_mul] using Nat.succ_le_of_lt positive
        simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
          BinaryEncoding.listBits, CapacityScan.scan, fits] using enlarge step time
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      cases assignments with
      | nil => simp at sameLength
      | cons assigned assignments =>
          have validTail : RawInstance.Valid items := fun q hq => valid q (List.mem_cons_of_mem _ hq)
          have sizeTail : assignments.length = items.length := by simpa using sameLength
          have itemValid := valid (a, d) (List.mem_cons_self ..)
          have aq : a ≤ d := itemValid.2
          have hden : den.size + d.size ≤ B + 1 := by
            simp only [FractionWidth.denominatorBits_cons] at denBudget
            omega
          have hnum := FractionWidth.size_mono fits
          have ha := FractionWidth.size_mono aq
          have itemTailBound : (BinaryEncoding.rawInstanceBits items).length ≤ B := by
            simp only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
              BinaryEncoding.pairBits, List.length_cons, List.length_append] at itemBound ⊢
            omega
          have assignmentTailBound : (BinaryEncoding.assignmentBits assignments).length ≤ B := by
            simp only [BinaryEncoding.assignmentBits, BinaryEncoding.listBits,
              List.length_cons, List.length_append] at assignmentBound ⊢
            omega
          have assignedBound : assigned.size ≤ B := by
            simp only [BinaryEncoding.assignmentBits, BinaryEncoding.listBits,
              List.length_cons, List.length_append, BinaryEncoding.natBits_length] at assignmentBound
            omega
          have tailDenBudget : den.size + FractionWidth.denominatorBits items ≤ B + 1 := by
            simp only [FractionWidth.denominatorBits_cons] at denBudget
            omega
          let itemWord := BinaryEncoding.rawInstanceBits items
          let assignmentWord := BinaryEncoding.assignmentBits assignments
          have guard := oneStep (guard_cons_step num.bits den.bits
            (BinaryEncoding.natBits a ++ BinaryEncoding.natBits d ++ itemWord)
            (BinaryEncoding.natBits assigned ++ assignmentWord) selected.bits [] [] [] [] [])
          have parsed := parseRowInTime num.bits den.bits selected.bits itemWord assignmentWord
            a d assigned
          have compared := compareInTime .label
            (work num.bits den.bits itemWord assignmentWord selected.bits a.bits d.bits
              assigned.bits [] []) assigned selected rfl rfl rfl rfl rfl
          rw [labelComparisonExit] at compared
          have rowPrefix := join (join guard parsed) compared
          have rowBound := rowCost_le num den a d assigned selected B fits aq hden
            assignedBound selectedBound
          have count : (((a, d) :: items).length + 1) * (1024 * (B + 1) ^ 2) =
              1024 * (B + 1) ^ 2 + (items.length + 1) * (1024 * (B + 1) ^ 2) := by
            simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
            omega
          by_cases matched : assigned = selected
          · rw [ite_eq_left matched] at rowPrefix
            have arithmetic := fractionInTime num den a d itemWord assignmentWord selected.bits assigned.bits
            have capacity := compareInTime .capacity
              (work num.bits den.bits itemWord assignmentWord selected.bits a.bits d.bits assigned.bits
                (num * d + a * den).bits (den * d).bits)
              (num * d + a * den) (den * d) rfl rfl rfl rfl rfl
            rw [capacityComparisonExit] at capacity
            have tested := join (join rowPrefix arithmetic) capacity
            have newDenBound := FractionWidth.addFraction_den_size_le (num, den) (a, d)
            have newNumBound := FractionWidth.addFraction_num_size_le
              (x := (num, den)) (q := (a, d)) fits aq
            change (den * d).size ≤ den.size + d.size at newDenBound
            change (num * d + a * den).size ≤ den.size + d.size + 1 at newNumBound
            by_cases accepted : num * d + a * den ≤ den * d
            · rw [ite_eq_left accepted] at tested
              have installed := installInTime num.bits den.bits itemWord assignmentWord selected.bits
                a.bits d.bits assigned.bits (num * d + a * den).bits (den * d).bits
              have cleared := clearRowInTime (num * d + a * den).bits (den * d).bits
                itemWord assignmentWord selected.bits a.bits d.bits assigned.bits
              have nextDenBudget : (den * d).size + FractionWidth.denominatorBits items ≤ B + 1 := by
                simp only [FractionWidth.denominatorBits_cons] at denBudget
                omega
              let later := ih assignments (num * d + a * den) (den * d) validTail sizeTail accepted
                nextDenBudget itemTailBound assignmentTailBound
              refine ⟨later.finish, later.bounded, ?_⟩
              have full := join (join (join tested installed) cleared) later.execution
              have sizeWords : num.bits.length = num.size ∧ den.bits.length = den.size ∧
                  a.bits.length = a.size ∧ d.bits.length = d.size ∧
                  assigned.bits.length = assigned.size ∧
                  (num * d + a * den).bits.length = (num * d + a * den).size ∧
                  (den * d).bits.length = (den * d).size := by
                simp only [Nat.size_eq_bits_len, and_self]
              rcases sizeWords with ⟨wN, wD, wa, wd, wj, wU, wV⟩
              have bounded :
                  (((((1 + ((2 * a.size + 2) + (2 * d.size + 2) +
                    (2 * assigned.size + 2))) +
                    BinaryOrderMachine.preservingSteps assigned.size selected.size) +
                    ExtensionFractionMachine.arithmeticBudget num den a d) +
                    BinaryOrderMachine.preservingSteps (num * d + a * den).size (den * d).size) +
                    (num.bits.length + den.bits.length + 2 * (num * d + a * den).bits.length +
                      2 * (den * d).bits.length + 6)) +
                    ((a.bits.length + 1) + (d.bits.length + 1) + (assigned.bits.length + 1)) +
                    (items.length + 1) * (1024 * (B + 1) ^ 2) ≤
                    (((a, d) :: items).length + 1) * (1024 * (B + 1) ^ 2) := by
                rw [wN, wD, wa, wd, wj, wU, wV, count]
                unfold rowCost at rowBound
                omega
              simpa only [ready, itemWord, assignmentWord, BinaryEncoding.rawInstanceBits,
                BinaryEncoding.assignmentBits, BinaryEncoding.listBits, BinaryEncoding.pairBits,
                CapacityScan.scan, ite_eq_left fits, CapacityScan.step, ite_eq_left matched,
                RawPacking.addFraction] using enlarge full bounded
            · rw [ite_eq_right accepted] at tested
              refine ⟨work num.bits den.bits itemWord assignmentWord selected.bits a.bits d.bits
                assigned.bits (num * d + a * den).bits (den * d).bits, ?_, ?_⟩
              · apply workBound <;>
                  simp only [Nat.size_eq_bits_len, itemWord, assignmentWord] <;> omega
              · have scanRejected := scan_overfull items assignments selected
                  (num * d + a * den) (den * d) (Nat.lt_of_not_ge accepted)
                have bounded :
                    (((1 + ((2 * a.size + 2) + (2 * d.size + 2) + (2 * assigned.size + 2))) +
                      BinaryOrderMachine.preservingSteps assigned.size selected.size) +
                      ExtensionFractionMachine.arithmeticBudget num den a d) +
                      BinaryOrderMachine.preservingSteps (num * d + a * den).size (den * d).size ≤
                      (((a, d) :: items).length + 1) * (1024 * (B + 1) ^ 2) := by
                  rw [count]
                  unfold rowCost at rowBound
                  omega
                simpa only [ready, itemWord, assignmentWord, BinaryEncoding.rawInstanceBits,
                  BinaryEncoding.assignmentBits, BinaryEncoding.listBits, BinaryEncoding.pairBits,
                  CapacityScan.scan, ite_eq_left fits, CapacityScan.step, ite_eq_left matched,
                  RawPacking.addFraction, scanRejected] using enlarge tested bounded
          · rw [ite_eq_right matched] at rowPrefix
            have cleared := clearRowInTime num.bits den.bits itemWord assignmentWord selected.bits
              a.bits d.bits assigned.bits
            let later := ih assignments num den validTail sizeTail fits tailDenBudget
              itemTailBound assignmentTailBound
            refine ⟨later.finish, later.bounded, ?_⟩
            have full := join (join rowPrefix cleared) later.execution
            have bounded :
                ((1 + ((2 * a.size + 2) + (2 * d.size + 2) + (2 * assigned.size + 2))) +
                  BinaryOrderMachine.preservingSteps assigned.size selected.size) +
                  ((a.bits.length + 1) + (d.bits.length + 1) + (assigned.bits.length + 1)) +
                  (items.length + 1) * (1024 * (B + 1) ^ 2) ≤
                  (((a, d) :: items).length + 1) * (1024 * (B + 1) ^ 2) := by
              simp only [Nat.size_eq_bits_len]
              rw [count]
              unfold rowCost at rowBound
              omega
            simpa only [ready, itemWord, assignmentWord, BinaryEncoding.rawInstanceBits,
              BinaryEncoding.assignmentBits, BinaryEncoding.listBits, BinaryEncoding.pairBits,
              CapacityScan.scan, ite_eq_left fits, CapacityScan.step, ite_eq_right matched] using
              enlarge full bounded

noncomputable def innerInPolynomialTime (items : RawInstance) (assignments : List Nat)
    (selected : Nat) (valid : items.Valid) (sameLength : assignments.length = items.length) :
    StateTransition.EvalsToInTime machine.step
      (initialCfg items assignments selected)
      (some (finalCfg (CapacityScan.scan selected items assignments (0, 1))))
      (timePolynomial.eval (inputLength items assignments selected)) := by
  let B := inputLength items assignments selected
  have itemBound : (BinaryEncoding.rawInstanceBits items).length ≤ B := by
    simp only [B, inputLength]
    omega
  have assignmentBound : (BinaryEncoding.assignmentBits assignments).length ≤ B := by
    simp only [B, inputLength]
    omega
  have selectedBound : selected.size ≤ B := by
    simp only [B, inputLength]
    omega
  have denominatorBound : (1 : Nat).size + FractionWidth.denominatorBits items ≤ B + 1 := by
    have h := ExtensionWitness.denominatorBits_le_rawInstanceBits items
    change 1 + FractionWidth.denominatorBits items ≤ B + 1
    omega
  let core := coreRun items assignments selected 0 1 B valid sameLength (by decide)
    denominatorBound itemBound assignmentBound selectedBound
  have initialization := oneStep (initializeStep items assignments selected)
  have ready_eq : inputTapes (fun _ => []) 0 1 selected items assignments =
      ready 0 1 selected items assignments := by
    funext k
    fin_cases k <;> simp [inputTapes, ready, work]
  rw [ready_eq] at initialization
  have cleanup := cleanupInTime (CapacityScan.scan selected items assignments (0, 1)) core.finish
  have all := join (join initialization core.execution) cleanup
  have lengthBound (chosen : List Tape) :
      MachineDrainMany.lengthSum chosen core.finish ≤ chosen.length * (B + 2) := by
    induction chosen with
    | nil => simp [MachineDrainMany.lengthSum]
    | cons k chosen ih =>
        have hk := core.bounded k
        simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
          List.length_cons, Nat.add_mul, Nat.one_mul] at ih ⊢
        omega
  have cleanupBound : MachineDrainMany.lengthSum allTapes core.finish ≤ 22 * (B + 2) := by
    simpa only [allTapes, List.length_ofFn] using lengthBound allTapes
  have itemCount : items.length ≤ B :=
    (BinaryEncoding.list_length_le_bits_length
      (BinaryEncoding.pairBits BinaryEncoding.natBits BinaryEncoding.natBits) items).trans itemBound
  have coreBound : (items.length + 1) * (1024 * (B + 1) ^ 2) ≤ 1024 * (B + 1) ^ 3 := by
    have h := Nat.mul_le_mul_right (1024 * (B + 1) ^ 2)
      (Nat.add_le_add_right itemCount 1)
    convert h using 1
    ring
  have powerBound : B + 1 ≤ (B + 1) ^ 3 := by
    have hsq : 1 ≤ (B + 1) ^ 2 := by
      have positive : 0 < (B + 1) ^ 2 := by positivity
      exact Nat.succ_le_of_lt positive
    have hm := Nat.mul_le_mul_left (B + 1) hsq
    nlinarith
  have budget :
      (1 + (items.length + 1) * (1024 * (B + 1) ^ 2)) +
        (MachineDrainMany.lengthSum allTapes core.finish + 23) ≤
        timePolynomial.eval B := by
    simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    omega
  exact enlarge all budget

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionCapacityOuterMachine

open Turing BinPackingGames.Foundations.Complexity BinPackingGames.Reduction

abbrev Tape := Fin 26
abbrev State := ExtensionCapacityMachine.State Unit
abbrev Alphabet (_ : Tape) := Bool

def allTapes : List Tape := List.ofFn id

inductive CopyKind
  | outerLabels | items | assignments
  deriving DecidableEq

protected abbrev CopyKind.enumList : List CopyKind := [.outerLabels, .items, .assignments]

protected theorem CopyKind.enumList_getElem?_ctorIdx_eq (x : CopyKind) :
    CopyKind.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem CopyKind.enumList_nodup : CopyKind.enumList.Nodup := by decide

instance : Fintype CopyKind where
  elems := ⟨CopyKind.enumList, CopyKind.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | copyOut (kind : CopyKind)
  | copyBack (kind : CopyKind)
  | guard
  | number (phase : ExtensionNatMachine.Label)
  | inner (phase : ExtensionCapacityMachine.FullLabel)
  | afterInner
  | cleanup (result : Bool) (phase : MachineDrainMany.Label allTapes)
  | emit (result : Bool)
  deriving DecidableEq, Fintype

def clean : State := BinaryAddMachine.clean ((), .eq)

def innerTape (k : ExtensionCapacityMachine.machine.K) : Tape :=
  ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩

def innerView (k : Tape) : Option ExtensionCapacityMachine.machine.K :=
  if small : k.val < 22 then some ⟨k.val, small⟩ else none

theorem innerView_left (k : ExtensionCapacityMachine.machine.K) :
    innerView (innerTape k) = some k := by
  simp [innerView, innerTape, k.isLt]
  rfl

theorem innerView_right (j : Tape) (k : ExtensionCapacityMachine.machine.K)
    (found : innerView j = some k) : innerTape k = j := by
  unfold innerView at found
  split at found
  · have equal := Option.some.inj found
    apply Fin.ext
    exact (congrArg Fin.val equal).symm
  · contradiction

def numberTapes : Fin 3 ↪ Tape := ⟨![24, 4, 25], by decide⟩

def copySource : CopyKind → Tape
  | .outerLabels => 23
  | .items => 22
  | .assignments => 23

def copyDestination : CopyKind → Tape
  | .outerLabels => 24
  | .items => 2
  | .assignments => 3

def afterCopy : CopyKind → Label
  | .outerLabels => .guard
  | .items => .copyOut .assignments
  | .assignments => .inner ExtensionCapacityMachine.machine.main

def cleanupEntry (result : Bool) : Option Label :=
  MachineDrainMany.entry allTapes (Label.cleanup result) (some (.emit result))

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => clean) (.goto fun _ => label)

def finish (exit : Option Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => clean) (match exit with
    | some label => .goto fun _ => label
    | none => .halt)

def program : Label → TM2.Stmt Alphabet Label State
  | .copyOut kind =>
      MachineTransfer.loopAt (copySource kind) 25 id false (.copyOut kind)
        (some (.copyBack kind))
  | .copyBack kind =>
      MachineCopy.forkLoop 25 (copySource kind) (copyDestination kind) false
        (.copyBack kind) (some (afterCopy kind))
  | .guard =>
      .pop 24 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.branch (fun state => state.2.getD false)
            (jump (.number .scan)) (finish (cleanupEntry true)))
          (finish (cleanupEntry false)))
  | .number phase =>
      ExtensionNatMachine.statement numberTapes Label.number
        (some (.copyOut .items)) (cleanupEntry false) phase
  | .inner phase =>
      ExtensionMachinePlacement.statement innerTape Label.inner (some .afterInner)
        (ExtensionMachineRegisters.Lens.identity State)
        (ExtensionCapacityMachine.machine.m phase)
  | .afterInner =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => decide (state.2 = some true))
          (jump .guard) (finish (cleanupEntry false)))
  | .cleanup result phase =>
      MachineDrainMany.instruction allTapes (Label.cleanup result) (some (.emit result)) phase
  | .emit result => .load (fun _ => clean) (.push 0 (fun _ => result) .halt)

def machine : FinTM2 where
  K := Tape
  k₀ := 22
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := .copyOut .outerLabels
  σ := State
  initialState := clean
  m := program

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

private def join {start middle finish : machine.Cfg} {firstTime secondTime : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) firstTime)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) secondTime) :
    StateTransition.EvalsToInTime machine.step start (some finish) (firstTime + secondTime) := by
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans machine.step _ _ _ _ _ first second

def stageTapes (items : RawInstance) (assignments remaining : List Nat) : Tape → List Bool :=
  fun k =>
    if k = 22 then BinaryEncoding.rawInstanceBits items
    else if k = 23 then BinaryEncoding.assignmentBits assignments
    else if k = 24 then BinaryEncoding.assignmentBits remaining
    else []

def initialTapes (items : RawInstance) (assignments : List Nat) : Tape → List Bool :=
  Function.update (stageTapes items assignments []) 24 []

def resultTapes (result : Bool) : Tape → List Bool :=
  Function.update (fun _ => []) 0 [result]

def configuration (label : Option Label) (tapes : Tape → List Bool) : machine.Cfg :=
  ⟨label, clean, tapes⟩

def initialCfg (items : RawInstance) (assignments : List Nat) : machine.Cfg :=
  configuration (some machine.main) (initialTapes items assignments)

def finalCfg (result : Bool) : machine.Cfg := configuration none (resultTapes result)

def inputLength (items : RawInstance) (assignments : List Nat) : Nat :=
  (BinaryEncoding.rawInstanceBits items).length + (BinaryEncoding.assignmentBits assignments).length

def scanResult (items : RawInstance) (assignments remaining : List Nat) : Bool :=
  remaining.all (fun selected => CapacityScan.scan selected items assignments (0, 1))

theorem scanResult_eq_capacityChecks (items : RawInstance) (valid : items.Valid)
    (assignments remaining : List Nat) :
    scanResult items assignments remaining =
      remaining.all (ExtensionCertificate.capacityCheck items assignments) := by
  induction remaining with
  | nil => rfl
  | cons selected remaining ih =>
      simpa only [scanResult, List.all_cons,
        CapacityScan.scan_initial_eq_capacityCheck selected items valid assignments] using
        congrArg (fun answer => ExtensionCertificate.capacityCheck items assignments selected && answer) ih

theorem selected_size_le_encoding (selected : Nat) (assignments : List Nat)
    (member : selected ∈ assignments) :
    selected.size ≤ (BinaryEncoding.assignmentBits assignments).length := by
  induction assignments with
  | nil => simp at member
  | cons value assignments ih =>
      have length : (BinaryEncoding.assignmentBits (value :: assignments)).length =
          2 * value.size + 2 + (BinaryEncoding.assignmentBits assignments).length := by
        simp [BinaryEncoding.assignmentBits, BinaryEncoding.listBits]
        omega
      rw [length]
      rcases List.mem_cons.mp member with same | member
      · subst selected
        omega
      · have bound := ih member
        omega

theorem suffix_encoding_length_le (before after : List Nat) :
    (BinaryEncoding.assignmentBits after).length ≤
      (BinaryEncoding.assignmentBits (before ++ after)).length := by
  induction before with
  | nil => exact Nat.le_refl _
  | cons value before ih =>
      simp only [List.cons_append]
      have length : (BinaryEncoding.assignmentBits (value :: (before ++ after))).length =
          2 * value.size + 2 + (BinaryEncoding.assignmentBits (before ++ after)).length := by
        simp [BinaryEncoding.assignmentBits, BinaryEncoding.listBits]
        omega
      rw [length]
      omega

noncomputable def roundBudget (inputLength : Nat) : Nat :=
  ExtensionCapacityMachine.timePolynomial.eval (2 * inputLength) + 6 * inputLength + 8

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 65536 * (Polynomial.X + Polynomial.C 1) ^ 4

theorem totalBudget_le (itemLength assignmentLength visits : Nat)
    (bounded : visits ≤ itemLength + assignmentLength) :
    visits * roundBudget (itemLength + assignmentLength) +
        itemLength + 4 * assignmentLength + 30 ≤
      timePolynomial.eval (itemLength + assignmentLength) := by
  have product := Nat.mul_le_mul_right
    (roundBudget (itemLength + assignmentLength)) bounded
  have linear : itemLength + 4 * assignmentLength ≤
      4 * (itemLength + assignmentLength) := by omega
  apply (Nat.add_le_add_right
    (show visits * roundBudget (itemLength + assignmentLength) +
        itemLength + 4 * assignmentLength ≤
      (itemLength + assignmentLength) * roundBudget (itemLength + assignmentLength) +
        4 * (itemLength + assignmentLength) by omega) 30).trans
  simp only [roundBudget, timePolynomial, ExtensionCapacityMachine.timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith [Nat.zero_le ((itemLength + assignmentLength) ^ 2),
    Nat.zero_le ((itemLength + assignmentLength) ^ 3),
    Nat.zero_le ((itemLength + assignmentLength) ^ 4)]

theorem guardStep (base : Tape → List Bool) (bit : Bool) (tail : List Bool)
    (word : base 24 = bit :: tail) :
    machine.step (configuration (some .guard) base) =
      some (configuration
        (if bit then some (.number .scan) else cleanupEntry true)
        (Function.update base 24 tail)) := by
  cases bit <;> cases cleanup : cleanupEntry true <;>
    simp [FinTM2.step, machine, configuration, program, TM2.step, TM2.stepAux,
      word, jump, finish, cleanup] <;> rfl

theorem afterInnerStep (base : Tape → List Bool) (result : Bool)
    (word : base 0 = [result]) :
    machine.step (configuration (some .afterInner) base) =
      some (configuration (if result then some .guard else cleanupEntry false)
        (Function.update base 0 [])) := by
  cases result <;> cases cleanup : cleanupEntry false <;>
    simp [FinTM2.step, machine, configuration, program, TM2.step, TM2.stepAux,
      word, jump, finish, cleanup] <;> rfl

def copyInTime (kind : CopyKind) (base : Tape → List Bool)
    (scratchEmpty : base 25 = []) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some (.copyOut kind)) base)
      (some (configuration (some (afterCopy kind))
        (Function.update base (copyDestination kind)
          (base (copySource kind) ++ base (copyDestination kind)))))
      (2 * ((base (copySource kind)).length + 1)) := by
  have sourceDestination : copySource kind ≠ copyDestination kind := by cases kind <;> decide
  have sourceScratch : copySource kind ≠ 25 := by cases kind <;> decide
  have destinationScratch : copyDestination kind ≠ 25 := by cases kind <;> decide
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.copyOut kind), clean, base⟩
    (some ⟨some (afterCopy kind), clean,
      Function.update base (copyDestination kind)
        (base (copySource kind) ++ base (copyDestination kind))⟩) _
  exact MachineCopy.copyInTime (copySource kind) (copyDestination kind) 25
    sourceDestination sourceScratch destinationScratch false
    (.copyOut kind) (.copyBack kind) (some (afterCopy kind)) program rfl rfl
    base scratchEmpty ((((), .eq), false), none) none

def initialCopyInTime (items : RawInstance) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some (.copyOut .outerLabels)) (initialTapes items assignments))
      (some (configuration (some .guard) (stageTapes items assignments assignments)))
      (2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
  have copied := copyInTime .outerLabels (initialTapes items assignments)
    (by simp [initialTapes, stageTapes])
  have original : initialTapes items assignments 23 = BinaryEncoding.assignmentBits assignments := by
    simp [initialTapes, stageTapes]
  have empty : initialTapes items assignments 24 = [] := by simp [initialTapes]
  have final : Function.update (initialTapes items assignments) 24
      (BinaryEncoding.assignmentBits assignments) = stageTapes items assignments assignments := by
    funext k
    by_cases selected : k = 24
    · subst k
      simp [stageTapes]
    · simp [initialTapes, stageTapes, selected]
  simpa only [copySource, copyDestination, afterCopy, original, empty, List.append_nil, final]
    using copied

def selectedInTime (base : Tape → List Bool) (selected : Nat) (remaining : List Nat)
    (word : base 24 = BinaryEncoding.natBits selected ++ BinaryEncoding.assignmentBits remaining)
    (scratchEmpty : base 25 = []) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some (.number .scan)) base)
      (some (configuration (some (.copyOut .items))
        (ExtensionNatMachine.resultTapes numberTapes base selected
          (BinaryEncoding.assignmentBits remaining))))
      (2 * selected.size + 2) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.number .scan), clean, base⟩
    (some ⟨some (.copyOut .items), clean,
      ExtensionNatMachine.resultTapes numberTapes base selected
        (BinaryEncoding.assignmentBits remaining)⟩) _
  exact ExtensionNatMachine.natInTime numberTapes Label.number (some (.copyOut .items))
    (cleanupEntry false) program (fun _ => rfl) base selected
    (BinaryEncoding.assignmentBits remaining) word scratchEmpty ((), .eq)

def readyTapes (items : RawInstance) (assignments remaining : List Nat) (selected : Nat) :
    Tape → List Bool :=
  ExtensionMachinePlacement.tapes innerView
    (ExtensionCapacityMachine.initialTapes items assignments selected)
    (stageTapes items assignments remaining)

def prepareSelectedInTime (items : RawInstance) (assignments remaining : List Nat)
    (selected : Nat) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
      (some (configuration (some (.inner ExtensionCapacityMachine.machine.main))
        (readyTapes items assignments remaining selected)))
      (1 + (2 * selected.size + 2) +
        2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
        2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
  let stage := stageTapes items assignments remaining
  let framed := Function.update stage 24
    (BinaryEncoding.natBits selected ++ BinaryEncoding.assignmentBits remaining)
  let parsed := Function.update stage 4 selected.bits
  let copiedItems := Function.update parsed 2 (BinaryEncoding.rawInstanceBits items)
  have guardRun : StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
      (some (configuration (some (.number .scan)) framed)) 1 := {
    steps := 1
    evals_in_steps := by
      change machine.step
        (configuration (some .guard) (stageTapes items assignments (selected :: remaining))) =
        some (configuration (some (.number .scan)) framed)
      have step := guardStep (stageTapes items assignments (selected :: remaining)) true
        (BinaryEncoding.natBits selected ++ BinaryEncoding.assignmentBits remaining)
        (by simp [stageTapes, BinaryEncoding.assignmentBits, BinaryEncoding.listBits])
      have updated : Function.update (stageTapes items assignments (selected :: remaining)) 24
          (BinaryEncoding.natBits selected ++ BinaryEncoding.assignmentBits remaining) = framed := by
        funext k
        by_cases same : k = 24 <;> simp [framed, stage, stageTapes, same]
      simpa only [↓reduceIte, updated] using step
    steps_le_m := Nat.le_refl _ }
  have parseRun := selectedInTime framed selected remaining
    (by simp [framed]) (by simp [framed, stage, stageTapes])
  have parseFinal : ExtensionNatMachine.resultTapes numberTapes framed selected
      (BinaryEncoding.assignmentBits remaining) = parsed := by
    funext k
    fin_cases k <;>
      simp [ExtensionNatMachine.resultTapes, numberTapes, framed, parsed, stage, stageTapes]
  rw [parseFinal] at parseRun
  have itemsRun := copyInTime .items parsed (by simp [parsed, stage, stageTapes])
  have itemsRun' : StateTransition.EvalsToInTime machine.step
      (configuration (some (.copyOut .items)) parsed)
      (some (configuration (some (.copyOut .assignments)) copiedItems))
      (2 * ((BinaryEncoding.rawInstanceBits items).length + 1)) := by
    have source : parsed 22 = BinaryEncoding.rawInstanceBits items := by
      simp [parsed, stage, stageTapes]
    have destination : parsed 2 = [] := by simp [parsed, stage, stageTapes]
    simpa only [copySource, copyDestination, afterCopy, source, destination,
      List.append_nil, copiedItems] using itemsRun
  have assignmentsRun := copyInTime .assignments copiedItems
    (by simp [copiedItems, parsed, stage, stageTapes])
  have assignmentsFinal : Function.update copiedItems 3
      (BinaryEncoding.assignmentBits assignments) = readyTapes items assignments remaining selected := by
    funext k
    fin_cases k <;>
      simp [copiedItems, parsed, stage, stageTapes, readyTapes,
        ExtensionMachinePlacement.tapes, innerView, ExtensionCapacityMachine.initialTapes]
  have assignmentsRun' : StateTransition.EvalsToInTime machine.step
      (configuration (some (.copyOut .assignments)) copiedItems)
      (some (configuration (some (.inner ExtensionCapacityMachine.machine.main))
        (readyTapes items assignments remaining selected)))
      (2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
    have source : copiedItems 23 = BinaryEncoding.assignmentBits assignments := by
      simp [copiedItems, parsed, stage, stageTapes]
    have destination : copiedItems 3 = [] := by simp [copiedItems, parsed, stage, stageTapes]
    simpa only [copySource, copyDestination, afterCopy, source, destination,
      List.append_nil, assignmentsFinal] using assignmentsRun
  have firstTwo := join guardRun parseRun
  have firstThree := join firstTwo itemsRun'
  exact join firstThree assignmentsRun'

def innerExecution (extra : Tape → List Bool)
    {start finish : ExtensionCapacityMachine.machine.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime ExtensionCapacityMachine.machine.step
      start (some finish) budget) :
    StateTransition.EvalsToInTime machine.step
      (ExtensionMachinePlacement.configuration innerView Label.inner (some .afterInner)
        (ExtensionMachineRegisters.Lens.identity State) clean extra start)
      (some (ExtensionMachinePlacement.configuration innerView Label.inner (some .afterInner)
        (ExtensionMachineRegisters.Lens.identity State) clean extra finish)) budget :=
  ExtensionMachinePlacement.execution innerTape innerView innerView_left innerView_right
    Label.inner (some .afterInner) (ExtensionMachineRegisters.Lens.identity State)
    clean extra ExtensionCapacityMachine.machine.m program (fun _ => rfl) run

theorem inner_initial_configuration (items : RawInstance) (assignments remaining : List Nat)
    (selected : Nat) :
    ExtensionMachinePlacement.configuration innerView Label.inner (some .afterInner)
      (ExtensionMachineRegisters.Lens.identity State) clean
      (stageTapes items assignments remaining)
      (ExtensionCapacityMachine.initialCfg items assignments selected) =
    configuration (some (.inner ExtensionCapacityMachine.machine.main))
      (readyTapes items assignments remaining selected) := rfl

theorem inner_final_configuration (items : RawInstance) (assignments remaining : List Nat)
    (result : Bool) :
    ExtensionMachinePlacement.configuration innerView Label.inner (some .afterInner)
      (ExtensionMachineRegisters.Lens.identity State) clean
      (stageTapes items assignments remaining) (ExtensionCapacityMachine.finalCfg result) =
    configuration (some .afterInner)
      (Function.update (stageTapes items assignments remaining) 0 [result]) := by
  change (⟨some .afterInner, clean, _⟩ : machine.Cfg) = ⟨some .afterInner, clean, _⟩
  congr 1
  funext k
  fin_cases k <;>
    simp [ExtensionMachinePlacement.tapes, innerView, ExtensionCapacityMachine.finalCfg,
      ExtensionCapacityMachine.finalTapes, stageTapes]

def afterInnerInTime (items : RawInstance) (assignments remaining : List Nat)
    (result : Bool) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .afterInner)
        (Function.update (stageTapes items assignments remaining) 0 [result]))
      (some (configuration (if result then some .guard else cleanupEntry false)
        (stageTapes items assignments remaining))) 1 where
  steps := 1
  evals_in_steps := by
    change machine.step (configuration (some .afterInner)
      (Function.update (stageTapes items assignments remaining) 0 [result])) =
      some (configuration (if result then some .guard else cleanupEntry false)
        (stageTapes items assignments remaining))
    have step := afterInnerStep
      (Function.update (stageTapes items assignments remaining) 0 [result]) result (by simp)
    have reset : Function.update (Function.update (stageTapes items assignments remaining) 0 [result])
        0 [] = stageTapes items assignments remaining := by
      rw [Function.update_idem]
      have initial : stageTapes items assignments remaining 0 = [] := by simp [stageTapes]
      rw [← initial]
      simp
    simpa only [reset] using step
  steps_le_m := Nat.le_refl _

theorem stage_lengthSum (items : RawInstance) (assignments remaining : List Nat) :
    MachineDrainMany.lengthSum allTapes (stageTapes items assignments remaining) =
      (BinaryEncoding.rawInstanceBits items).length +
      (BinaryEncoding.assignmentBits assignments).length +
      (BinaryEncoding.assignmentBits remaining).length := by
  simp [MachineDrainMany.lengthSum, allTapes, List.ofFn_succ, stageTapes, Nat.add_assoc]

theorem ended_lengthSum (items : RawInstance) (assignments : List Nat) :
    MachineDrainMany.lengthSum allTapes
      (Function.update (stageTapes items assignments []) 24 []) =
      (BinaryEncoding.rawInstanceBits items).length +
      (BinaryEncoding.assignmentBits assignments).length := by
  simp [MachineDrainMany.lengthSum, allTapes, List.ofFn_succ, stageTapes]

theorem cleanup_tapes (base : Tape → List Bool) :
    MachineDrainMany.finalTapes allTapes base = fun _ => [] := by
  funext k
  apply MachineDrainMany.finalTapes_mem
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

def cleanupInTime (result : Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime machine.step
      (configuration (cleanupEntry result) base)
      (some (configuration none (resultTapes result)))
      (MachineDrainMany.lengthSum allTapes base + 27) := by
  have first := MachineDrainMany.execution allTapes (Label.cleanup result)
    (some (.emit result)) program (fun _ => rfl) base
    ((((), .eq), false), none) none
  rw [cleanup_tapes] at first
  have first' : StateTransition.EvalsToInTime machine.step
      (configuration (cleanupEntry result) base)
      (some (configuration (some (.emit result)) (fun _ => [])))
      (MachineDrainMany.lengthSum allTapes base + 26) := by
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨cleanupEntry result, clean, base⟩
      (some ⟨some (.emit result), clean, fun _ => []⟩) _
    simpa only [cleanupEntry, configuration, clean, BinaryAddMachine.clean,
      BinaryAddMachine.state, MachineDrainMany.finalRegister_none,
      allTapes, List.length_ofFn] using first
  have second : StateTransition.EvalsToInTime machine.step
      (configuration (some (.emit result)) (fun _ => []))
      (some (configuration none (resultTapes result))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (.emit result)) clean (fun _ => [])) = _
      simp only [program, TM2.stepAux, configuration]
      congr 1
    steps_le_m := Nat.le_refl _ }
  have combined := join first' second
  have clock : MachineDrainMany.lengthSum allTapes base + 26 + 1 =
      MachineDrainMany.lengthSum allTapes base + 27 := by omega
  rw [clock] at combined
  exact combined

def emptyInTime (items : RawInstance) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments []))
      (some (configuration none (resultTapes true)))
      ((BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length + 28) := by
  have first : StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments []))
      (some (configuration (cleanupEntry true)
        (Function.update (stageTapes items assignments []) 24 []))) 1 := {
    steps := 1
    evals_in_steps := by
      change machine.step (configuration (some .guard) (stageTapes items assignments [])) =
        some (configuration (cleanupEntry true)
          (Function.update (stageTapes items assignments []) 24 []))
      simpa only [Bool.false_eq_true, ↓reduceIte] using guardStep (stageTapes items assignments []) false []
        (by simp [stageTapes, BinaryEncoding.assignmentBits, BinaryEncoding.listBits])
    steps_le_m := Nat.le_refl _ }
  have second := cleanupInTime true (Function.update (stageTapes items assignments []) 24 [])
  have combined := join first second
  have clock : 1 +
      (MachineDrainMany.lengthSum allTapes
        (Function.update (stageTapes items assignments []) 24 []) + 27) =
      (BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length + 28 := by
    rw [ended_lengthSum]
    omega
  rw [clock] at combined
  exact combined

private abbrev InnerRuns (items : RawInstance) (assignments : List Nat) :=
  ∀ selected : Nat, StateTransition.EvalsToInTime ExtensionCapacityMachine.machine.step
    (ExtensionCapacityMachine.initialCfg items assignments selected)
    (some (ExtensionCapacityMachine.finalCfg
      (CapacityScan.scan selected items assignments (0, 1))))
    (ExtensionCapacityMachine.timePolynomial.eval
      (ExtensionCapacityMachine.inputLength items assignments selected))

private noncomputable def roundFromInner (items : RawInstance) (assignments remaining : List Nat)
    (selected : Nat) (member : selected ∈ assignments) (innerRuns : InnerRuns items assignments) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
      (some (configuration
        (if CapacityScan.scan selected items assignments (0, 1) then some .guard
          else cleanupEntry false) (stageTapes items assignments remaining)))
      (roundBudget ((BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length)) := by
  have prepare := prepareSelectedInTime items assignments remaining selected
  have placed := innerExecution (stageTapes items assignments remaining) (innerRuns selected)
  have placed' : StateTransition.EvalsToInTime machine.step
      (configuration (some (.inner ExtensionCapacityMachine.machine.main))
        (readyTapes items assignments remaining selected))
      (some (configuration (some .afterInner)
        (Function.update (stageTapes items assignments remaining) 0
          [CapacityScan.scan selected items assignments (0, 1)])))
      (ExtensionCapacityMachine.timePolynomial.eval
        (ExtensionCapacityMachine.inputLength items assignments selected)) := by
    erw [inner_initial_configuration, inner_final_configuration] at placed
    exact placed
  have finish := afterInnerInTime items assignments remaining
    (CapacityScan.scan selected items assignments (0, 1))
  have firstTwo := join prepare placed'
  have complete := join firstTwo finish
  have selectedWidth := selected_size_le_encoding selected assignments member
  have innerBound := MachineComposition.natPolynomial_eval_mono
    ExtensionCapacityMachine.timePolynomial
    (show ExtensionCapacityMachine.inputLength items assignments selected ≤
      2 * ((BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length) by
      unfold ExtensionCapacityMachine.inputLength
      omega)
  refine { toEvalsTo := complete.toEvalsTo, steps_le_m := complete.steps_le_m.trans ?_ }
  unfold roundBudget
  omega

private noncomputable def loopBudget (items : RawInstance) (assignments remaining : List Nat) : Nat :=
  remaining.length * roundBudget ((BinaryEncoding.rawInstanceBits items).length +
    (BinaryEncoding.assignmentBits assignments).length) +
    (BinaryEncoding.rawInstanceBits items).length +
    2 * (BinaryEncoding.assignmentBits assignments).length + 28

private noncomputable def loopFromInner (items : RawInstance) (assignments remaining : List Nat)
    (suffix : ∃ before, assignments = before ++ remaining)
    (innerRuns : InnerRuns items assignments) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments remaining))
      (some (configuration none (resultTapes (scanResult items assignments remaining))))
      (loopBudget items assignments remaining) := by
  induction remaining with
  | nil =>
      have run := emptyInTime items assignments
      refine { toEvalsTo := run.toEvalsTo, steps_le_m := run.steps_le_m.trans ?_ }
      simp only [loopBudget, List.length_nil, Nat.zero_mul, Nat.zero_add]
      omega
  | cons selected remaining ih =>
      have member : selected ∈ assignments := by
        obtain ⟨before, equality⟩ := suffix
        rw [equality]
        simp
      have tailSuffix : ∃ before, assignments = before ++ remaining := by
        obtain ⟨before, equality⟩ := suffix
        exact ⟨before ++ [selected],
          by simpa only [List.append_assoc, List.singleton_append] using equality⟩
      have round := roundFromInner items assignments remaining selected member innerRuns
      cases answer : CapacityScan.scan selected items assignments (0, 1) with
      | false =>
          have round' : StateTransition.EvalsToInTime machine.step
              (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
              (some (configuration (cleanupEntry false) (stageTapes items assignments remaining)))
              (roundBudget ((BinaryEncoding.rawInstanceBits items).length +
                (BinaryEncoding.assignmentBits assignments).length)) := by
            simpa only [answer, Bool.false_eq_true, ↓reduceIte] using round
          have cleaned := cleanupInTime false (stageTapes items assignments remaining)
          have complete := join round' cleaned
          have tailEncoding : (BinaryEncoding.assignmentBits remaining).length ≤
              (BinaryEncoding.assignmentBits assignments).length := by
            obtain ⟨before, rfl⟩ := tailSuffix
            exact suffix_encoding_length_le before remaining
          have clock : roundBudget ((BinaryEncoding.rawInstanceBits items).length +
                  (BinaryEncoding.assignmentBits assignments).length) +
                (MachineDrainMany.lengthSum allTapes (stageTapes items assignments remaining) + 27) ≤
              loopBudget items assignments (selected :: remaining) := by
            rw [stage_lengthSum]
            simp only [loopBudget, List.length_cons, Nat.add_mul, Nat.one_mul]
            omega
          have enlarged : StateTransition.EvalsToInTime machine.step
              (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
              (some (configuration none (resultTapes false)))
              (loopBudget items assignments (selected :: remaining)) :=
            { toEvalsTo := complete.toEvalsTo, steps_le_m := complete.steps_le_m.trans clock }
          simpa only [scanResult, List.all_cons, answer, Bool.false_and] using enlarged
      | true =>
          have round' : StateTransition.EvalsToInTime machine.step
              (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
              (some (configuration (some .guard) (stageTapes items assignments remaining)))
              (roundBudget ((BinaryEncoding.rawInstanceBits items).length +
                (BinaryEncoding.assignmentBits assignments).length)) := by
            simpa only [answer, ↓reduceIte] using round
          have tailRun := ih tailSuffix
          have complete := join round' tailRun
          have clock : roundBudget ((BinaryEncoding.rawInstanceBits items).length +
                  (BinaryEncoding.assignmentBits assignments).length) +
                loopBudget items assignments remaining =
              loopBudget items assignments (selected :: remaining) := by
            simp only [loopBudget, List.length_cons, Nat.add_mul, Nat.one_mul]
            omega
          simpa only [clock, scanResult, List.all_cons, answer, Bool.true_and] using complete

noncomputable def outerInPolynomialTime (items : RawInstance) (assignments : List Nat)
    (valid : items.Valid) (sameLength : assignments.length = items.length) :
    StateTransition.EvalsToInTime machine.step
      (initialCfg items assignments)
      (some (finalCfg (assignments.all (ExtensionCertificate.capacityCheck items assignments))))
      (timePolynomial.eval (inputLength items assignments)) := by
  have first := initialCopyInTime items assignments
  have loops := loopFromInner items assignments assignments ⟨[], rfl⟩
    (fun selected => ExtensionCapacityMachine.innerInPolynomialTime
      items assignments selected valid sameLength)
  have complete := join first loops
  have labelCount : assignments.length ≤ inputLength items assignments := by
    have bound := BinaryEncoding.list_length_le_bits_length BinaryEncoding.natBits assignments
    change assignments.length ≤ (BinaryEncoding.assignmentBits assignments).length at bound
    unfold inputLength
    omega
  have budget := totalBudget_le (BinaryEncoding.rawInstanceBits items).length
    (BinaryEncoding.assignmentBits assignments).length assignments.length labelCount
  have clock : 2 * ((BinaryEncoding.assignmentBits assignments).length + 1) +
      loopBudget items assignments assignments ≤ timePolynomial.eval (inputLength items assignments) := by
    unfold loopBudget inputLength
    omega
  have enlarged : StateTransition.EvalsToInTime machine.step
      (initialCfg items assignments)
      (some (finalCfg (scanResult items assignments assignments)))
      (timePolynomial.eval (inputLength items assignments)) :=
    { toEvalsTo := complete.toEvalsTo, steps_le_m := complete.steps_le_m.trans clock }
  simpa only [scanResult_eq_capacityChecks items valid assignments assignments] using enlarged

end BinPackingGap.ExtensionCapacityOuterMachine

namespace BinPackingGap.ExtensionVerifierMachine

open Turing BinPackingGames.Foundations.Complexity
open ExtensionMachineRegisters (Lens)

inductive Helper
  | pair | query | witness | fields | validation | agreement | capacity
  deriving DecidableEq

protected abbrev Helper.enumList : List Helper := [.pair, .query, .witness, .fields, .validation,
  .agreement, .capacity]

protected theorem Helper.enumList_getElem?_ctorIdx_eq (x : Helper) :
    Helper.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Helper.enumList_nodup : Helper.enumList.Nodup := by decide

instance : Fintype Helper where
  elems := ⟨Helper.enumList, Helper.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev LocalTape : Helper → Type
  | .pair | .query | .witness => Fin 3
  | .fields => Fin 7
  | .validation => Fin 10
  | .agreement => Fin 2
  | .capacity => Fin 26

abbrev LocalLabel : Helper → Type
  | .pair => ExtensionPairMachine.Label
  | .query | .witness => ExtensionShapeMachine.Label
  | .fields => Fields.Label
  | .validation => ExtensionValidationMachine.Label
  | .agreement => ExtensionAgreementMachine.Label
  | .capacity => ExtensionCapacityOuterMachine.Label

abbrev LocalState : Helper → Type
  | .pair => ExtensionPairMachine.State
  | .query | .witness => ExtensionShapeMachine.State
  | .fields => Fields.State
  | .validation => ExtensionValidationMachine.State
  | .agreement => ExtensionAgreementMachine.State
  | .capacity => ExtensionCapacityOuterMachine.State

instance (h : Helper) : Fintype (LocalTape h) := by cases h <;> infer_instance
instance (h : Helper) : DecidableEq (LocalTape h) := by cases h <;> infer_instance
instance (h : Helper) : Fintype (LocalLabel h) := by cases h <;> infer_instance
instance (h : Helper) : DecidableEq (LocalLabel h) := by cases h <;> infer_instance
instance (h : Helper) : Fintype (LocalState h) := by cases h <;> infer_instance
instance (h : Helper) : DecidableEq (LocalState h) := by cases h <;> infer_instance

def localInitial : (h : Helper) → LocalState h
  | .pair => ExtensionPairMachine.machine.initialState
  | .query => (ExtensionShapeMachine.machine .extension).initialState
  | .witness => (ExtensionShapeMachine.machine .assignments).initialState
  | .fields => Fields.machine.initialState
  | .validation => ExtensionValidationMachine.machine.initialState
  | .agreement => ExtensionAgreementMachine.machine.initialState
  | .capacity => ExtensionCapacityOuterMachine.machine.initialState

def localMain : (h : Helper) → LocalLabel h
  | .pair => ExtensionPairMachine.machine.main
  | .query => (ExtensionShapeMachine.machine .extension).main
  | .witness => (ExtensionShapeMachine.machine .assignments).main
  | .fields => Fields.machine.main
  | .validation => ExtensionValidationMachine.machine.main
  | .agreement => ExtensionAgreementMachine.machine.main
  | .capacity => ExtensionCapacityOuterMachine.machine.main

def localProgram : (h : Helper) →
    LocalLabel h → TM2.Stmt (fun _ : LocalTape h => Bool) (LocalLabel h) (LocalState h)
  | .pair => ExtensionPairMachine.machine.m
  | .query => (ExtensionShapeMachine.machine .extension).m
  | .witness => (ExtensionShapeMachine.machine .assignments).m
  | .fields => Fields.machine.m
  | .validation => ExtensionValidationMachine.machine.m
  | .agreement => ExtensionAgreementMachine.machine.m
  | .capacity => ExtensionCapacityOuterMachine.machine.m

abbrev Tape := Fin 40
abbrev Registers := (h : Helper) → LocalState h
abbrev State := Registers × Option Bool
abbrev Alphabet (_ : Tape) := Bool

def clean : State := (localInitial, none)

def register (h : Helper) : Lens State (LocalState h) where
  get state := state.1 h
  set state value := (Function.update state.1 h value, state.2)
  get_set := by intros; simp
  set_get := by intros; simp
  set_set := by intros; simp

@[simp] theorem register_clean (h : Helper) :
    (register h).set clean (localInitial h) = clean := by
  simp [register, clean]

def slot : (h : Helper) → LocalTape h → Tape
  | .pair => ![0, 1, 2]
  | .query => ![1, 3, 2]
  | .witness => ![0, 4, 2]
  | .fields => ![3, 5, 6, 7, 8, 9, 10]
  | .validation => ![8, 12, 13, 14, 15, 16, 17, 11, 18, 19]
  | .agreement => ![10, 13]
  | .capacity => ![15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 9, 4, 37, 38]

def view : (h : Helper) → Tape → Option (LocalTape h)
  | .pair, k => match k.val with
      | 0 => some 0
      | 1 => some 1
      | 2 => some 2
      | _ => none
  | .query, k => match k.val with
      | 1 => some 0
      | 3 => some 1
      | 2 => some 2
      | _ => none
  | .witness, k => match k.val with
      | 0 => some 0
      | 4 => some 1
      | 2 => some 2
      | _ => none
  | .fields, k => match k.val with
      | 3 => some 0
      | 5 => some 1
      | 6 => some 2
      | 7 => some 3
      | 8 => some 4
      | 9 => some 5
      | 10 => some 6
      | _ => none
  | .validation, k => match k.val with
      | 8 => some 0
      | 12 => some 1
      | 13 => some 2
      | 14 => some 3
      | 15 => some 4
      | 16 => some 5
      | 17 => some 6
      | 11 => some 7
      | 18 => some 8
      | 19 => some 9
      | _ => none
  | .agreement, k => match k.val with
      | 10 => some 0
      | 13 => some 1
      | _ => none
  | .capacity, k => match k.val with
      | 15 => some 0
      | 16 => some 1
      | 17 => some 2
      | 18 => some 3
      | 19 => some 4
      | 20 => some 5
      | 21 => some 6
      | 22 => some 7
      | 23 => some 8
      | 24 => some 9
      | 25 => some 10
      | 26 => some 11
      | 27 => some 12
      | 28 => some 13
      | 29 => some 14
      | 30 => some 15
      | 31 => some 16
      | 32 => some 17
      | 33 => some 18
      | 34 => some 19
      | 35 => some 20
      | 36 => some 21
      | 9 => some 22
      | 4 => some 23
      | 37 => some 24
      | 38 => some 25
      | _ => none

theorem view_slot (h : Helper) (k : LocalTape h) : view h (slot h k) = some k := by
  cases h <;> fin_cases k <;> rfl

theorem slot_view (h : Helper) (j : Tape) (k : LocalTape h)
    (found : view h j = some k) : slot h k = j := by
  cases h <;> fin_cases j <;> simp only [view] at found
  all_goals
    first
    | contradiction
    | have equal := Option.some.inj found
      subst k
      rfl

def put (h : Helper) (localTapes : LocalTape h → List Bool) (base : Tape → List Bool) :
    Tape → List Bool := ExtensionMachinePlacement.tapes (view h) localTapes base

@[simp] theorem put_slot (h : Helper) (localTapes : LocalTape h → List Bool)
    (base : Tape → List Bool) (k : LocalTape h) :
    put h localTapes base (slot h k) = localTapes k :=
  ExtensionMachinePlacement.tapes_apply (slot h) (view h) (view_slot h) localTapes base k

theorem put_restrict (h : Helper) (base : Tape → List Bool) :
    put h (fun k => base (slot h k)) base = base :=
  ExtensionMachinePlacement.tapes_restrict (slot h) (view h) (slot_view h) base

inductive Gate
  | query | witness | validation | agreement | capacity
  deriving DecidableEq

protected abbrev Gate.enumList : List Gate := [.query, .witness, .validation, .agreement,
  .capacity]

protected theorem Gate.enumList_getElem?_ctorIdx_eq (x : Gate) :
    Gate.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Gate.enumList_nodup : Gate.enumList.Nodup := by decide

instance : Fintype Gate where
  elems := ⟨Gate.enumList, Gate.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Copy
  | items | validationAssignments | agreementAssignments
  deriving DecidableEq

protected abbrev Copy.enumList : List Copy := [.items, .validationAssignments,
  .agreementAssignments]

protected theorem Copy.enumList_getElem?_ctorIdx_eq (x : Copy) :
    Copy.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Copy.enumList_nodup : Copy.enumList.Nodup := by decide

instance : Fintype Copy where
  elems := ⟨Copy.enumList, Copy.enumList_nodup⟩
  complete x := by cases x <;> decide

def allTapes : List Tape := List.ofFn id

inductive Label
  | helper (h : Helper) (phase : LocalLabel h)
  | gate (phase : Gate)
  | copyOut (phase : Copy)
  | copyBack (phase : Copy)
  | cleanup (result : Bool) (phase : MachineDrainMany.Label allTapes)
  | emit (result : Bool)
  deriving DecidableEq, Fintype

def entry (h : Helper) : Label := .helper h (localMain h)

def cleanupEntry (result : Bool) : Option Label :=
  MachineDrainMany.entry allTapes (.cleanup result) (some (.emit result))

def afterHelper : Helper → Label
  | .pair => entry .query
  | .query => .gate .query
  | .witness => .gate .witness
  | .fields => .copyOut .items
  | .validation => .gate .validation
  | .agreement => .gate .agreement
  | .capacity => .gate .capacity

def gateTape : Gate → Tape
  | .query => 3
  | .witness => 4
  | .validation => 8
  | .agreement => 10
  | .capacity => 15

def afterGate : Gate → Option Label
  | .query => some (entry .witness)
  | .witness => some (entry .fields)
  | .validation => some (.copyOut .agreementAssignments)
  | .agreement => some (entry .capacity)
  | .capacity => cleanupEntry true

def copySource : Copy → Tape
  | .items => 9
  | .validationAssignments | .agreementAssignments => 4

def copyDestination : Copy → Tape
  | .items => 12
  | .validationAssignments | .agreementAssignments => 13

def afterCopy : Copy → Label
  | .items => .copyOut .validationAssignments
  | .validationAssignments => entry .validation
  | .agreementAssignments => entry .agreement

def jump (next : Option Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => clean) (match next with
    | some l => .goto fun _ => l
    | none => .halt)

def program : Label → TM2.Stmt Alphabet Label State
  | .helper h phase =>
      ExtensionMachinePlacement.statement (slot h) (.helper h)
        (some (afterHelper h)) (register h) (localProgram h phase)
  | .gate phase =>
      .pop (gateTape phase) (fun state bit => (state.1, bit))
        (.branch (fun state => state.2.getD false)
          (jump (afterGate phase)) (jump (cleanupEntry false)))
  | .copyOut phase =>
      BinPackingGames.Reduction.MachineTransfer.loopAt (copySource phase) 11 id false
        (.copyOut phase) (some (.copyBack phase))
  | .copyBack phase =>
      MachineCopy.forkLoop 11 (copySource phase) (copyDestination phase) false
        (.copyBack phase) (some (afterCopy phase))
  | .cleanup result phase =>
      MachineDrainMany.instruction allTapes (.cleanup result) (some (.emit result)) phase
  | .emit result => .push 0 (fun _ => result) (.load (fun _ => clean) .halt)

def machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := entry .pair
  σ := State
  initialState := clean
  m := program

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

def cfg (label : Option Label) (tapes : Tape → List Bool) : machine.Cfg :=
  ⟨label, clean, tapes⟩

def stagedTapes (query witness bins items fixed bound itemCopy assignmentCopy : List Bool) :
    Tape → List Bool := fun k =>
  if k = 3 then query else if k = 4 then witness else if k = 8 then bins
  else if k = 9 then items else if k = 10 then fixed else if k = 14 then bound
  else if k = 12 then itemCopy else if k = 13 then assignmentCopy else []

def fieldInput (query witness : List Bool) : Tape → List Bool :=
  stagedTapes query witness [] [] [] [] [] []

def oneStep {start finish : machine.Cfg} (step : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := step
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
  steps_le_m := run.steps_le_m.trans bounded

def callInTime (h : Helper) (base : Tape → List Bool)
    (start finish : TM2.Cfg (fun _ : LocalTape h => Bool) (LocalLabel h) (LocalState h))
    (budget : Nat)
    (run : StateTransition.EvalsToInTime (TM2.step (localProgram h)) start (some finish) budget)
    (startLabel : start.l = some (localMain h)) (endLabel : finish.l = none)
    (startState : start.var = localInitial h) (endState : finish.var = localInitial h)
    (inputs : ∀ k, base (slot h k) = start.stk k) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry h)) base)
      (some (cfg (some (afterHelper h)) (put h finish.stk base))) budget := by
  have transported := ExtensionMachinePlacement.execution (slot h) (view h)
    (view_slot h) (slot_view h) (.helper h) (some (afterHelper h))
    (register h) clean base (localProgram h) program (fun _ => rfl) run
  have tapesEqual : put h start.stk base = base := by
    rw [show start.stk = fun k => base (slot h k) from funext fun k => (inputs k).symm]
    exact put_restrict h base
  change ExtensionMachinePlacement.tapes (view h) start.stk base = base at tapesEqual
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.helper h (localMain h)), clean, base⟩
    (some ⟨some (afterHelper h), clean,
      ExtensionMachinePlacement.tapes (view h) finish.stk base⟩) budget
  simpa only [ExtensionMachinePlacement.configuration, ExtensionMachinePlacement.label,
    startLabel, endLabel, startState, endState, register_clean, tapesEqual] using transported

theorem gateStep (gate : Gate) (base : Tape → List Bool) (result : Bool) (tail : List Bool)
    (word : base (gateTape gate) = result :: tail) :
    machine.step (cfg (some (.gate gate)) base) =
      some (cfg (if result then afterGate gate else cleanupEntry false)
        (Function.update base (gateTape gate) tail)) := by
  cases result <;> cases good : afterGate gate <;> cases bad : cleanupEntry false <;>
    simp [FinTM2.step, TM2.step, machine, cfg, program, TM2.stepAux, word, jump, good, bad] <;> rfl

def copyInTime (phase : Copy) (base : Tape → List Bool) (scratchEmpty : base 11 = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.copyOut phase)) base)
      (some (cfg (some (afterCopy phase))
        (Function.update base (copyDestination phase)
          (base (copySource phase) ++ base (copyDestination phase)))))
      (2 * ((base (copySource phase)).length + 1)) := by
  exact MachineCopy.copyInTime (copySource phase) (copyDestination phase) 11
    (by cases phase <;> decide) (by cases phase <;> decide) (by cases phase <;> decide)
    false (.copyOut phase) (.copyBack phase) (some (afterCopy phase)) program rfl rfl
    base scratchEmpty localInitial none

theorem cleanup_tapes (base : Tape → List Bool) :
    MachineDrainMany.finalTapes allTapes base = fun _ => [] := by
  funext k
  apply MachineDrainMany.finalTapes_mem
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

def resultTapes (result : Bool) : Tape → List Bool :=
  Function.update (fun _ => []) 0 [result]

def cleanupInTime (result : Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime machine.step (cfg (cleanupEntry result) base)
      (some (cfg none (resultTapes result)))
      (MachineDrainMany.lengthSum allTapes base + 41) := by
  have first := MachineDrainMany.execution allTapes (.cleanup result)
    (some (.emit result)) program (fun _ => rfl) base localInitial none
  rw [cleanup_tapes] at first
  have first' : StateTransition.EvalsToInTime machine.step
      (cfg (cleanupEntry result) base)
      (some (cfg (some (.emit result)) (fun _ => [])))
      (MachineDrainMany.lengthSum allTapes base + 40) := by
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨cleanupEntry result, clean, base⟩
      (some ⟨some (.emit result), clean, fun _ => []⟩) _
    simpa only [clean, MachineDrainMany.finalRegister_none,
      cleanupEntry, allTapes, List.length_ofFn] using first
  have second := oneStep (show machine.step (cfg (some (.emit result)) (fun _ => [])) =
      some (cfg none (resultTapes result)) from by
    simp [FinTM2.step, machine, TM2.step, TM2.stepAux, program, cfg, clean, resultTapes]
    rfl)
  simpa only [Nat.add_assoc] using join first' second

end BinPackingGap.ExtensionVerifierMachine

end OAI
