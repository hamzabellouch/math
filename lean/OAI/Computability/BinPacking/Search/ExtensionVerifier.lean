import OAI.Computability.BinPacking.Search.ExtensionVerifierPipeline

namespace OAI

namespace BinPackingGap.ExtensionVerifierMachine

open Turing BinPackingGames.Foundations.Complexity

def frontTapes (zero one three four : List Bool) : Tape → List Bool := fun k =>
  if k = 0 then zero else if k = 1 then one else if k = 3 then three
  else if k = 4 then four else []

def frontendAccepted (query witness : List Bool) : Bool :=
  (BinaryEncoding.decodeExtension query).isSome &&
    (BinaryEncoding.decodeAssignments witness).isSome

def frontendExit (query witness : List Bool) : Option Label :=
  if frontendAccepted query witness then some (entry .fields) else cleanupEntry false

def frontendTapes (query witness : List Bool) : Tape → List Bool :=
  if (BinaryEncoding.decodeExtension query).isSome then fieldInput query witness
  else frontTapes witness [] query []

@[simp] theorem frontTapes_fieldInput (query witness : List Bool) :
    frontTapes [] [] query witness = fieldInput query witness := by
  funext k
  fin_cases k <;> simp [frontTapes, fieldInput, stagedTapes]

theorem frontend_of_decoded (query witness : List Bool)
    (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) (assignments : List Nat)
    (queryDecoded : BinaryEncoding.decodeExtension query = some (bins, items, fixed))
    (witnessDecoded : BinaryEncoding.decodeAssignments witness = some assignments) :
    frontendExit query witness = some (entry .fields) ∧
      frontendTapes query witness = fieldInput query witness := by
  simp [frontendExit, frontendAccepted, frontendTapes, queryDecoded, witnessDecoded]

def pairedInputInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (CookLevin.pairBits (query, witness)))
      (some (cfg (some (entry .query)) (frontTapes witness query [] [])))
      (3 * query.length + 4) := by
  let base := frontTapes (CookLevin.pairBits (query, witness)) [] [] []
  have call := callInTime .pair base
    (initList ExtensionPairMachine.machine (CookLevin.pairBits (query, witness)))
    (ExtensionPairMachine.cfg none witness query []) (3 * query.length + 4)
    (ExtensionPairMachine.pairHaltInTime query witness) rfl rfl rfl rfl
    (by
      intro k
      fin_cases k <;>
        simp [base, frontTapes, slot, initList, ExtensionPairMachine.machine,
          BinPackingCompleteness.BinaryPairMachine.machine])
  have initial : cfg (some (entry .pair)) base =
      initList machine (CookLevin.pairBits (query, witness)) := by
    change (⟨some (entry .pair), clean, base⟩ : machine.Cfg) = ⟨some (entry .pair), clean, _⟩
    congr 1
    funext k
    fin_cases k <;> simp [base, frontTapes, machine]
    rfl
  have final : put .pair (ExtensionPairMachine.cfg none witness query []).stk base =
      frontTapes witness query [] [] := by
    funext k
    fin_cases k <;>
      simp [put, ExtensionMachinePlacement.tapes, view, base, frontTapes,
        ExtensionPairMachine.cfg, BinPackingCompleteness.BinaryPairMachine.cfg,
        BinPackingCompleteness.BinaryPairMachine.tapes]
  simpa only [initial, final, afterHelper] using call

def queryShapeInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry .query)) (frontTapes witness query [] []))
      (some (cfg (some (.gate .query))
        (frontTapes witness []
          (ExtensionShapeMachine.decodeAccepts .extension query :: query) [])))
      (2 * query.length + 3) := by
  let base := frontTapes witness query [] []
  let output := ExtensionShapeMachine.decodeAccepts .extension query :: query
  have call := callInTime .query base
    (initList (ExtensionShapeMachine.machine .extension) query)
    (haltList (ExtensionShapeMachine.machine .extension) output) (2 * query.length + 3)
    (ExtensionShapeMachine.outputsInTime .extension query) rfl rfl rfl rfl
    (by
      intro k
      fin_cases k <;> simp [base, frontTapes, slot, initList, ExtensionShapeMachine.machine])
  have final : put .query (haltList (ExtensionShapeMachine.machine .extension) output).stk base =
      frontTapes witness [] output [] := by
    funext k
    fin_cases k <;>
      simp [put, ExtensionMachinePlacement.tapes, view, base, frontTapes,
        haltList, ExtensionShapeMachine.machine]
  simpa only [base, final, afterHelper, output] using call

def queryGateInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.gate .query))
        (frontTapes witness []
          (ExtensionShapeMachine.decodeAccepts .extension query :: query) []))
      (some (cfg
        (if ExtensionShapeMachine.decodeAccepts .extension query then
          some (entry .witness) else cleanupEntry false)
        (frontTapes witness [] query []))) 1 := by
  have step := gateStep .query
    (frontTapes witness [] (ExtensionShapeMachine.decodeAccepts .extension query :: query) [])
    (ExtensionShapeMachine.decodeAccepts .extension query) query (by simp [frontTapes, gateTape])
  have final : Function.update
      (frontTapes witness [] (ExtensionShapeMachine.decodeAccepts .extension query :: query) [])
      (gateTape .query) query = frontTapes witness [] query [] := by
    funext k
    by_cases same : k = 3 <;> simp [frontTapes, gateTape, same]
  exact oneStep (by simpa only [afterGate, final] using step)

def witnessShapeInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry .witness)) (frontTapes witness [] query []))
      (some (cfg (some (.gate .witness))
        (frontTapes [] [] query
          (ExtensionShapeMachine.decodeAccepts .assignments witness :: witness))))
      (2 * witness.length + 3) := by
  let base := frontTapes witness [] query []
  let output := ExtensionShapeMachine.decodeAccepts .assignments witness :: witness
  have call := callInTime .witness base
    (initList (ExtensionShapeMachine.machine .assignments) witness)
    (haltList (ExtensionShapeMachine.machine .assignments) output) (2 * witness.length + 3)
    (ExtensionShapeMachine.outputsInTime .assignments witness) rfl rfl rfl rfl
    (by
      intro k
      fin_cases k <;> simp [base, frontTapes, slot, initList, ExtensionShapeMachine.machine])
  have final : put .witness (haltList (ExtensionShapeMachine.machine .assignments) output).stk base =
      frontTapes [] [] query output := by
    funext k
    fin_cases k <;>
      simp [put, ExtensionMachinePlacement.tapes, view, base, frontTapes,
        haltList, ExtensionShapeMachine.machine]
  simpa only [base, final, afterHelper, output] using call

def witnessGateInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.gate .witness))
        (frontTapes [] [] query
          (ExtensionShapeMachine.decodeAccepts .assignments witness :: witness)))
      (some (cfg
        (if ExtensionShapeMachine.decodeAccepts .assignments witness then
          some (entry .fields) else cleanupEntry false)
        (fieldInput query witness))) 1 := by
  have step := gateStep .witness
    (frontTapes [] [] query (ExtensionShapeMachine.decodeAccepts .assignments witness :: witness))
    (ExtensionShapeMachine.decodeAccepts .assignments witness) witness
    (by simp [frontTapes, gateTape])
  have final : Function.update
      (frontTapes [] [] query (ExtensionShapeMachine.decodeAccepts .assignments witness :: witness))
      (gateTape .witness) witness = fieldInput query witness := by
    rw [← frontTapes_fieldInput]
    funext k
    by_cases same : k = 4 <;> simp [frontTapes, gateTape, same, -frontTapes_fieldInput]
  exact oneStep (by simpa only [afterGate, final] using step)

def frontendInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (CookLevin.pairBits (query, witness)))
      (some (cfg (frontendExit query witness) (frontendTapes query witness)))
      (16 * ((CookLevin.pairBits (query, witness)).length + 1)) := by
  have first := join (join (pairedInputInTime query witness) (queryShapeInTime query witness))
    (queryGateInTime query witness)
  cases queryFlag : (BinaryEncoding.decodeExtension query).isSome with
  | false =>
      have stopped : StateTransition.EvalsToInTime machine.step
          (initList machine (CookLevin.pairBits (query, witness)))
          (some (cfg (frontendExit query witness) (frontendTapes query witness)))
          ((3 * query.length + 4) + (2 * query.length + 3) + 1) := by
        simpa [ExtensionShapeMachine.decodeAccepts, queryFlag, frontendExit,
          frontendAccepted, frontendTapes] using first
      exact enlarge stopped (by rw [CookLevin.pairBits_length]; dsimp only; omega)
  | true =>
      have continued : StateTransition.EvalsToInTime machine.step
          (initList machine (CookLevin.pairBits (query, witness)))
          (some (cfg (some (entry .witness)) (frontTapes witness [] query [])))
          ((3 * query.length + 4) + (2 * query.length + 3) + 1) := by
        simpa [ExtensionShapeMachine.decodeAccepts, queryFlag] using first
      have all := join (join continued (witnessShapeInTime query witness))
        (witnessGateInTime query witness)
      have completed : StateTransition.EvalsToInTime machine.step
          (initList machine (CookLevin.pairBits (query, witness)))
          (some (cfg (frontendExit query witness) (frontendTapes query witness)))
          ((((3 * query.length + 4) + (2 * query.length + 3) + 1) +
            (2 * witness.length + 3)) + 1) := by
        simpa [ExtensionShapeMachine.decodeAccepts, queryFlag, frontendExit,
          frontendAccepted, frontendTapes] using! all
      exact enlarge completed (by rw [CookLevin.pairBits_length]; dsimp only; omega)

def extractedTapes (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) (BinaryEncoding.natBits bins)
    (BinaryEncoding.rawInstanceBits items) (ExtensionAgreementMachine.fixedBits fixed) [] [] []

def validationInput (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) (BinaryEncoding.natBits bins)
    (BinaryEncoding.rawInstanceBits items) (ExtensionAgreementMachine.fixedBits fixed) []
    (BinaryEncoding.rawInstanceBits items) (BinaryEncoding.assignmentBits assignments)

def checkedTapes (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) []
    (BinaryEncoding.rawInstanceBits items) (ExtensionAgreementMachine.fixedBits fixed) bins.bits [] []

def agreementInput (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) []
    (BinaryEncoding.rawInstanceBits items) (ExtensionAgreementMachine.fixedBits fixed) bins.bits []
    (BinaryEncoding.assignmentBits assignments)

def capacityInput (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) []
    (BinaryEncoding.rawInstanceBits items) [] bins.bits [] []

def extractionInTime (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry .fields)) (fieldInput (BinaryEncoding.extensionBits bins items fixed)
        (BinaryEncoding.assignmentBits assignments)))
      (some (cfg (some (.copyOut .items)) (extractedTapes bins items fixed assignments)))
      (2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) := by
  have lifted := callInTime .fields
    (fieldInput (BinaryEncoding.extensionBits bins items fixed)
      (BinaryEncoding.assignmentBits assignments))
    _ _ _ (Fields.extensionInTime bins items fixed) rfl rfl rfl rfl
    (by intro k; fin_cases k <;> rfl)
  have words : put .fields (Fields.tapes [] Fields.empty (Fields.encodedWords bins items fixed))
      (fieldInput (BinaryEncoding.extensionBits bins items fixed)
        (BinaryEncoding.assignmentBits assignments)) = extractedTapes bins items fixed assignments := by
    funext k
    fin_cases k <;> simp [put, ExtensionMachinePlacement.tapes, view, Fields.tapes,
      Fields.empty, Fields.encodedWords, fieldInput, extractedTapes, stagedTapes,
      ExtensionAgreementMachine.fixedBits]
  simpa only [Fields.cfg, words, afterHelper] using lifted

def prepareValidationInTime (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.copyOut .items)) (extractedTapes bins items fixed assignments))
      (some (cfg (some (entry .validation)) (validationInput bins items fixed assignments)))
      (2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
        2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
  have first := copyInTime .items (extractedTapes bins items fixed assignments) rfl
  have second := copyInTime .validationAssignments
    (Function.update (extractedTapes bins items fixed assignments) 12
      (BinaryEncoding.rawInstanceBits items)) (by simp [extractedTapes, stagedTapes])
  have output : Function.update (Function.update (extractedTapes bins items fixed assignments)
      12 (BinaryEncoding.rawInstanceBits items)) 13 (BinaryEncoding.assignmentBits assignments) =
      validationInput bins items fixed assignments := by
    funext k
    fin_cases k <;> simp [extractedTapes, validationInput, stagedTapes]
  have firstSource : extractedTapes bins items fixed assignments 9 =
      BinaryEncoding.rawInstanceBits items := rfl
  have firstEmpty : extractedTapes bins items fixed assignments 12 = [] := rfl
  have secondSource :
      Function.update (extractedTapes bins items fixed assignments) 12
        (BinaryEncoding.rawInstanceBits items) 4 = BinaryEncoding.assignmentBits assignments := rfl
  have secondEmpty :
      Function.update (extractedTapes bins items fixed assignments) 12
        (BinaryEncoding.rawInstanceBits items) 13 = [] := rfl
  simp only [copySource, copyDestination, afterCopy, firstSource, firstEmpty,
    List.append_nil] at first
  simp only [copySource, copyDestination, afterCopy, secondSource, secondEmpty,
    List.append_nil] at second
  have joined := join first second
  rw [output] at joined
  exact joined

def prepareAgreementInTime (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.copyOut .agreementAssignments)) (checkedTapes bins items fixed assignments))
      (some (cfg (some (entry .agreement)) (agreementInput bins items fixed assignments)))
      (2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
  have copied := copyInTime .agreementAssignments (checkedTapes bins items fixed assignments) rfl
  have output : Function.update (checkedTapes bins items fixed assignments) 13
      (BinaryEncoding.assignmentBits assignments) = agreementInput bins items fixed assignments := by
    funext k
    fin_cases k <;> simp [checkedTapes, agreementInput, stagedTapes]
  have source : checkedTapes bins items fixed assignments 4 =
      BinaryEncoding.assignmentBits assignments := rfl
  have empty : checkedTapes bins items fixed assignments 13 = [] := rfl
  simp only [copySource, copyDestination, afterCopy, source, empty, List.append_nil] at copied
  rw [output] at copied
  exact copied

theorem check_factor (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    ExtensionCertificate.check bins items fixed assignments =
      (ExtensionValidationMachine.validRows bins items assignments &&
        (ExtensionCertificate.agreesBool fixed assignments &&
          assignments.all (ExtensionCertificate.capacityCheck items assignments))) := by
  simp only [ExtensionCertificate.check, ExtensionValidationMachine.validRows_eq, Bool.and_assoc]

noncomputable def canonicalBudget (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Nat :=
  (2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) +
  (2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
    2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) +
  ExtensionValidationMachine.validationTime.eval
    (ExtensionValidationMachine.inputLength bins items assignments) + 1 +
  2 * ((BinaryEncoding.assignmentBits assignments).length + 1) +
  (ExtensionAgreementMachine.agreementTime.eval
    ((ExtensionAgreementMachine.fixedBits fixed).length +
      (BinaryEncoding.assignmentBits assignments).length) + 1) + 1 +
  ExtensionCapacityOuterMachine.timePolynomial.eval
    (ExtensionCapacityOuterMachine.inputLength items assignments) + 1

structure CanonicalRun (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) where
  finish : Tape → List Bool
  execution : StateTransition.EvalsToInTime machine.step
    (cfg (some (entry .fields)) (fieldInput (BinaryEncoding.extensionBits bins items fixed)
      (BinaryEncoding.assignmentBits assignments)))
    (some (cfg (cleanupEntry (ExtensionCertificate.check bins items fixed assignments)) finish))
    (canonicalBudget bins items fixed assignments)

noncomputable def canonicalRun (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : CanonicalRun bins items fixed assignments := by
  let validated := ExtensionValidationMachine.validationInTime bins items assignments
  have extracted := extractionInTime bins items fixed assignments
  have copied := prepareValidationInTime bins items fixed assignments
  have validation := callInTime .validation (validationInput bins items fixed assignments)
    _ _ _ validated.execution rfl rfl rfl rfl
    (by intro k; fin_cases k <;>
        simp [validationInput, stagedTapes, slot, ExtensionValidationMachine.cfg,
          ExtensionValidationMachine.inputTapes, ExtensionValidationMachine.work])
  let afterValidation := put .validation validated.finish (validationInput bins items fixed assignments)
  have validationFlag : afterValidation 8 = [ExtensionValidationMachine.validRows bins items assignments] := by
    change put .validation validated.finish (validationInput bins items fixed assignments)
      (slot .validation 0) = _
    simpa only [put_slot] using validated.flag
  have validateGate := oneStep (gateStep .validation afterValidation
    (ExtensionValidationMachine.validRows bins items assignments) [] validationFlag)
  have checkedPrefix := join (join (join extracted copied) validation) validateGate
  by_cases valid : ExtensionValidationMachine.validRows bins items assignments = true
  · have validity : items.Valid := by
      have h := valid
      rw [ExtensionValidationMachine.validRows_eq, Bool.and_eq_true] at h
      exact (ExtensionCertificate.validItems_eq_true_iff items).mp h.1
    have sameLength : assignments.length = items.length := by
      have h := valid
      simp only [ExtensionValidationMachine.validRows_eq, Bool.and_eq_true,
        decide_eq_true_eq] at h
      exact h.2.1
    have validatedWords : Function.update afterValidation 8 [] =
        checkedTapes bins items fixed assignments := by
      rw [show afterValidation = put .validation
        (Function.update (ExtensionValidationMachine.work bins.bits [] [] [] [] []) 0 [true])
        (validationInput bins items fixed assignments) from congrArg
          (fun v => put .validation v (validationInput bins items fixed assignments))
          (validated.accepted_clean valid)]
      funext k
      fin_cases k <;>
        simp [put, ExtensionMachinePlacement.tapes, view, validationInput, stagedTapes,
          checkedTapes, ExtensionValidationMachine.work]
    simp only [valid, ↓reduceIte,
      afterGate, gateTape, validatedWords] at checkedPrefix
    have copiedAgain := prepareAgreementInTime bins items fixed assignments
    have agreement := callInTime .agreement (agreementInput bins items fixed assignments)
      _ _ _ (ExtensionAgreementMachine.agreementFlagInTime fixed assignments) rfl rfl rfl rfl
      (by intro k; fin_cases k <;>
          simp [agreementInput, stagedTapes, slot, ExtensionAgreementMachine.cfg,
            ExtensionAgreementMachine.tapes])
    let agreementResult := ExtensionCertificate.agreesBool fixed assignments
    let afterAgreement := put .agreement (ExtensionAgreementMachine.tapes [agreementResult] [])
      (agreementInput bins items fixed assignments)
    have agreementFlag : afterAgreement 10 = [agreementResult] := by
      change put .agreement _ _ (slot .agreement 0) = _
      simp [put_slot, ExtensionAgreementMachine.tapes]
    have agreeGate := oneStep (gateStep .agreement afterAgreement agreementResult [] agreementFlag)
    have throughAgreement := join (join (join checkedPrefix copiedAgain) agreement) agreeGate
    by_cases agrees : agreementResult = true
    · have agreedWords : Function.update afterAgreement 10 [] =
          capacityInput bins items assignments := by
        funext k
        fin_cases k <;>
          simp [afterAgreement, put, ExtensionMachinePlacement.tapes, view,
            ExtensionAgreementMachine.tapes, agreementInput, stagedTapes, capacityInput]
      simp only [agrees, ↓reduceIte,
        afterGate, gateTape, agreedWords] at throughAgreement
      have capacity := callInTime .capacity (capacityInput bins items assignments) _ _ _
        (ExtensionCapacityOuterMachine.outerInPolynomialTime items assignments validity sameLength)
        rfl rfl rfl rfl
        (by intro k; fin_cases k <;>
            simp [slot, capacityInput, stagedTapes, ExtensionCapacityOuterMachine.initialCfg,
              ExtensionCapacityOuterMachine.configuration, ExtensionCapacityOuterMachine.initialTapes,
              ExtensionCapacityOuterMachine.stageTapes])
      let result := assignments.all (ExtensionCertificate.capacityCheck items assignments)
      let afterCapacity := put .capacity (ExtensionCapacityOuterMachine.resultTapes result)
        (capacityInput bins items assignments)
      have capacityFlag : afterCapacity 15 = [result] := by
        change put .capacity _ _ (slot .capacity 0) = _
        simp [put_slot, ExtensionCapacityOuterMachine.resultTapes]
      have capacityGate := oneStep (gateStep .capacity afterCapacity result [] capacityFlag)
      have finish := join (join throughAgreement capacity) capacityGate
      refine ⟨Function.update afterCapacity 15 [], ?_⟩
      have semantics : ExtensionCertificate.check bins items fixed assignments = result := by
        simp only [check_factor, valid, Bool.true_and, ← show
          agreementResult = ExtensionCertificate.agreesBool fixed assignments from rfl, agrees,
          Bool.true_and, result]
      have exit : (if result then afterGate .capacity else cleanupEntry false) = cleanupEntry result := by
        cases result <;> rfl
      simpa only [canonicalBudget, ExtensionCapacityOuterMachine.finalCfg,
        ExtensionCapacityOuterMachine.configuration, afterHelper, gateTape, exit, semantics,
        afterCapacity, afterAgreement, agreementResult, result] using finish
    · have rejected : agreementResult = false := Bool.eq_false_of_not_eq_true agrees
      refine ⟨Function.update afterAgreement 10 [], ?_⟩
      have semantics : ExtensionCertificate.check bins items fixed assignments = false := by
        simp only [check_factor, valid, Bool.true_and, ← show
          agreementResult = ExtensionCertificate.agreesBool fixed assignments from rfl,
          rejected, Bool.false_and]
      have bounded :
          (((((2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) +
            (2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
              2 * ((BinaryEncoding.assignmentBits assignments).length + 1))) +
            ExtensionValidationMachine.validationTime.eval
              (ExtensionValidationMachine.inputLength bins items assignments)) + 1) +
            2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) +
            (ExtensionAgreementMachine.agreementTime.eval
              ((ExtensionAgreementMachine.fixedBits fixed).length +
                (BinaryEncoding.assignmentBits assignments).length) + 1) + 1 ≤
          canonicalBudget bins items fixed assignments := by
        unfold canonicalBudget
        omega
      simpa only [rejected, Bool.cond_false, Bool.false_eq_true, ↓reduceIte,
        gateTape, semantics, afterHelper,
        afterAgreement, agreementResult] using enlarge throughAgreement bounded
  · have rejected : ExtensionValidationMachine.validRows bins items assignments = false :=
      Bool.eq_false_of_not_eq_true valid
    refine ⟨Function.update afterValidation 8 [], ?_⟩
    have semantics : ExtensionCertificate.check bins items fixed assignments = false := by
      simp only [check_factor, rejected, Bool.false_and]
    have bounded :
        (((2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) +
          (2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
            2 * ((BinaryEncoding.assignmentBits assignments).length + 1))) +
          ExtensionValidationMachine.validationTime.eval
            (ExtensionValidationMachine.inputLength bins items assignments)) + 1 ≤
        canonicalBudget bins items fixed assignments := by
      unfold canonicalBudget
      omega
    simpa only [rejected, Bool.cond_false, Bool.false_eq_true, ↓reduceIte,
      gateTape, semantics, afterHelper, afterValidation]
      using enlarge checkedPrefix bounded

noncomputable def canonicalTime : Polynomial Nat :=
  ExtensionCapacityOuterMachine.timePolynomial + ExtensionValidationMachine.validationTime +
    Polynomial.C 10 * Polynomial.X + Polynomial.C 20

theorem canonicalBudget_le (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    canonicalBudget bins items fixed assignments ≤ canonicalTime.eval
      ((BinaryEncoding.extensionBits bins items fixed).length +
        (BinaryEncoding.assignmentBits assignments).length) := by
  let n := (BinaryEncoding.extensionBits bins items fixed).length +
    (BinaryEncoding.assignmentBits assignments).length
  have queryLength : (BinaryEncoding.extensionBits bins items fixed).length =
      (BinaryEncoding.natBits bins).length + (BinaryEncoding.rawInstanceBits items).length +
        (ExtensionAgreementMachine.fixedBits fixed).length := by
    simp [BinaryEncoding.extensionBits, ExtensionAgreementMachine.fixedBits, Nat.add_assoc]
  have validationBound : ExtensionValidationMachine.inputLength bins items assignments ≤ n := by
    simp only [ExtensionValidationMachine.inputLength, n, queryLength]
    omega
  have capacityBound : ExtensionCapacityOuterMachine.inputLength items assignments ≤ n := by
    simp only [ExtensionCapacityOuterMachine.inputLength, n, queryLength]
    omega
  have validationClock := MachineComposition.natPolynomial_eval_mono
    ExtensionValidationMachine.validationTime validationBound
  have capacityClock := MachineComposition.natPolynomial_eval_mono
    ExtensionCapacityOuterMachine.timePolynomial capacityBound
  simp only [canonicalBudget, canonicalTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, ExtensionAgreementMachine.agreementTime,
    Polynomial.eval_ofNat]
  dsimp [n] at validationClock capacityClock
  omega

noncomputable def canonicalInPolynomialTime (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry .fields)) (fieldInput (BinaryEncoding.extensionBits bins items fixed)
        (BinaryEncoding.assignmentBits assignments)))
      (some (cfg (cleanupEntry (ExtensionCertificate.check bins items fixed assignments))
        (canonicalRun bins items fixed assignments).finish))
      (canonicalTime.eval ((BinaryEncoding.extensionBits bins items fixed).length +
        (BinaryEncoding.assignmentBits assignments).length)) :=
  enlarge (canonicalRun bins items fixed assignments).execution
    (canonicalBudget_le bins items fixed assignments)

noncomputable def decisionTime : Polynomial Nat :=
  Polynomial.C 16 * (Polynomial.X + Polynomial.C 1) + canonicalTime

structure DecisionRun (query witness : List Bool) where
  finish : Tape → List Bool
  execution : StateTransition.EvalsToInTime machine.step
    (initList machine (CookLevin.pairBits (query, witness)))
    (some (cfg (cleanupEntry (ExtensionCertificate.verify (query, witness))) finish))
    (decisionTime.eval (CookLevin.pairBits (query, witness)).length)

noncomputable def decisionRun (query witness : List Bool) : DecisionRun query witness := by
  have frontend := frontendInTime query witness
  have frontendBound : 16 * ((CookLevin.pairBits (query, witness)).length + 1) ≤
      decisionTime.eval (CookLevin.pairBits (query, witness)).length := by
    simp only [decisionTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  cases queryDecoded : BinaryEncoding.decodeExtension query with
  | none =>
      refine ⟨frontendTapes query witness, ?_⟩
      simpa [frontendExit, frontendAccepted, queryDecoded, ExtensionCertificate.verify] using
        enlarge frontend frontendBound
  | some data =>
      rcases data with ⟨bins, items, fixed⟩
      cases witnessDecoded : BinaryEncoding.decodeAssignments witness with
      | none =>
          refine ⟨frontendTapes query witness, ?_⟩
          simpa [frontendExit, frontendAccepted, queryDecoded, witnessDecoded,
            ExtensionCertificate.verify] using enlarge frontend frontendBound
      | some assignments =>
          have queryEncoding := BinaryEncoding.decodeExtension_sound queryDecoded
          have witnessEncoding := BinaryEncoding.decodeAssignments_sound witnessDecoded
          have canonical := canonicalInPolynomialTime bins items fixed assignments
          rw [← queryEncoding, ← witnessEncoding] at canonical
          have parsedPrefix : StateTransition.EvalsToInTime machine.step
              (initList machine (CookLevin.pairBits (query, witness)))
              (some (cfg (some (entry .fields)) (fieldInput query witness)))
              (16 * ((CookLevin.pairBits (query, witness)).length + 1)) := by
            simpa [frontendExit, frontendAccepted, frontendTapes, queryDecoded, witnessDecoded]
              using frontend
          have complete := join parsedPrefix canonical
          refine ⟨(canonicalRun bins items fixed assignments).finish, ?_⟩
          have lengthBound : query.length + witness.length ≤
              (CookLevin.pairBits (query, witness)).length := by
            rw [CookLevin.pairBits_length]
            dsimp only
            omega
          have canonicalBound := MachineComposition.natPolynomial_eval_mono canonicalTime lengthBound
          have budget : 16 * ((CookLevin.pairBits (query, witness)).length + 1) +
              canonicalTime.eval (query.length + witness.length) ≤
              decisionTime.eval (CookLevin.pairBits (query, witness)).length := by
            simp only [decisionTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X]
            omega
          simpa only [ExtensionCertificate.verify, queryDecoded, witnessDecoded] using
            enlarge complete budget

theorem initialConfiguration (input : List Bool) :
    initList machine input = cfg (some (entry .pair)) (Function.update (fun _ => []) 0 input) := by
  unfold initList cfg machine
  congr 1
  funext k
  fin_cases k <;> rfl

theorem finalConfiguration (result : Bool) :
    cfg none (resultTapes result) = haltList machine [result] := by
  unfold haltList cfg resultTapes
  congr 1
  funext k
  fin_cases k <;> rfl

theorem initial_mass (input : List Bool) :
    MachineDrainMany.lengthSum allTapes (initList machine input).stk = input.length := by
  rw [initialConfiguration]
  simp [MachineDrainMany.lengthSum, allTapes, List.ofFn_succ, cfg]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C (40 * Runtime.programPushBound machine + 1) * decisionTime +
    Polynomial.X + Polynomial.C 41

noncomputable def outputsInTime (query witness : List Bool) :
    TM2OutputsInTime machine (CookLevin.pairBits (query, witness))
      (some [ExtensionCertificate.verify (query, witness)])
      (timePolynomial.eval (CookLevin.pairBits (query, witness)).length) := by
  let run := decisionRun query witness
  have cleanup := cleanupInTime (ExtensionCertificate.verify (query, witness)) run.finish
  have complete := join run.execution cleanup
  have space := ExtensionMachineSpace.execution_lengthSum machine allTapes run.execution
  change MachineDrainMany.lengthSum allTapes run.finish ≤
    MachineDrainMany.lengthSum allTapes
      (initList machine (CookLevin.pairBits (query, witness))).stk +
      allTapes.length * (decisionTime.eval (CookLevin.pairBits (query, witness)).length *
        Runtime.programPushBound machine) at space
  rw [initial_mass] at space
  simp only [allTapes, List.length_ofFn] at space
  have budget :
      decisionTime.eval (CookLevin.pairBits (query, witness)).length +
        (MachineDrainMany.lengthSum allTapes run.finish + 41) ≤
      timePolynomial.eval (CookLevin.pairBits (query, witness)).length := by
    calc
      _ ≤ decisionTime.eval (CookLevin.pairBits (query, witness)).length +
          ((CookLevin.pairBits (query, witness)).length +
            40 * (decisionTime.eval (CookLevin.pairBits (query, witness)).length *
              Runtime.programPushBound machine) + 41) := Nat.add_le_add_left
                (Nat.add_le_add_right space 41) _
      _ = _ := by
        simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X]
        ring
  change StateTransition.EvalsToInTime machine.step
    (initList machine (CookLevin.pairBits (query, witness)))
    (some (haltList machine [ExtensionCertificate.verify (query, witness)]))
    (timePolynomial.eval (CookLevin.pairBits (query, witness)).length)
  simpa only [finalConfiguration] using enlarge complete budget

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CookLevin.pairBits (fun bit : Bool => [bit])
      ExtensionCertificate.verify where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun pair := by
    rcases pair with ⟨query, witness⟩
    change TM2OutputsInTime machine ((CookLevin.pairBits (query, witness)).map id)
      (some ([ExtensionCertificate.verify (query, witness)].map id))
      (timePolynomial.eval (CookLevin.pairBits (query, witness)).length)
    have input_eq : @List.map (machine.Γ machine.k₀) (machine.Γ machine.k₀) id
        (CookLevin.pairBits (query, witness)) = CookLevin.pairBits (query, witness) := List.map_id _
    simpa only [input_eq, List.map_cons, List.map_nil, id_eq] using! outputsInTime query witness

theorem computation_finiteAlphabet (k : computableInPolyTime.tm.K) :
    Finite (computableInPolyTime.tm.Γ k) := by
  change Finite Bool
  infer_instance

end BinPackingGap.ExtensionVerifierMachine

namespace BinPackingGap

open BinPackingGames.Foundations.Complexity

noncomputable def packingExtensionVerifier : CookLevin.NPVerifier where
  witnessBound := ExtensionWitness.witnessPolynomial
  verify := ExtensionCertificate.verify
  computation := ExtensionVerifierMachine.computableInPolyTime
  finiteAlphabet _ := inferInstanceAs (Fintype Bool)

theorem packingExtensionVerifier_accepts (input : List Bool) :
    packingExtensionVerifier.Accepts input ↔ ExtensionCertificate.language input := by
  simpa only [CookLevin.NPVerifier.Accepts, packingExtensionVerifier,
    ExtensionWitness.witnessPolynomial_eval] using
      (ExtensionWitness.language_iff_bounded_witness input).symm

theorem packingExtension_inNP : CookLevin.InNP ExtensionCertificate.language := by
  refine ⟨packingExtensionVerifier, ?_⟩
  intro input
  exact (packingExtensionVerifier_accepts input).symm

theorem packingExtension_allNone (bins : Nat) (items : RawInstance) (valid : items.Valid) :
    ExtensionCertificate.language
        (BinaryEncoding.extensionBits bins items (List.replicate items.length none)) ↔
      HasPacking (items.toInstance valid) bins := by
  rw [ExtensionCertificate.language_extensionBits]
  exact ExtensionQuery.ext_none_iff_hasPacking bins items valid

end BinPackingGap

end OAI
