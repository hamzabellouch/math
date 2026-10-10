import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Arithmetic.BinaryPowerMachine
import OAI.Computability.BinPacking.Packing.CapacityScan
import OAI.Computability.BinPacking.Search.SearchInitialItemsMachine

namespace OAI

namespace BinPackingGap.ExtensionWitness

open BinaryEncoding

def bound (inputLength : Nat) : Nat := 4 * (inputLength + 1) ^ 2

noncomputable def witnessPolynomial : Polynomial Nat :=
  Polynomial.C 4 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp] theorem witnessPolynomial_eval (inputLength : Nat) :
    witnessPolynomial.eval inputLength = bound inputLength := by
  simp [witnessPolynomial, bound]

theorem bins_size_le_input (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    bins.size ≤ (extensionBits bins items fixed).length := by
  simp only [extensionBits, List.length_append, natBits_length]
  omega

theorem items_length_le_input (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    items.length ≤ (extensionBits bins items fixed).length := by
  have counted := list_length_le_bits_length (pairBits natBits natBits) items
  change items.length ≤ (rawInstanceBits items).length at counted
  simp only [extensionBits, List.length_append]
  omega

theorem denominatorBits_le_rawInstanceBits (items : RawInstance) :
    FractionWidth.denominatorBits items ≤ (rawInstanceBits items).length := by
  induction items with
  | nil => simp [FractionWidth.denominatorBits, rawInstanceBits_length]
  | cons q items ih =>
      simp only [FractionWidth.denominatorBits, rawInstanceBits_length,
        List.map_cons, List.sum_cons] at *
      omega

theorem denominatorBits_le_input (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    FractionWidth.denominatorBits items ≤ (extensionBits bins items fixed).length := by
  have recorded := denominatorBits_le_rawInstanceBits items
  simp only [extensionBits, List.length_append]
  omega

theorem denominatorBits_append (before after : RawInstance) :
    FractionWidth.denominatorBits (before ++ after) =
      FractionWidth.denominatorBits before + FractionWidth.denominatorBits after := by
  simp [FractionWidth.denominatorBits, List.map_append, List.sum_append]

theorem assignmentBits_length_le (bins : Nat) (assignments : List Nat)
    (range : ∀ label ∈ assignments, label < bins) :
    (assignmentBits assignments).length ≤ 1 + assignments.length * (2 * bins.size + 2) := by
  induction assignments with
  | nil => simp [assignmentBits, listBits]
  | cons label assignments ih =>
      have head : label.size ≤ bins.size :=
        FractionWidth.size_mono (Nat.le_of_lt (range label (List.mem_cons_self ..)))
      have tail : ∀ value ∈ assignments, value < bins :=
        fun value mem => range value (List.mem_cons_of_mem label mem)
      have rest := ih tail
      have length_eq : (assignmentBits (label :: assignments)).length =
          2 * label.size + 2 + (assignmentBits assignments).length := by
        simp [assignmentBits, listBits]
        omega
      rw [length_eq, List.length_cons]
      nlinarith

theorem assignmentBits_length_le_bound (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat)
    (feasible : (RawPacking.mk bins assignments).Feasible items) :
    (assignmentBits assignments).length ≤ bound (extensionBits bins items fixed).length := by
  have length_bound := assignmentBits_length_le bins assignments feasible.2.1
  rw [feasible.1] at length_bound
  have item_bound := items_length_le_input bins items fixed
  have header_bound := bins_size_le_input bins items fixed
  have product_bound : items.length * (2 * bins.size + 2) ≤
      (extensionBits bins items fixed).length *
        (2 * (extensionBits bins items fixed).length + 2) :=
    Nat.mul_le_mul item_bound (by omega)
  unfold bound
  nlinarith

theorem load_den_width_le_input (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat) (label : Nat) :
    (RawPacking.loadFraction items assignments label).2.size ≤
      (extensionBits bins items fixed).length + 1 := by
  have fold_bound := FractionWidth.loadFraction_den_size_le items assignments label
  have input_bound := denominatorBits_le_input bins items fixed
  omega

theorem load_num_width_le_input (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat) (label : Nat)
    (accepted : (RawPacking.loadFraction items assignments label).1 ≤
      (RawPacking.loadFraction items assignments label).2) :
    (RawPacking.loadFraction items assignments label).1.size ≤
      (extensionBits bins items fixed).length + 1 := by
  exact (FractionWidth.size_mono accepted).trans
    (load_den_width_le_input bins items fixed assignments label)

theorem scan_operands_width_le_input (bins : Nat) (before after : RawInstance)
    (item : Nat × Nat) (fixed : List (Option Nat))
    (assignments : List Nat) (label : Nat)
    (valid : (before ++ item :: after).Valid)
    (accepted : (RawPacking.loadFraction before assignments label).1 ≤
      (RawPacking.loadFraction before assignments label).2) :
    let total := RawPacking.loadFraction before assignments label
    let inputLength := (extensionBits bins (before ++ item :: after) fixed).length
    total.1.size + total.2.size + item.1.size + item.2.size ≤
      4 * (inputLength + 1) := by
  have member : item ∈ before ++ item :: after := by simp
  have item_width := FractionWidth.size_mono (valid item member).2
  have numerator_width := FractionWidth.size_mono accepted
  have denominator_width := FractionWidth.loadFraction_den_size_le before assignments label
  have input_width := denominatorBits_le_input bins (before ++ item :: after) fixed
  rw [denominatorBits_append, FractionWidth.denominatorBits_cons] at input_width
  dsimp only
  omega

theorem scan_step_width_le_input (bins : Nat) (before after : RawInstance)
    (item : Nat × Nat) (fixed : List (Option Nat))
    (assignments : List Nat) (label : Nat)
    (valid : (before ++ item :: after).Valid)
    (accepted : (RawPacking.loadFraction before assignments label).1 ≤
      (RawPacking.loadFraction before assignments label).2) :
    let total := RawPacking.loadFraction before assignments label
    let inputLength := (extensionBits bins (before ++ item :: after) fixed).length
    (RawPacking.addFraction total item).2.size ≤ inputLength + 1 ∧
    (total.1 * item.2).size ≤ inputLength + 1 ∧
    (item.1 * total.2).size ≤ inputLength + 1 ∧
    (RawPacking.addFraction total item).1.size ≤ inputLength + 2 := by
  have member : item ∈ before ++ item :: after := by simp
  have size_valid : item.1 ≤ item.2 := (valid item member).2
  have step_width := FractionWidth.loadFraction_next_width
    before assignments label item accepted size_valid
  have input_width := denominatorBits_le_input bins (before ++ item :: after) fixed
  rw [denominatorBits_append, FractionWidth.denominatorBits_cons] at input_width
  dsimp only
  omega

theorem exists_bounded_witness (input : List Bool)
    (member : ExtensionCertificate.language input) :
    ∃ witness : List Bool, witness.length ≤ bound input.length ∧
      ExtensionCertificate.verify (input, witness) = true := by
  cases parsed : decodeExtension input with
  | none => simp [ExtensionCertificate.language, parsed] at member
  | some query =>
      rcases query with ⟨bins, items, fixed⟩
      have extension : ExtensionQuery.Ext bins items fixed := by
        simpa [ExtensionCertificate.language, parsed] using member
      obtain ⟨valid, assignments, feasible, agrees⟩ := extension
      refine ⟨assignmentBits assignments, ?_, ?_⟩
      · have represented : input = extensionBits bins items fixed :=
          decodeExtension_sound parsed
        rw [represented]
        exact assignmentBits_length_le_bound bins items fixed assignments feasible
      · have checked :=
          (ExtensionCertificate.check_eq_true_iff bins items fixed assignments).mpr
            ⟨valid, feasible, agrees⟩
        simpa [ExtensionCertificate.verify, parsed] using checked

theorem language_iff_bounded_witness (input : List Bool) :
    ExtensionCertificate.language input ↔
      ∃ witness : List Bool, witness.length ≤ bound input.length ∧
        ExtensionCertificate.verify (input, witness) = true := by
  constructor
  · exact exists_bounded_witness input
  · rintro ⟨witness, _, accepted⟩
    exact ExtensionCertificate.verify_sound input witness accepted

end BinPackingGap.ExtensionWitness

namespace BinPackingGap.ExtensionFractionMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

inductive Product
  | leftNumerator | rightNumerator | denominator
  deriving DecidableEq

protected abbrev Product.enumList : List Product := [.leftNumerator, .rightNumerator,
  .denominator]

protected theorem Product.enumList_getElem?_ctorIdx_eq (x : Product) :
    Product.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Product.enumList_nodup : Product.enumList.Nodup := by decide

instance : Fintype Product where
  elems := ⟨Product.enumList, Product.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | multiply (product : Product) (localLabel : BinaryMulMachine.Label)
  | add
  | restore
  deriving DecidableEq, Fintype

abbrev State (A : Type) := BinaryAddMachine.State A
abbrev Alphabet {K : Type} (_ : K) := Bool

abbrev Tape := Fin 15

def productTapes : Product → (Fin 9 ↪ Tape)
  | .leftNumerator =>
      ⟨![0, 3, 6, 9, 10, 11, 12, 13, 14], by decide⟩
  | .rightNumerator =>
      ⟨![2, 1, 7, 9, 10, 11, 12, 13, 14], by decide⟩
  | .denominator =>
      ⟨![1, 3, 5, 9, 10, 11, 12, 13, 14], by decide⟩

def productExit {Λ : Type} (labels : Label → Λ) : Product → Option Λ
  | .leftNumerator => some (labels (.multiply .rightNumerator .copyLeft))
  | .rightNumerator => some (labels (.multiply .denominator .copyLeft))
  | .denominator => some (labels .add)

variable {K Λ A : Type} [DecidableEq K]

def statement (slots : Tape ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .multiply product localLabel =>
      BinaryMulMachine.statement ((productTapes product).trans slots)
        (fun localLabel => labels (.multiply product localLabel))
        (productExit labels product) localLabel
  | .add =>
      BinaryAddMachine.addLoop (slots 6) (slots 7) (slots 8)
        (labels .add) (some (labels .restore))
  | .restore =>
      MachineTransfer.loopAt (slots 8) (slots 4) id false (labels .restore) exit

def program : Label → TM2.Stmt (Alphabet (K := Tape)) Label (State Unit) :=
  statement (Function.Embedding.refl Tape) id none

def machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label
  main := .multiply .leftNumerator .copyLeft
  σ := State Unit
  initialState := BinaryAddMachine.clean ()
  m := program

def leftProduct (numerator itemDenominator : List Bool) : List Bool :=
  BinaryArithmetic.mulAcc numerator itemDenominator []

def rightProduct (itemNumerator denominator : List Bool) : List Bool :=
  BinaryArithmetic.mulAcc itemNumerator denominator []

def nextNumerator (numerator denominator itemNumerator itemDenominator : List Bool) : List Bool :=
  BinaryArithmetic.addCarry (leftProduct numerator itemDenominator)
    (rightProduct itemNumerator denominator) false

def nextDenominator (denominator itemDenominator : List Bool) : List Bool :=
  BinaryArithmetic.mulAcc denominator itemDenominator []

def steps (numerator denominator itemNumerator itemDenominator : List Bool) : Nat :=
  BinaryMulMachine.steps numerator itemDenominator +
    BinaryMulMachine.steps itemNumerator denominator +
    BinaryMulMachine.steps denominator itemDenominator +
    (max (leftProduct numerator itemDenominator).length
      (rightProduct itemNumerator denominator).length + 1) +
    ((nextNumerator numerator denominator itemNumerator itemDenominator).length + 1)

@[simp] theorem nextNumerator_bits (A D a d : Nat) :
    nextNumerator A.bits D.bits a.bits d.bits = (A * d + a * D).bits := by
  simp [nextNumerator, leftProduct, rightProduct, BinaryArithmetic.mulAcc_bits,
    BinaryArithmetic.addCarry_bits]

@[simp] theorem nextDenominator_bits (D d : Nat) :
    nextDenominator D.bits d.bits = (D * d).bits := by
  simp [nextDenominator, BinaryArithmetic.mulAcc_bits]

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

omit [DecidableEq K] in
private theorem workspace_multiply (slots : Tape ↪ K) (base : K → List Bool)
    (workspace : ∀ i : Tape, 9 ≤ i.val → base (slots i) = [])
    (product : Product) :
    ∀ i : Fin 9, 3 ≤ i.val → base (((productTapes product).trans slots) i) = [] := by
  intro i hi
  have h9 := workspace 9 (by decide)
  have h10 := workspace 10 (by decide)
  have h11 := workspace 11 (by decide)
  have h12 := workspace 12 (by decide)
  have h13 := workspace 13 (by decide)
  have h14 := workspace 14 (by decide)
  cases product <;> fin_cases i <;> simp_all [productTapes]

private theorem workspace_update (slots : Tape ↪ K) (base : K → List Bool)
    (workspace : ∀ i : Tape, 9 ≤ i.val → base (slots i) = [])
    (j : Tape) (hj : j.val < 9) (word : List Bool) :
    ∀ i : Tape, 9 ≤ i.val → Function.update base (slots j) word (slots i) = [] := by
  intro i hi
  have distinct : i ≠ j := by intro h; subst i; omega
  simpa only [Function.update_of_ne (slots.injective.ne distinct)] using workspace i hi

def resultTapes (slots : Tape ↪ K) (base : K → List Bool) (A D a d : Nat) :
    K → List Bool :=
  Function.update (Function.update base (slots 5) (D * d).bits)
    (slots 4) (A * d + a * D).bits

noncomputable def arithmeticBudget (A D a d : Nat) : Nat :=
  BinaryMulMachine.timePolynomial.eval (A.size + d.size) +
    BinaryMulMachine.timePolynomial.eval (a.size + D.size) +
    BinaryMulMachine.timePolynomial.eval (D.size + d.size) +
    (max (A * d).size (a * D).size + 1) +
    ((A * d + a * D).size + 1)

noncomputable def arithmeticInTime (slots : Tape ↪ K) (labels : Label → Λ)
    (exit : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (num den itemNum itemDen : Nat)
    (hnum : base (slots 0) = num.bits) (hden : base (slots 1) = den.bits)
    (hitemNum : base (slots 2) = itemNum.bits) (hitemDen : base (slots 3) = itemDen.bits)
    (emptyWorkspace : ∀ i : Tape, 4 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .leftNumerator .copyLeft)), BinaryAddMachine.clean ambient, base⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        resultTapes slots base num den itemNum itemDen⟩)
      (arithmeticBudget num den itemNum itemDen) := by
  have hd (i j : Tape) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  have h4 := emptyWorkspace 4 (by decide)
  have h5 := emptyWorkspace 5 (by decide)
  have h6 := emptyWorkspace 6 (by decide)
  have h7 := emptyWorkspace 7 (by decide)
  have h8 := emptyWorkspace 8 (by decide)
  have work : ∀ i : Tape, 9 ≤ i.val → base (slots i) = [] :=
    fun i hi => emptyWorkspace i (by omega)
  let afterLeft := Function.update base (slots 6) (num * itemDen).bits
  let afterRight := Function.update afterLeft (slots 7) (itemNum * den).bits
  let afterDen := Function.update afterRight (slots 5) (den * itemDen).bits
  let afterAdd := BinaryAddMachine.tapes (slots 6) (slots 7) (slots 8)
    afterDen [] [] (num * itemDen + itemNum * den).bits.reverse
  have leftRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .leftNumerator .copyLeft)), BinaryAddMachine.clean ambient, base⟩
      (some ⟨some (labels (.multiply .rightNumerator .copyLeft)),
        BinaryAddMachine.clean ambient, afterLeft⟩)
      (BinaryMulMachine.timePolynomial.eval (num.size + itemDen.size)) := by
    have h := BinaryMulMachine.multiplyNatInPolynomialTime
      ((productTapes .leftNumerator).trans slots)
      (fun l => labels (.multiply .leftNumerator l))
      (productExit labels .leftNumerator) p
      (fun l => atLabels (.multiply .leftNumerator l))
      base num itemDen hnum hitemDen (workspace_multiply slots base work .leftNumerator) ambient
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .leftNumerator .copyLeft)), BinaryAddMachine.clean ambient, base⟩
      (some ⟨some (labels (.multiply .rightNumerator .copyLeft)), BinaryAddMachine.clean ambient,
        Function.update base (slots 6) ((num * itemDen).bits ++ base (slots 6))⟩) _ at h
    simpa only [h6, List.append_nil, afterLeft] using h
  have workLeft := workspace_update slots base work 6 (by decide) (num * itemDen).bits
  have rightRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .rightNumerator .copyLeft)),
        BinaryAddMachine.clean ambient, afterLeft⟩
      (some ⟨some (labels (.multiply .denominator .copyLeft)),
        BinaryAddMachine.clean ambient, afterRight⟩)
      (BinaryMulMachine.timePolynomial.eval (itemNum.size + den.size)) := by
    have h := BinaryMulMachine.multiplyNatInPolynomialTime
      ((productTapes .rightNumerator).trans slots)
      (fun l => labels (.multiply .rightNumerator l))
      (productExit labels .rightNumerator) p
      (fun l => atLabels (.multiply .rightNumerator l))
      afterLeft itemNum den
      (by
        change afterLeft (slots 2) = itemNum.bits
        simpa [afterLeft, hd 2 6 (by decide)] using hitemNum)
      (by
        change afterLeft (slots 1) = den.bits
        simpa [afterLeft, hd 1 6 (by decide)] using hden)
      (workspace_multiply slots afterLeft workLeft .rightNumerator) ambient
    have hout : afterLeft (slots 7) = [] := by simp [afterLeft, hd 7 6 (by decide), h7]
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .rightNumerator .copyLeft)), BinaryAddMachine.clean ambient, afterLeft⟩
      (some ⟨some (labels (.multiply .denominator .copyLeft)), BinaryAddMachine.clean ambient,
        Function.update afterLeft (slots 7) ((itemNum * den).bits ++ afterLeft (slots 7))⟩) _ at h
    simpa only [hout, List.append_nil, afterRight] using h
  have workRight := workspace_update slots afterLeft workLeft 7 (by decide) (itemNum * den).bits
  have denominatorRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .denominator .copyLeft)),
        BinaryAddMachine.clean ambient, afterRight⟩
      (some ⟨some (labels .add), BinaryAddMachine.clean ambient, afterDen⟩)
      (BinaryMulMachine.timePolynomial.eval (den.size + itemDen.size)) := by
    have h := BinaryMulMachine.multiplyNatInPolynomialTime
      ((productTapes .denominator).trans slots)
      (fun l => labels (.multiply .denominator l))
      (productExit labels .denominator) p
      (fun l => atLabels (.multiply .denominator l))
      afterRight den itemDen
      (by
        change afterRight (slots 1) = den.bits
        simpa [afterRight, afterLeft, hd 1 6 (by decide), hd 1 7 (by decide)] using hden)
      (by
        change afterRight (slots 3) = itemDen.bits
        simpa [afterRight, afterLeft, hd 3 6 (by decide), hd 3 7 (by decide)] using hitemDen)
      (workspace_multiply slots afterRight workRight .denominator) ambient
    have hout : afterRight (slots 5) = [] := by
      simp [afterRight, afterLeft, hd 5 6 (by decide), hd 5 7 (by decide), h5]
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .denominator .copyLeft)), BinaryAddMachine.clean ambient, afterRight⟩
      (some ⟨some (labels .add), BinaryAddMachine.clean ambient,
        Function.update afterRight (slots 5) ((den * itemDen).bits ++ afterRight (slots 5))⟩) _ at h
    simpa only [hout, List.append_nil, afterDen] using h
  have den6 : afterDen (slots 6) = (num * itemDen).bits := by
    simp [afterDen, afterRight, afterLeft, hd 6 5 (by decide), hd 6 7 (by decide)]
  have den7 : afterDen (slots 7) = (itemNum * den).bits := by
    simp [afterDen, afterRight, hd 7 5 (by decide)]
  have den8 : afterDen (slots 8) = [] := by
    simp [afterDen, afterRight, afterLeft, hd 8 5 (by decide), hd 8 6 (by decide),
      hd 8 7 (by decide), h8]
  have addRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .add), BinaryAddMachine.clean ambient, afterDen⟩
      (some ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterAdd⟩)
      (max (num * itemDen).size (itemNum * den).size + 1) := by
    have h := BinaryAddMachine.addNatInTime (slots 6) (slots 7) (slots 8)
      (hd 6 7 (by decide)) (hd 6 8 (by decide)) (hd 7 8 (by decide))
      (labels .add) (some (labels .restore)) p (atLabels .add)
      afterDen ambient (num * itemDen) (itemNum * den) []
    have initial : BinaryAddMachine.tapes (slots 6) (slots 7) (slots 8) afterDen
        (num * itemDen).bits (itemNum * den).bits [] = afterDen := by
      rw [← den6, ← den7, ← den8]
      simp [BinaryAddMachine.tapes]
    simpa only [initial, List.append_nil, afterAdd] using h
  have add8 : afterAdd (slots 8) = (num * itemDen + itemNum * den).bits.reverse := by
    simp [afterAdd, BinaryAddMachine.tapes]
  have add4 : afterAdd (slots 4) = [] := by
    simp [afterAdd, BinaryAddMachine.tapes, afterDen, afterRight, afterLeft,
      hd 4 5 (by decide), hd 4 6 (by decide), hd 4 7 (by decide), hd 4 8 (by decide), h4]
  have finalTapes : MachineTransfer.tapesAt (slots 8) (slots 4) afterAdd []
      (num * itemDen + itemNum * den).bits = resultTapes slots base num den itemNum itemDen := by
    funext k
    by_cases h4k : k = slots 4
    · subst k; simp [MachineTransfer.tapesAt, resultTapes]
    by_cases h5k : k = slots 5
    · subst k
      simp [MachineTransfer.tapesAt, afterAdd, BinaryAddMachine.tapes, afterDen,
        resultTapes, hd 5 4 (by decide), hd 5 6 (by decide), hd 5 7 (by decide),
        hd 5 8 (by decide)]
    by_cases h6k : k = slots 6
    · subst k
      simp [MachineTransfer.tapesAt, afterAdd, BinaryAddMachine.tapes, resultTapes,
        hd 6 4 (by decide), hd 6 5 (by decide), hd 6 7 (by decide), hd 6 8 (by decide), h6]
    by_cases h7k : k = slots 7
    · subst k
      simp [MachineTransfer.tapesAt, afterAdd, BinaryAddMachine.tapes, resultTapes,
        hd 7 4 (by decide), hd 7 5 (by decide), hd 7 8 (by decide), h7]
    by_cases h8k : k = slots 8
    · subst k
      simp [MachineTransfer.tapesAt, resultTapes, hd 8 4 (by decide), hd 8 5 (by decide), h8]
    simp [MachineTransfer.tapesAt, afterAdd, BinaryAddMachine.tapes, afterDen,
      afterRight, afterLeft, resultTapes, h4k, h5k, h6k, h7k, h8k]
  have restoreRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterAdd⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        resultTapes slots base num den itemNum itemDen⟩)
      ((num * itemDen + itemNum * den).size + 1) := by
    have h := MachineTransfer.transferAtInTime (slots 8) (slots 4)
      (hd 8 4 (by decide)) (id : Bool → Bool) false (labels .restore) exit p
      (by simpa only [statement] using atLabels .restore)
      afterAdd ((ambient, false), none) none
    simpa only [add8, add4, List.length_reverse, List.reverse_reverse,
      List.map_id_fun, id_eq, List.append_nil, ← Nat.size_eq_bits_len, finalTapes,
      BinaryAddMachine.clean, BinaryAddMachine.state] using h
  have firstTwo := StateTransition.EvalsToInTime.trans (TM2.step p) _ _ _ _ _ leftRun rightRun
  have firstThree := StateTransition.EvalsToInTime.trans (TM2.step p) _ _ _ _ _ firstTwo denominatorRun
  have firstFour := StateTransition.EvalsToInTime.trans (TM2.step p) _ _ _ _ _ firstThree addRun
  have full := StateTransition.EvalsToInTime.trans (TM2.step p) _ _ _ _ _ firstFour restoreRun
  exact { toEvalsTo := full.toEvalsTo
          steps_le_m := by
            have bound := full.steps_le_m
            unfold arithmeticBudget
            omega }

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X ^ 2 + Polynomial.C 44 * Polynomial.X + Polynomial.C 39

theorem arithmeticBudget_le (A D a d : Nat) :
    arithmeticBudget A D a d ≤ timePolynomial.eval (A.size + D.size + a.size + d.size) := by
  let s := A.size + D.size + a.size + d.size
  have hm₁ := MachineComposition.natPolynomial_eval_mono BinaryMulMachine.timePolynomial
    (show A.size + d.size ≤ s by dsimp [s]; omega)
  have hm₂ := MachineComposition.natPolynomial_eval_mono BinaryMulMachine.timePolynomial
    (show a.size + D.size ≤ s by dsimp [s]; omega)
  have hm₃ := MachineComposition.natPolynomial_eval_mono BinaryMulMachine.timePolynomial
    (show D.size + d.size ≤ s by dsimp [s]; omega)
  have hp₁ := BinaryArithmetic.size_mul_le A d
  have hp₂ := BinaryArithmetic.size_mul_le a D
  have hs := BinaryArithmetic.size_add_le (A * d) (a * D)
  have hprod : max (A * d).size (a * D).size ≤ s := by dsimp [s]; omega
  have hsum : (A * d + a * D).size ≤ s + 1 := by omega
  unfold arithmeticBudget
  have hbound :
      BinaryMulMachine.timePolynomial.eval (A.size + d.size) +
        BinaryMulMachine.timePolynomial.eval (a.size + D.size) +
        BinaryMulMachine.timePolynomial.eval (D.size + d.size) +
        (max (A * d).size (a * D).size + 1) + ((A * d + a * D).size + 1) ≤
      3 * BinaryMulMachine.timePolynomial.eval s + 2 * s + 3 := by omega
  apply hbound.trans
  simp only [timePolynomial, BinaryMulMachine.timePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  dsimp [s]
  omega

noncomputable def arithmeticInPolynomialTime (slots : Tape ↪ K) (labels : Label → Λ)
    (exit : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (num den itemNum itemDen : Nat)
    (hnum : base (slots 0) = num.bits) (hden : base (slots 1) = den.bits)
    (hitemNum : base (slots 2) = itemNum.bits) (hitemDen : base (slots 3) = itemDen.bits)
    (emptyWorkspace : ∀ i : Tape, 4 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .leftNumerator .copyLeft)), BinaryAddMachine.clean ambient, base⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        resultTapes slots base num den itemNum itemDen⟩)
      (timePolynomial.eval (num.size + den.size + itemNum.size + itemDen.size)) where
  toEvalsTo := (arithmeticInTime slots labels exit p atLabels base num den itemNum itemDen
    hnum hden hitemNum hitemDen emptyWorkspace ambient).toEvalsTo
  steps_le_m := (arithmeticInTime slots labels exit p atLabels base num den itemNum itemDen
    hnum hden hitemNum hitemDen emptyWorkspace ambient).steps_le_m.trans
      (arithmeticBudget_le num den itemNum itemDen)

end BinPackingGap.ExtensionFractionMachine

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

inductive Field
  | numerator | denominator | label
  deriving DecidableEq

protected abbrev Field.enumList : List Field := [.numerator, .denominator, .label]

protected theorem Field.enumList_getElem?_ctorIdx_eq (x : Field) :
    Field.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Compare
  | label | capacity
  deriving DecidableEq

protected abbrev Compare.enumList : List Compare := [.label, .capacity]

protected theorem Compare.enumList_getElem?_ctorIdx_eq (x : Compare) :
    Compare.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Compare.enumList_nodup : Compare.enumList.Nodup := by decide

instance : Fintype Compare where
  elems := ⟨Compare.enumList, Compare.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | guard
  | number (field : Field) (phase : ExtensionNatMachine.Label)
  | compare (which : Compare) (phase : BinaryOrderMachine.PreserveLabel)
  | fraction (phase : ExtensionFractionMachine.Label)
  | clearOldNumerator | clearOldDenominator
  | numeratorOut | numeratorBack | denominatorOut | denominatorBack
  | clearItemNumerator | clearItemDenominator | clearItemLabel
  deriving DecidableEq, Fintype

abbrev Tape := Fin 22
abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := BinaryAddMachine.State (A × Ordering)

def numberTapes : Field → (Fin 3 ↪ Tape)
  | .numerator => ⟨![2, 5, 10], by decide⟩
  | .denominator => ⟨![2, 6, 10], by decide⟩
  | .label => ⟨![3, 7, 10], by decide⟩

def compareTapes : Compare → (Fin 5 ↪ Tape)
  | .label => ⟨![7, 4, 8, 9, 10], by decide⟩
  | .capacity => ⟨![11, 12, 8, 9, 10], by decide⟩

def fractionTapes : ExtensionFractionMachine.Tape ↪ Tape :=
  ⟨![0, 1, 5, 6, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21], by decide⟩

def afterNumber {Λ : Type} (labels : Label → Λ) : Field → Option Λ
  | .numerator => some (labels (.number .denominator .scan))
  | .denominator => some (labels (.number .label .scan))
  | .label => some (labels (.compare .label .leftOut))

def comparisonExits {Λ : Type} (labels : Label → Λ) (rejected : Option Λ) :
    Compare → Ordering → Option Λ
  | .label, .eq => some (labels (.fraction (.multiply .leftNumerator .copyLeft)))
  | .label, _ => some (labels .clearItemNumerator)
  | .capacity, .gt => rejected
  | .capacity, _ => some (labels .clearOldNumerator)

variable {K Λ A : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => BinaryAddMachine.clean state.1.1.1)
    (match exit with | none => .halt | some label => .goto fun _ => label)

def statement (slots : Tape ↪ K) (labels : Label → Λ)
    (accepted rejected : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .guard =>
      .pop (slots 2) (fun state head => ((state.1.1, head), state.2))
        (.pop (slots 3) (fun state head => (state.1, head))
          (.branch (fun state => decide (state.1.2 = some true ∧ state.2 = some true))
            (finish (some (labels (.number .numerator .scan))))
            (.branch (fun state => decide (state.1.2 = some false ∧ state.2 = some false))
              (finish accepted) (finish rejected))))
  | .number field phase =>
      ExtensionNatMachine.statement ((numberTapes field).trans slots)
        (fun phase => labels (.number field phase)) (afterNumber labels field) rejected phase
  | .compare which phase =>
      ExtensionNatMachine.orderStatement ((compareTapes which).trans slots)
        (fun phase => labels (.compare which phase))
        (comparisonExits labels rejected which) phase
  | .fraction phase =>
      ExtensionFractionMachine.statement (fractionTapes.trans slots)
        (fun phase => labels (.fraction phase))
        (some (labels (.compare .capacity .leftOut))) phase
  | .clearOldNumerator =>
      MachineDrain.drain (slots 0) (labels .clearOldNumerator)
        (some (labels .clearOldDenominator))
  | .clearOldDenominator =>
      MachineDrain.drain (slots 1) (labels .clearOldDenominator)
        (some (labels .numeratorOut))
  | .numeratorOut =>
      MachineTransfer.loopAt (slots 11) (slots 10) id false
        (labels .numeratorOut) (some (labels .numeratorBack))
  | .numeratorBack =>
      MachineTransfer.loopAt (slots 10) (slots 0) id false
        (labels .numeratorBack) (some (labels .denominatorOut))
  | .denominatorOut =>
      MachineTransfer.loopAt (slots 12) (slots 10) id false
        (labels .denominatorOut) (some (labels .denominatorBack))
  | .denominatorBack =>
      MachineTransfer.loopAt (slots 10) (slots 1) id false
        (labels .denominatorBack) (some (labels .clearItemNumerator))
  | .clearItemNumerator =>
      MachineDrain.drain (slots 5) (labels .clearItemNumerator)
        (some (labels .clearItemDenominator))
  | .clearItemDenominator =>
      MachineDrain.drain (slots 6) (labels .clearItemDenominator)
        (some (labels .clearItemLabel))
  | .clearItemLabel =>
      MachineDrain.drain (slots 7) (labels .clearItemLabel) (some (labels .guard))

def allTapes : List Tape := List.ofFn id

inductive FullLabel
  | initialize
  | core (label : Label)
  | clear (result : Bool) (phase : MachineDrainMany.Label allTapes)
  | emit (result : Bool)
  deriving DecidableEq, Fintype

def cleanupEntry (result : Bool) : Option FullLabel :=
  MachineDrainMany.entry allTapes (FullLabel.clear result) (some (.emit result))

def program : FullLabel → TM2.Stmt (Alphabet (K := Tape)) FullLabel (State Unit)
  | .initialize => .push 1 (fun _ => true) (.goto fun _ => .core .guard)
  | .core label => statement (Function.Embedding.refl Tape) FullLabel.core
      (cleanupEntry true) (cleanupEntry false) label
  | .clear result phase =>
      MachineDrainMany.instruction allTapes (FullLabel.clear result) (some (.emit result)) phase
  | .emit result =>
      .push 0 (fun _ => result)
        (.load (fun _ => BinaryAddMachine.clean ((), .eq)) .halt)

def machine : FinTM2 where
  K := Tape
  k₀ := 2
  k₁ := 0
  Γ _ := Bool
  Λ := FullLabel
  main := .initialize
  σ := State Unit
  initialState := BinaryAddMachine.clean ((), .eq)
  m := program

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

def inputTapes (base : Tape → List Bool) (numerator denominator selected : Nat)
    (items : RawInstance) (assignments : List Nat) : Tape → List Bool := fun k =>
  if k = 0 then numerator.bits
  else if k = 1 then denominator.bits
  else if k = 2 then BinaryEncoding.rawInstanceBits items
  else if k = 3 then BinaryEncoding.assignmentBits assignments
  else if k = 4 then selected.bits
  else base k

def initialTapes (items : RawInstance) (assignments : List Nat) (selected : Nat) :
    Tape → List Bool := fun k =>
  if k = 2 then BinaryEncoding.rawInstanceBits items
  else if k = 3 then BinaryEncoding.assignmentBits assignments
  else if k = 4 then selected.bits
  else []

def initialCfg (items : RawInstance) (assignments : List Nat) (selected : Nat) : machine.Cfg :=
  ⟨some .initialize, BinaryAddMachine.clean ((), .eq), initialTapes items assignments selected⟩

def finalTapes (result : Bool) : Tape → List Bool := fun k => if k = 0 then [result] else []

def finalCfg (result : Bool) : machine.Cfg :=
  ⟨none, BinaryAddMachine.clean ((), .eq), finalTapes result⟩

def inputLength (items : RawInstance) (assignments : List Nat) (selected : Nat) : Nat :=
  (BinaryEncoding.rawInstanceBits items).length +
    (BinaryEncoding.assignmentBits assignments).length + selected.size

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 4096 * (Polynomial.X + 1) ^ 3

theorem initializeStep (items : RawInstance) (assignments : List Nat) (selected : Nat) :
    machine.step (initialCfg items assignments selected) =
      some ⟨some (.core .guard), BinaryAddMachine.clean ((), .eq),
        inputTapes (fun _ => []) 0 1 selected items assignments⟩ := by
  change some (TM2.stepAux (program .initialize) _ _) = _
  simp only [program, TM2.stepAux]
  congr 1
  congr 1
  funext k
  fin_cases k <;> simp [initialTapes, inputTapes]

theorem cleanup_tapes (base : Tape → List Bool) :
    MachineDrainMany.finalTapes allTapes base = fun _ => [] := by
  funext k
  apply MachineDrainMany.finalTapes_mem
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

def cleanupInTime (result : Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨cleanupEntry result, BinaryAddMachine.clean ((), .eq), base⟩
      (some (finalCfg result))
      (MachineDrainMany.lengthSum allTapes base + 23) := by
  have first := MachineDrainMany.execution allTapes (FullLabel.clear result)
    (some (.emit result)) program (fun _ => rfl) base
    ((((), .eq), false), none) none
  rw [cleanup_tapes] at first
  have first' : StateTransition.EvalsToInTime machine.step
      ⟨cleanupEntry result, BinaryAddMachine.clean ((), .eq), base⟩
      (some ⟨some (.emit result), BinaryAddMachine.clean ((), .eq), fun _ => []⟩)
      (MachineDrainMany.lengthSum allTapes base + 22) := by
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨cleanupEntry result, BinaryAddMachine.clean ((), .eq), base⟩
      (some ⟨some (.emit result), BinaryAddMachine.clean ((), .eq), fun _ => []⟩)
      (MachineDrainMany.lengthSum allTapes base + 22)
    simpa only [cleanupEntry, BinaryAddMachine.clean, BinaryAddMachine.state,
      MachineDrainMany.finalRegister_none, allTapes, List.length_ofFn] using first
  have second : StateTransition.EvalsToInTime machine.step
      ⟨some (.emit result), BinaryAddMachine.clean ((), .eq), fun _ => []⟩
      (some (finalCfg result)) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (.emit result)) _ _) = _
      simp only [program, TM2.stepAux, finalCfg]
      congr 1
      congr 1
      funext k
      change Function.update (fun _ : Tape => ([] : List Bool)) 0 [result] k = finalTapes result k
      by_cases h : k = 0
      · subst k
        rfl
      · rw [Function.update_of_ne h]
        simp only [finalTapes, ite_eq_right h]
    steps_le_m := Nat.le_refl _ }
  have combined := StateTransition.EvalsToInTime.trans machine.step _ _ _ _ _ first' second
  exact { toEvalsTo := combined.toEvalsTo
          steps_le_m := by
            have bound := combined.steps_le_m
            omega }

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionArithmeticBounds

open BinPackingGames.Foundations.Complexity

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 512 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp] theorem timePolynomial_eval (inputLength : Nat) :
    timePolynomial.eval inputLength = 512 * (inputLength + 1) ^ 2 := by
  simp [timePolynomial]

theorem fractionTime_le (operandLength inputLength : Nat)
    (bounded : operandLength ≤ 4 * (inputLength + 1)) :
    ExtensionFractionMachine.timePolynomial.eval operandLength ≤
      timePolynomial.eval inputLength := by
  apply (MachineComposition.natPolynomial_eval_mono
    ExtensionFractionMachine.timePolynomial bounded).trans
  simp only [ExtensionFractionMachine.timePolynomial, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  nlinarith

theorem scan_arithmeticBudget_le_input (bins : Nat) (before after : RawInstance)
    (item : Nat × Nat) (fixed : List (Option Nat))
    (assignments : List Nat) (label : Nat)
    (valid : (before ++ item :: after).Valid)
    (accepted : (RawPacking.loadFraction before assignments label).1 ≤
      (RawPacking.loadFraction before assignments label).2) :
    let total := RawPacking.loadFraction before assignments label
    ExtensionFractionMachine.arithmeticBudget total.1 total.2 item.1 item.2 ≤
      timePolynomial.eval (BinaryEncoding.extensionBits bins
        (before ++ item :: after) fixed).length := by
  dsimp only
  apply (ExtensionFractionMachine.arithmeticBudget_le _ _ _ _).trans
  apply fractionTime_le
  exact ExtensionWitness.scan_operands_width_le_input
    bins before after item fixed assignments label valid accepted

theorem visit_budget_le (visits inputLength : Nat)
    (bounded : visits ≤ inputLength ^ 2) :
    visits * timePolynomial.eval inputLength ≤ 512 * (inputLength + 1) ^ 4 := by
  rw [timePolynomial_eval]
  have square_bound : inputLength ^ 2 ≤ (inputLength + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_succ inputLength) 2
  have product_bound := Nat.mul_le_mul_right
    (512 * (inputLength + 1) ^ 2) (bounded.trans square_bound)
  apply product_bound.trans
  exact le_of_eq (by ring)

end BinPackingGap.ExtensionArithmeticBounds

namespace BinPackingGap.ExtensionCapacityMachine

section

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

def clean : State Unit := BinaryAddMachine.clean ((), .eq)

def cfg (label : Option FullLabel) (tapes : Tape → List Bool) : machine.Cfg :=
  ⟨label, clean, tapes⟩

def work (numerator denominator items assignments selected a d j nextNumerator nextDenominator
    : List Bool) (scratch : List Bool := []) : Tape → List Bool
  | 0 => numerator
  | 1 => denominator
  | 2 => items
  | 3 => assignments
  | 4 => selected
  | 5 => a
  | 6 => d
  | 7 => j
  | 10 => scratch
  | 11 => nextNumerator
  | 12 => nextDenominator
  | _ => []

def ready (numerator denominator selected : Nat) (items : RawInstance)
    (assignments : List Nat) : Tape → List Bool :=
  work numerator.bits denominator.bits (BinaryEncoding.rawInstanceBits items)
    (BinaryEncoding.assignmentBits assignments) selected.bits [] [] [] [] []

private theorem update0 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 0 r = work r D i w s a d j U V t := by
  funext k; fin_cases k <;> rfl
private theorem update1 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 1 r = work N r i w s a d j U V t := by
  funext k; fin_cases k <;> rfl
private theorem update2 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 2 r = work N D r w s a d j U V t := by
  funext k; fin_cases k <;> rfl
private theorem update3 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 3 r = work N D i r s a d j U V t := by
  funext k; fin_cases k <;> rfl
private theorem update5 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 5 r = work N D i w s r d j U V t := by
  funext k; fin_cases k <;> rfl
private theorem update6 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 6 r = work N D i w s a r j U V t := by
  funext k; fin_cases k <;> rfl
private theorem update7 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 7 r = work N D i w s a d r U V t := by
  funext k; fin_cases k <;> rfl
private theorem update10 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 10 r = work N D i w s a d j U V r := by
  funext k; fin_cases k <;> rfl
private theorem update11 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 11 r = work N D i w s a d j r V t := by
  funext k; fin_cases k <;> rfl
private theorem update12 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 12 r = work N D i w s a d j U r t := by
  funext k; fin_cases k <;> rfl

def oneStep {start finish : machine.Cfg} (h : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := h
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

theorem guard_cons_step (N D i w s a d j U V : List Bool) :
    machine.step (cfg (some (.core .guard)) (work N D (true :: i) (true :: w) s a d j U V)) =
      some (cfg (some (.core (.number .numerator .scan))) (work N D i w s a d j U V)) := by
  change some (TM2.stepAux (program (.core .guard)) _ _) = _
  simp [program, statement, finish, cfg, clean, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, Function.Embedding.coe_refl, id_eq,
    work, update2, update3]
  rfl

theorem guard_nil_step (N D s : List Bool) :
    machine.step (cfg (some (.core .guard)) (work N D [false] [false] s [] [] [] [] [])) =
      some (cfg (cleanupEntry true) (work N D [] [] s [] [] [] [] [])) := by
  change some (TM2.stepAux (program (.core .guard)) _ _) = _
  cases h : cleanupEntry true <;>
    simp [program, statement, finish, cfg, clean, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, Function.Embedding.coe_refl, id_eq,
      work, update2, update3, h] <;> rfl

def numberInTime (field : Field) (base : Tape → List Bool) (n : Nat) (suffix : List Bool)
    (input : base (numberTapes field 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (numberTapes field 2) = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core (.number field .scan))) base)
      (some (cfg (afterNumber FullLabel.core field)
        (ExtensionNatMachine.resultTapes (numberTapes field) base n suffix)))
      (2 * n.size + 2) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core (.number field .scan)), BinaryAddMachine.clean ((), .eq), base⟩
    (some ⟨afterNumber FullLabel.core field, BinaryAddMachine.clean ((), .eq),
      ExtensionNatMachine.resultTapes (numberTapes field) base n suffix⟩) _
  exact ExtensionNatMachine.natInTime (numberTapes field)
    (fun phase => FullLabel.core (.number field phase))
    (afterNumber FullLabel.core field) (cleanupEntry false) program (fun _ => rfl)
    base n suffix input scratchEmpty ((), .eq)

def parseRowInTime (N D selected : List Bool) (items assignments : List Bool) (a d j : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core (.number .numerator .scan)))
        (work N D (BinaryEncoding.natBits a ++ BinaryEncoding.natBits d ++ items)
          (BinaryEncoding.natBits j ++ assignments) selected [] [] [] [] []))
      (some (cfg (some (.core (.compare .label .leftOut)))
        (work N D items assignments selected a.bits d.bits j.bits [] [])))
      ((2 * a.size + 2) + (2 * d.size + 2) + (2 * j.size + 2)) := by
  have first := numberInTime .numerator
    (work N D (BinaryEncoding.natBits a ++ BinaryEncoding.natBits d ++ items)
      (BinaryEncoding.natBits j ++ assignments) selected [] [] [] [] [])
    a (BinaryEncoding.natBits d ++ items) (by simp [numberTapes, work, List.append_assoc]) rfl
  have second := numberInTime .denominator
    (work N D (BinaryEncoding.natBits d ++ items)
      (BinaryEncoding.natBits j ++ assignments) selected a.bits [] [] [] []) d items rfl rfl
  have third := numberInTime .label
    (work N D items (BinaryEncoding.natBits j ++ assignments) selected a.bits d.bits [] [] [])
    j assignments rfl rfl
  simp only [numberTapes, afterNumber, ExtensionNatMachine.resultTapes,
    Function.Embedding.coeFn_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    update2, update3, update5, update6, update7, work, List.append_nil] at first second third
  exact join (join first second) third

def compareInTime (which : Compare) (base : Tape → List Bool) (a b : Nat)
    (leftWord : base (compareTapes which 0) = a.bits)
    (rightWord : base (compareTapes which 1) = b.bits)
    (leftEmpty : base (compareTapes which 2) = [])
    (rightEmpty : base (compareTapes which 3) = [])
    (scratchEmpty : base (compareTapes which 4) = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core (.compare which .leftOut))) base)
      (some (cfg (comparisonExits FullLabel.core (cleanupEntry false) which
        (BinaryOrderMachine.orderNat a b .eq)) base))
      (BinaryOrderMachine.preservingSteps a.size b.size) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core (.compare which .leftOut)), BinaryAddMachine.clean ((), .eq), base⟩
    (some ⟨comparisonExits FullLabel.core (cleanupEntry false) which
      (BinaryOrderMachine.orderNat a b .eq), BinaryAddMachine.clean ((), .eq), base⟩) _
  exact ExtensionNatMachine.preservingOrderInTime (compareTapes which)
    (fun phase => FullLabel.core (.compare which phase))
    (comparisonExits FullLabel.core (cleanupEntry false) which)
    program (fun _ => rfl) base a b leftWord rightWord leftEmpty rightEmpty scratchEmpty ()

theorem labelComparisonExit (assigned selected : Nat) :
    comparisonExits FullLabel.core (cleanupEntry false) .label
        (BinaryOrderMachine.orderNat assigned selected .eq) =
      some (.core (if assigned = selected then .fraction (.multiply .leftNumerator .copyLeft)
        else .clearItemNumerator)) := by
  unfold BinaryOrderMachine.orderNat
  split_ifs <;> simp_all [comparisonExits]
  omega

theorem capacityComparisonExit (numerator denominator : Nat) :
    comparisonExits FullLabel.core (cleanupEntry false) .capacity
        (BinaryOrderMachine.orderNat numerator denominator .eq) =
      if numerator ≤ denominator then some (.core .clearOldNumerator) else cleanupEntry false := by
  unfold BinaryOrderMachine.orderNat
  split_ifs <;> simp_all [comparisonExits] <;> omega

noncomputable def fractionInTime (num den a d : Nat) (items assignments selected j : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core (.fraction (.multiply .leftNumerator .copyLeft))))
        (work num.bits den.bits items assignments selected a.bits d.bits j [] []))
      (some (cfg (some (.core (.compare .capacity .leftOut)))
        (work num.bits den.bits items assignments selected a.bits d.bits j
          (num * d + a * den).bits (den * d).bits)))
      (ExtensionFractionMachine.arithmeticBudget num den a d) := by
  have run := ExtensionFractionMachine.arithmeticInTime fractionTapes
    (fun phase => .core (.fraction phase)) (some (.core (.compare .capacity .leftOut)))
    program (fun _ => rfl)
    (work num.bits den.bits items assignments selected a.bits d.bits j [] [])
    num den a d rfl rfl rfl rfl
    (by intro i hi; fin_cases i <;> simp_all [fractionTapes, work]) ((), .eq)
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core (.fraction (.multiply .leftNumerator .copyLeft))),
      BinaryAddMachine.clean ((), .eq),
      work num.bits den.bits items assignments selected a.bits d.bits j [] []⟩
    (some ⟨some (.core (.compare .capacity .leftOut)), BinaryAddMachine.clean ((), .eq),
      Function.update
        (Function.update (work num.bits den.bits items assignments selected a.bits d.bits j [] [])
          12 (den * d).bits) 11 (num * d + a * den).bits⟩) _ at run
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core (.fraction (.multiply .leftNumerator .copyLeft))),
      BinaryAddMachine.clean ((), .eq),
      work num.bits den.bits items assignments selected a.bits d.bits j [] []⟩
    (some ⟨some (.core (.compare .capacity .leftOut)), BinaryAddMachine.clean ((), .eq),
      work num.bits den.bits items assignments selected a.bits d.bits j
        (num * d + a * den).bits (den * d).bits⟩) _
  simpa only [update11, update12] using run

def clearRowInTime (N D i w s a d j : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core .clearItemNumerator)) (work N D i w s a d j [] []))
      (some (cfg (some (.core .guard)) (work N D i w s [] [] [] [] [])))
      ((a.length + 1) + (d.length + 1) + (j.length + 1)) := by
  have first := MachineDrain.drainInTime (5 : Tape) (.core .clearItemNumerator)
    (some (.core .clearItemDenominator)) program rfl (work N D i w s a d j [] [])
    ((((), Ordering.eq), false), none) none
  have second := MachineDrain.drainInTime (6 : Tape) (.core .clearItemDenominator)
    (some (.core .clearItemLabel)) program rfl (work N D i w s [] d j [] [])
    ((((), Ordering.eq), false), none) none
  have third := MachineDrain.drainInTime (7 : Tape) (.core .clearItemLabel)
    (some (.core .guard)) program rfl (work N D i w s [] [] j [] [])
    ((((), Ordering.eq), false), none) none
  simp only [update5, work] at first
  simp only [update6, work] at second
  simp only [update7, work] at third
  exact join (join first second) third

def installInTime (N D i w s a d j U V : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core .clearOldNumerator)) (work N D i w s a d j U V))
      (some (cfg (some (.core .clearItemNumerator)) (work U V i w s a d j [] [])))
      (N.length + D.length + 2 * U.length + 2 * V.length + 6) := by
  have oldN := MachineDrain.drainInTime (0 : Tape) (.core .clearOldNumerator)
    (some (.core .clearOldDenominator)) program rfl (work N D i w s a d j U V)
    ((((), Ordering.eq), false), none) none
  have oldD := MachineDrain.drainInTime (1 : Tape) (.core .clearOldDenominator)
    (some (.core .numeratorOut)) program rfl (work [] D i w s a d j U V)
    ((((), Ordering.eq), false), none) none
  have numOut := MachineTransfer.transferAtInTime (11 : Tape) 10 (by decide)
    id false (.core .numeratorOut) (some (.core .numeratorBack)) program rfl
    (work [] [] i w s a d j U V) ((((), Ordering.eq), false), none) none
  have numBack := MachineTransfer.transferAtInTime (10 : Tape) 0 (by decide)
    id false (.core .numeratorBack) (some (.core .denominatorOut)) program rfl
    (work [] [] i w s a d j [] V U.reverse) ((((), Ordering.eq), false), none) none
  have denOut := MachineTransfer.transferAtInTime (12 : Tape) 10 (by decide)
    id false (.core .denominatorOut) (some (.core .denominatorBack)) program rfl
    (work U [] i w s a d j [] V) ((((), Ordering.eq), false), none) none
  have denBack := MachineTransfer.transferAtInTime (10 : Tape) 1 (by decide)
    id false (.core .denominatorBack) (some (.core .clearItemNumerator)) program rfl
    (work U [] i w s a d j [] [] V.reverse) ((((), Ordering.eq), false), none) none
  simp only [update0, work] at oldN
  simp only [update1, work] at oldD
  simp only [MachineTransfer.tapesAt, update11, update10, work, List.map_id_fun,
    id_eq, List.append_nil] at numOut
  simp only [MachineTransfer.tapesAt, update10, update0, work, List.map_id_fun,
    id_eq, List.append_nil, List.reverse_reverse, List.length_reverse] at numBack
  simp only [MachineTransfer.tapesAt, update12, update10, work, List.map_id_fun,
    id_eq, List.append_nil] at denOut
  simp only [MachineTransfer.tapesAt, update10, update1, work, List.map_id_fun,
    id_eq, List.append_nil, List.reverse_reverse, List.length_reverse] at denBack
  have joined := join (join (join (join (join oldN oldD) numOut) numBack) denOut) denBack
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core .clearOldNumerator), BinaryAddMachine.clean ((), .eq), work N D i w s a d j U V⟩
    (some ⟨some (.core .clearItemNumerator), BinaryAddMachine.clean ((), .eq),
      work U V i w s a d j [] []⟩) _
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := by
            have bound := joined.steps_le_m
            omega }

noncomputable def rowCost (num den a d assigned selected : Nat) : Nat :=
  1 + ((2 * a.size + 2) + (2 * d.size + 2) + (2 * assigned.size + 2)) +
    BinaryOrderMachine.preservingSteps assigned.size selected.size +
    ExtensionFractionMachine.arithmeticBudget num den a d +
    BinaryOrderMachine.preservingSteps (num * d + a * den).size (den * d).size +
    (num.size + den.size + 2 * (num * d + a * den).size + 2 * (den * d).size + 6) +
    (a.size + d.size + assigned.size + 3)

end

theorem rowCost_le (num den a d assigned selected B : Nat)
    (accepted : num ≤ den) (itemBound : a ≤ d)
    (denominatorBound : den.size + d.size ≤ B + 1)
    (assignedBound : assigned.size ≤ B) (selectedBound : selected.size ≤ B) :
    rowCost num den a d assigned selected ≤ 1024 * (B + 1) ^ 2 := by
  have numeratorWidth := FractionWidth.size_mono accepted
  have itemWidth := FractionWidth.size_mono itemBound
  have productWidth := (FractionWidth.size_mul_le den d).trans denominatorBound
  have leftWidth : (num * d).size ≤ B + 1 :=
    (FractionWidth.addFraction_left_product_size_le
      (x := (num, den)) (q := (a, d)) accepted).trans denominatorBound
  have rightWidth : (a * den).size ≤ B + 1 :=
    (FractionWidth.addFraction_right_product_size_le
      (x := (num, den)) (q := (a, d)) itemBound).trans denominatorBound
  have sumWidth : (num * d + a * den).size ≤ B + 2 :=
    FractionWidth.size_add_le leftWidth rightWidth
  have arithmeticBound := (ExtensionFractionMachine.arithmeticBudget_le num den a d).trans
    (ExtensionArithmeticBounds.fractionTime_le
      (num.size + den.size + a.size + d.size) B (by omega))
  rw [ExtensionArithmeticBounds.timePolynomial_eval] at arithmeticBound
  have labelComparison := BinaryOrderMachine.preservingSteps_le assigned.size selected.size
  have capacityComparison := BinaryOrderMachine.preservingSteps_le
    (num * d + a * den).size (den * d).size
  unfold rowCost
  nlinarith [Nat.zero_le (B ^ 2)]

theorem next_denominator_budget (den a d B : Nat) (remaining : RawInstance)
    (bounded : den.size + FractionWidth.denominatorBits ((a, d) :: remaining) ≤ B + 1) :
    (den * d).size + FractionWidth.denominatorBits remaining ≤ B + 1 := by
  have product := FractionWidth.size_mul_le den d
  simp only [FractionWidth.denominatorBits_cons] at bounded
  omega

end BinPackingGap.ExtensionCapacityMachine

end OAI
