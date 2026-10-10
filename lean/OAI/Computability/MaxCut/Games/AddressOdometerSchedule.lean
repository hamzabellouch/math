import Mathlib
import OAI.Computability.MaxCut.Machines.MachineTupleOdometer
import OAI.Computability.MaxCut.Machines.CanonicalBodyMachine

namespace OAI

namespace MaxCutGames.Reduction.AddressOdometerSchedule

open Turing
open MaxCutGames.Foundations.Complexity MachineTupleOdometer
open MaxCutGames.Foundations.Hastad
open MachineTransfer

noncomputable section

abbrev Tape := AddressMachineSpace.Tape

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def current (k s d noiseCount : Nat) (i : Fin k) : Tape k s d noiseCount :=
  AddressMachineSpace.current k s d noiseCount i

def remaining (k s d noiseCount : Nat) (i : Fin k) : Tape k s d noiseCount :=
  AddressMachineSpace.remaining k s d noiseCount i

def accumulator (k s d noiseCount : Nat) : Tape k s d noiseCount :=
  AddressMachineSpace.headerTape k s d noiseCount .reversed

def currentAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then current k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

def remainingAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then remaining k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

@[simp] theorem current_eq_iff (i j : Fin k) :
    current k s d noiseCount i = current k s d noiseCount j ↔ i = j := by
  simp [current, AddressMachineSpace.current]
@[simp] theorem remaining_eq_iff (i j : Fin k) :
    remaining k s d noiseCount i = remaining k s d noiseCount j ↔ i = j := by
  simp [remaining, AddressMachineSpace.remaining]
@[simp] theorem current_ne_remaining (i j : Fin k) :
    current k s d noiseCount i ≠ remaining k s d noiseCount j :=
  AddressMachineSpace.current_ne_remaining k s d noiseCount i j
@[simp] theorem remaining_ne_current (i j : Fin k) :
    remaining k s d noiseCount i ≠ current k s d noiseCount j :=
  Ne.symm (current_ne_remaining j i)
@[simp] theorem accumulator_ne_current (i : Fin k) :
    accumulator k s d noiseCount ≠ current k s d noiseCount i :=
  AddressMachineSpace.headerTape_ne_current k s d noiseCount .reversed i
@[simp] theorem accumulator_ne_remaining (i : Fin k) :
    accumulator k s d noiseCount ≠ remaining k s d noiseCount i :=
  AddressMachineSpace.headerTape_ne_remaining k s d noiseCount .reversed i
@[simp] theorem current_ne_accumulator (i : Fin k) :
    current k s d noiseCount i ≠ accumulator k s d noiseCount := Ne.symm (accumulator_ne_current i)
@[simp] theorem remaining_ne_accumulator (i : Fin k) :
    remaining k s d noiseCount i ≠ accumulator k s d noiseCount := Ne.symm (accumulator_ne_remaining i)

/-- Odometer coordinate zero is the low coordinate; physical saved positions
are reversed to match the actual occurrence-tuple enumeration. -/
def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape k s d noiseCount → List Bool) : Tape k s d noiseCount → List Bool
  | .savedIndex i => if h : i.rev.val < q then encodeWord (digits ⟨i.rev.val, h⟩)
      else base (.savedIndex i)
  | .extra (.inr (.inr (.inl i))) => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.extra (.inr (.inr (.inl i))))
  | tape => base tape

def setAcc (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    Tape k s d noiseCount → List Bool := Function.update base (accumulator k s d noiseCount) bits

def putDigit (i : Fin k) (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    Tape k s d noiseCount → List Bool :=
  digitTapes (current k s d noiseCount i) (remaining k s d noiseCount i) base a r [] []

@[simp] theorem setDigits_current (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (i : Fin k) :
    setDigits m digits base (current k s d noiseCount i) =
      if h : i.val < q then encodeWord (digits ⟨i.val, h⟩) else base (current k s d noiseCount i) := by
  simp [setDigits, current, AddressMachineSpace.current]
@[simp] theorem setDigits_remaining (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (i : Fin k) :
    setDigits m digits base (remaining k s d noiseCount i) =
      if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (remaining k s d noiseCount i) := rfl

theorem setDigits_other (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (tape : Tape k s d noiseCount)
    (hc : ∀ i, tape ≠ current k s d noiseCount i)
    (hr : ∀ i, tape ≠ remaining k s d noiseCount i) : setDigits m digits base tape = base tape := by
  cases tape with
  | savedIndex i => exact (hc i.rev (by simp [current, AddressMachineSpace.current])).elim
  | extra e =>
    rcases e with a | a
    · rfl
    · rcases a with a | a
      · rfl
      · rcases a with i | unused
        · exact (hr i rfl).elim
        · rfl
  | _ => rfl

private theorem digitCases_inline_AddressOdometerSchedule {P : Tape k s d noiseCount → Prop} (tape : Tape k s d noiseCount)
    (hc : ∀ i, P (current k s d noiseCount i))
    (hr : ∀ i, P (remaining k s d noiseCount i))
    (other : ∀ tape, (∀ i, tape ≠ current k s d noiseCount i) →
      (∀ i, tape ≠ remaining k s d noiseCount i) → P tape) : P tape := by
  classical
  by_cases h : ∃ i, tape = current k s d noiseCount i
  · obtain ⟨i, rfl⟩ := h; exact hc i
  · by_cases h' : ∃ i, tape = remaining k s d noiseCount i
    · obtain ⟨i, rfl⟩ := h'; exact hr i
    · exact other tape (fun i hi => h ⟨i, hi⟩) (fun i hi => h' ⟨i, hi⟩)

@[simp] theorem setDigits_zero (m : Nat) (digits : Fin 0 → Nat)
    (base : Tape k s d noiseCount → List Bool) : setDigits m digits base = base := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp
  · intro i; simp
  · intro tape hc hr; exact setDigits_other m digits base tape hc hr

@[simp] theorem setDigits_accumulator (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits base (accumulator k s d noiseCount) = base (accumulator k s d noiseCount) := rfl

@[simp] theorem setAcc_self (base : Tape k s d noiseCount → List Bool) :
    setAcc base (base (accumulator k s d noiseCount)) = base := by simp [setAcc]
@[simp] theorem setAcc_setAcc (base : Tape k s d noiseCount → List Bool) (first second : List Bool) :
    setAcc (setAcc base first) second = setAcc base second := by simp [setAcc]
@[simp] theorem setAcc_apply (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setAcc base bits (accumulator k s d noiseCount) = bits := by simp [setAcc]

theorem setDigits_setAcc (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc base bits) = setAcc (setDigits m digits base) bits := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [setDigits_other m digits _ tape hc hr, setAcc, ha]

@[simp] theorem putDigit_current (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (i : Fin k) :
    putDigit j base a r (current k s d noiseCount i) =
      if i = j then encodeWord a else base (current k s d noiseCount i) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Function.update_apply]
@[simp] theorem putDigit_remaining (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (i : Fin k) :
    putDigit j base a r (remaining k s d noiseCount i) =
      if i = j then encodeWord r else base (remaining k s d noiseCount i) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Function.update_apply]

theorem putDigit_other (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (tape : Tape k s d noiseCount)
    (hc : tape ≠ current k s d noiseCount j) (hr : tape ≠ remaining k s d noiseCount j) :
    putDigit j base a r tape = base tape := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hc, hr]

@[simp] theorem putDigit_accumulator (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) : putDigit j base a r (accumulator k s d noiseCount) =
      base (accumulator k s d noiseCount) := by
  apply putDigit_other <;> simp

theorem putDigit_setAcc (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (bits : List Bool) :
    putDigit j (setAcc base bits) a r = setAcc (putDigit j base a r) bits := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [putDigit_other j _ a r tape (hc j) (hr j), setAcc, ha]

theorem setDigits_putDigit (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a r := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro tape hc hr
    simp [setDigits_other m digits _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m (Fin.snoc digits a) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a (m - 1 - a) := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro tape hc hr
    simp [setDigits_other m _ _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc_base (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a (m - 1 - a)) =
      setDigits m (Fin.snoc digits a) base := by
  rw [setDigits_putDigit, setDigits_snoc]

@[simp] theorem setDigits_savedIndex (m : Nat) (digits : Fin k → Nat)
    (base : Tape k s d noiseCount → List Bool) (j : Fin k) :
    setDigits m digits base (.savedIndex j) = encodeWord (digits j.rev) := by
  have h : j.rev.val < k := j.rev.isLt
  simp only [setDigits, h, dite_eq_left]

@[simp] theorem setAcc_other (base : Tape k s d noiseCount → List Bool)
    (bits : List Bool) (tape : Tape k s d noiseCount)
    (h : tape ≠ accumulator k s d noiseCount) : setAcc base bits tape = base tape := by
  simp [setAcc, h]

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

def blocks {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) (d : ℕ) : List Bool :=
  if h : d < m then allBits (fun c => bits (Fin.snoc c ⟨d, h⟩)) else []

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

def configuration (label : Λ) (canonical : σ) (tapes : Tape k s d noiseCount → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ := ⟨some label, (canonical, none), tapes⟩

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ)
    {q : ℕ} (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (digit : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c digit i).val) =
      Fin.snoc (fun i => (c i).val) digit.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) : Configuration (Tape k s d noiseCount) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape k s d noiseCount) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc base ((allBits bits).reverse ++ base (accumulator k s d noiseCount))))

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ k)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (accumulator k s d noiseCount))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt k s d noiseCount)
      (remaining := remainingAt k s d noiseCount) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    dsimp only [tree]
    erw [NestedCycle.LeafBound]
    exact hcount
  | succ q ih =>
    have hqu : q < k := by omega
    let schedule : CycleSchedule (Tape k s d noiseCount) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (accumulator k s d noiseCount))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
            (checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.register schedule.base), tree.LeafBound B := by
      let digit : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c digit)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (accumulator k s d noiseCount)))
        digit.val (m - 1 - digit.val)
      have hrem : m - 1 - digit.val = r.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = digit.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = digit.val + 1 := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, digit.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c digit) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical childBase childBits =
          checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
            schedule.ambient schedule.register schedule.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_accumulator, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) schedule children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, schedule,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        finalConfiguration (next (q + 1)) canonical base bits := by
      simp only [cycleExit, finalConfiguration, configuration, schedule, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
        (cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

/-- The time bound is derived from the concrete schedule, not from the number
of tuples alone. Dimension zero consists of its single actual body trace. -/
theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B : ℕ) (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin k → Fin m) → List Bool)
    (atCheck : ∀ i, i < k → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < k → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) k bodyLabel canonical base)
      (some (finalConfiguration (next k) canonical base bits))
      ((B + 2 * k) * m ^ k)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical
    positive B k (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

@[simp] theorem initial_current (base : Tape k s d noiseCount → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin k) :
    (initialConfiguration (m := m) k bodyLabel canonical base).stk (current k s d noiseCount i) =
      encodeWord 0 := by simp [initialConfiguration, configuration]

@[simp] theorem initial_remaining (base : Tape k s d noiseCount → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin k) :
    (initialConfiguration (m := m) k bodyLabel canonical base).stk (remaining k s d noiseCount i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration]

@[simp] theorem final_current (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) (i : Fin k) :
    (finalConfiguration exitLabel canonical base bits).stk (current k s d noiseCount i) =
      encodeWord 0 := by simp [finalConfiguration, configuration]

@[simp] theorem final_remaining (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) (i : Fin k) :
    (finalConfiguration exitLabel canonical base bits).stk (remaining k s d noiseCount i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration]

@[simp] theorem final_accumulator (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ)
    (bits : (Fin k → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical base bits).stk (accumulator k s d noiseCount) =
      ((tupleOrder m k).flatMap bits).reverse ++ base (accumulator k s d noiseCount) := by
  simp [finalConfiguration, configuration, allBits]

/-- Traversal frames every tape outside the digits and reversed output. -/
theorem final_other (base : Tape k s d noiseCount → List Bool)
    (exitLabel : Λ) (canonical : σ) (bits : (Fin k → Fin m) → List Bool)
    (tape : Tape k s d noiseCount)
    (hc : ∀ i, tape ≠ current k s d noiseCount i)
    (hr : ∀ i, tape ≠ remaining k s d noiseCount i)
    (ha : tape ≠ accumulator k s d noiseCount) :
    (finalConfiguration exitLabel canonical base bits).stk tape = base tape := by
  simp only [finalConfiguration, configuration, setDigits_other m _ _ tape hc hr,
    setAcc_other _ _ tape ha]

end
end MaxCutGames.Reduction.AddressOdometerSchedule

end OAI
