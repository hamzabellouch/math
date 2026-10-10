import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryMachine

namespace OAI

section

namespace KS.W01.FixedStack
open KS.W29 (StackAction FairSeed polynomialFuel)

structure Instruction (stackCount states : ℕ) where
  next : Option (Fin states)
  actions : Vector StackAction stackCount

def Instruction.action {k q : ℕ} (i : Instruction k q) (j : Fin k) : StackAction :=
  i.actions[j.val]

def Instruction.halt (k q : ℕ) : Instruction k q :=
  ⟨none, Vector.ofFn (fun _ => .stay)⟩

structure Machine where
  stackCount : ℕ
  states : ℕ
  initial : Fin states
  inputStack : Fin stackCount
  outputStack : Fin stackCount
  table : List (Instruction stackCount states)

theorem Machine.stackCount_pos (M : Machine) : 0 < M.stackCount :=
  lt_of_le_of_lt (Nat.zero_le M.inputStack.val) M.inputStack.isLt

theorem Machine.states_pos (M : Machine) : 0 < M.states :=
  lt_of_le_of_lt (Nat.zero_le M.initial.val) M.initial.isLt

def haltMachine : Machine := ⟨1, 1, 0, 0, 0, []⟩

structure Config (k q : ℕ) where
  state : Option (Fin q)
  «stacks» : Fin k → List Bool

def headsCode : (k : ℕ) → (Fin k → Fin 3) → ℕ
  | 0, _ => 0
  | k + 1, h => (h 0).val + 3 * headsCode k (fun i => h i.succ)

def decodeHeads : (k : ℕ) → ℕ → Fin k → Fin 3
  | 0, _, i => Fin.elim0 i
  | k + 1, n, i => Fin.cases ⟨n % 3, Nat.mod_lt _ (by decide)⟩ (decodeHeads k (n / 3)) i

theorem headsCode_lt (k : ℕ) (h : Fin k → Fin 3) : headsCode k h < 3 ^ k := by
  induction k with
  | zero => simp [headsCode]
  | succ k ih =>
      have h0 := (h 0).isLt
      have ht := ih (fun i => h i.succ)
      simp only [headsCode, pow_succ]
      omega

@[simp] theorem decodeHeads_headsCode (k : ℕ) (h : Fin k → Fin 3) :
    decodeHeads k (headsCode k h) = h := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
      have h0 := (h 0).isLt
      have hm : ((h 0).val + 3 * headsCode k (fun i => h i.succ)) % 3 = (h 0).val := by
        omega
      have hd : ((h 0).val + 3 * headsCode k (fun i => h i.succ)) / 3 =
          headsCode k (fun i => h i.succ) := by omega
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · apply Fin.ext
        exact hm
      · change decodeHeads k (((h 0).val + 3 * headsCode k (fun i => h i.succ)) / 3) j = _
        rw [hd, ih]

def observedHeads {k q : ℕ} (c : Config k q) : Fin k → Fin 3 :=
  fun j => ⟨KS.W29.topCode (c.«stacks» j), KS.W29.topCode_lt_three _⟩

def headFin {k : ℕ} (h : Fin k → Fin 3) : Fin (3 ^ k) :=
  ⟨headsCode k h, headsCode_lt k h⟩

def coinFin (b : Bool) : Fin 2 := if b then 1 else 0

def tableIndex {k q : ℕ} (s : Fin q) (h : Fin k → Fin 3) (b : Bool) :
    Fin (q * (3 ^ k * 2)) :=
  finProdFinEquiv (s, finProdFinEquiv (headFin h, coinFin b))

theorem tableIndex_val {k q : ℕ} (s : Fin q) (h : Fin k → Fin 3) (b : Bool) :
    (tableIndex s h b).val = (3 ^ k * 2) * s.val +
      2 * headsCode k h + KS.W29.bitCode b := by
  change (coinFin b).val + 2 * (headFin h).val + (3 ^ k * 2) * s.val = _
  cases b <;> simp [coinFin, headFin, KS.W29.bitCode] <;> omega

def Machine.step (M : Machine) (c : Config M.stackCount M.states) (b : Bool) :
    Config M.stackCount M.states :=
  match c.state with
  | none => c
  | some s =>
      let i := M.table.getD (tableIndex s (observedHeads c) b).val
        (Instruction.halt M.stackCount M.states)
      ⟨i.next, fun j => (i.action j).apply (c.«stacks» j)⟩

def Machine.init (M : Machine) (input : List Bool) : Config M.stackCount M.states :=
  ⟨some M.initial, fun j => if j = M.inputStack then input else []⟩

def Machine.run (M : Machine) : Config M.stackCount M.states → List Bool →
    Config M.stackCount M.states
  | c, [] => c
  | c, b :: bs => M.run (M.step c b) bs

def Machine.output (M : Machine) (input bits : List Bool) : List Bool :=
  (M.run (M.init input) bits).«stacks» M.outputStack

def Machine.runSeed (M : Machine) (input : List Bool) {fuel : ℕ} (seed : FairSeed fuel) :
    Config M.stackCount M.states := M.run (M.init input) (List.ofFn seed)

def Machine.HaltsWithin (M : Machine) (input : List Bool) (fuel : ℕ) : Prop :=
  ∀ seed : FairSeed fuel, (M.runSeed input seed).state = none

noncomputable def Machine.successCount (M : Machine) (input : List Bool) (fuel : ℕ)
    (good : List Bool → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun seed : FairSeed fuel =>
    good (M.output input (List.ofFn seed))).card

def Machine.SucceedsTwoThirds (M : Machine) (input : List Bool) (fuel : ℕ)
    (good : List Bool → Prop) : Prop :=
  2 * 2 ^ fuel ≤ 3 * M.successCount input fuel good

def Machine.PolynomialTime (M : Machine) : Prop :=
  ∃ coefficient degree : ℕ, ∀ input : List Bool,
    M.HaltsWithin input (polynomialFuel coefficient degree input.length)

def RandomizedPolynomialSpec (valid : List Bool → Prop)
    (good : List Bool → List Bool → Prop) : Prop :=
  ∃ M : Machine, ∃ coefficient degree : ℕ, ∀ input : List Bool, valid input →
    M.HaltsWithin input (polynomialFuel coefficient degree input.length) ∧
    M.SucceedsTwoThirds input (polynomialFuel coefficient degree input.length) (good input)

@[simp] theorem Machine.step_halted (M : Machine) (c : Config M.stackCount M.states)
    (h : c.state = none) (b : Bool) : M.step c b = c := by simp [Machine.step, h]

theorem Machine.run_halted (M : Machine) (c : Config M.stackCount M.states)
    (h : c.state = none) (bits : List Bool) : M.run c bits = c := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simpa [Machine.run, M.step_halted c h b] using ih

theorem Machine.run_append (M : Machine) (c : Config M.stackCount M.states)
    (xs ys : List Bool) : M.run c (xs ++ ys) = M.run (M.run c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons b bs ih => simpa [Machine.run] using ih (M.step c b)

theorem Machine.step_stack_length_le (M : Machine) (c : Config M.stackCount M.states)
    (b : Bool) (j : Fin M.stackCount) :
    ((M.step c b).«stacks» j).length ≤ (c.«stacks» j).length + 1 := by
  unfold Machine.step
  cases hs : c.state with
  | none => simp
  | some s => exact StackAction.length_apply_le _ _

theorem Machine.run_stack_length_le (M : Machine) (c : Config M.stackCount M.states)
    (bits : List Bool) (j : Fin M.stackCount) :
    ((M.run c bits).«stacks» j).length ≤ (c.«stacks» j).length + bits.length := by
  induction bits generalizing c with
  | nil => simp [Machine.run]
  | cons b bs ih =>
      have hstep := M.step_stack_length_le c b j
      have hrun := ih (M.step c b)
      simp only [Machine.run, List.length_cons]
      omega

def decodeDispatch {k q : ℕ}
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q)
    (index : Fin (q * (3 ^ k * 2))) : Instruction k q :=
  let stateHeads : Fin q × Fin (3 ^ k * 2) := finProdFinEquiv.symm index
  let headsBit : Fin (3 ^ k) × Fin 2 := finProdFinEquiv.symm stateHeads.2
  dispatch stateHeads.1 (decodeHeads k headsBit.1.val) (headsBit.2.val == 1)

def compile {k q : ℕ} (initial : Fin q) (input output : Fin k)
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q) : Machine :=
  ⟨k, q, initial, input, output, List.ofFn (decodeDispatch dispatch)⟩

theorem compile_table_length {k q : ℕ} (initial : Fin q) (input output : Fin k)
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q) :
    (compile initial input output dispatch).table.length = q * (3 ^ k * 2) := by
  simp [compile]

theorem decodeDispatch_tableIndex {k q : ℕ}
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q)
    (s : Fin q) (h : Fin k → Fin 3) (b : Bool) :
    decodeDispatch dispatch (tableIndex s h b) = dispatch s h b := by
  simp only [decodeDispatch, tableIndex, Equiv.symm_apply_apply, headFin,
    decodeHeads_headsCode]
  cases b <;> rfl

theorem lookup_compile {k q : ℕ} (initial : Fin q) (input output : Fin k)
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q)
    (s : Fin q) (h : Fin k → Fin 3) (b : Bool) :
    (compile initial input output dispatch).table.getD (tableIndex s h b).val
      (Instruction.halt k q) = dispatch s h b := by
  change (List.ofFn (decodeDispatch dispatch)).getD _ _ = _
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn]
  exact decodeDispatch_tableIndex dispatch s h b

theorem step_compile {k q : ℕ} (initial : Fin q) (input output : Fin k)
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → Instruction k q)
    (s : Fin q) («stacks» : Fin k → List Bool) (b : Bool) :
    (compile initial input output dispatch).step ⟨some s, «stacks»⟩ b =
      let c : Config k q := ⟨some s, «stacks»⟩
      let i := dispatch s (observedHeads c) b
      Config.mk i.next (fun j => (i.action j).apply («stacks» j)) := by
  simp only [Machine.step]
  erw [lookup_compile]
  rfl

def liftInstruction {k q : ℕ} (ports : Fin 3 ↪ Fin k)
    (i : KS.W29.Instruction q) : Instruction k q :=
  ⟨i.next, Vector.ofFn (fun j =>
    if j = ports 0 then i.first else if j = ports 1 then i.second
    else if j = ports 2 then i.third else .stay)⟩

@[simp] theorem liftInstruction_on_port {k q : ℕ} (ports : Fin 3 ↪ Fin k)
    (i : KS.W29.Instruction q) (j : Fin 3) :
    (liftInstruction ports i).action (ports j) = i.action j := by
  fin_cases j <;> simp [Instruction.action, liftInstruction, KS.W29.Instruction.action,
    ports.injective.eq_iff]

@[simp] theorem liftInstruction_off_port {k q : ℕ} (ports : Fin 3 ↪ Fin k)
    (i : KS.W29.Instruction q) (j : Fin k) (hj : ∀ r : Fin 3, j ≠ ports r) :
    (liftInstruction ports i).action j = .stay := by
  simp [Instruction.action, liftInstruction, hj]

def project {k q : ℕ} (ports : Fin 3 ↪ Fin k) (c : Config k q) : KS.W29.Config q :=
  ⟨c.state, fun j => c.«stacks» (ports j)⟩

def selectedCode {k : ℕ} (ports : Fin 3 ↪ Fin k) (h : Fin k → Fin 3) : ℕ :=
  (h (ports 0)).val + 3 * (h (ports 1)).val + 9 * (h (ports 2)).val

def liftDispatch {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (s : Fin M.states) (h : Fin k → Fin 3) (b : Bool) : Instruction k M.states :=
  liftInstruction ports (M.table.getD
    (54 * s.val + 2 * selectedCode ports h + KS.W29.bitCode b)
    (KS.W29.Instruction.halt M.states))

def lift3 {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k) : Machine :=
  compile M.initial (ports 0) (ports 1) (liftDispatch M ports)

theorem lift3_step {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (s : Fin M.states) («stacks» : Fin k → List Bool) (b : Bool) :
    (lift3 M ports).step ⟨some s, «stacks»⟩ b =
      let c : Config k M.states := ⟨some s, «stacks»⟩
      let i := M.table.getD (KS.W29.transitionIndex s (project ports c) b)
        (KS.W29.Instruction.halt M.states)
      Config.mk i.next (fun j => ((liftInstruction ports i).action j).apply («stacks» j)) := by
  unfold lift3
  rw [step_compile]
  rfl

theorem lift3_project_step {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : Config k M.states) (b : Bool) :
    project ports ((lift3 M ports).step c b) = M.step (project ports c) b := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      erw [lift3_step M ports s «stacks» b]
      change KS.W29.Config.mk _ _ = KS.W29.Config.mk _ _
      congr 1
      funext j
      dsimp only [project]
      rw [liftInstruction_on_port ports _ j]

theorem lift3_step_preserves_other {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (c : Config k M.states) (b : Bool)
    (j : Fin k) (hj : ∀ r : Fin 3, j ≠ ports r) :
    ((lift3 M ports).step c b).«stacks» j = c.«stacks» j := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      erw [lift3_step M ports s «stacks» b]
      change ((liftInstruction ports _).action j).apply («stacks» j) = «stacks» j
      rw [liftInstruction_off_port ports _ j hj]
      rfl

theorem lift3_project_run {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : Config k M.states) (bits : List Bool) :
    project ports ((lift3 M ports).run c bits) = M.run (project ports c) bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [Machine.run.eq_def, ih]
      erw [lift3_project_step M ports c b]
      rfl

theorem lift3_run_preserves_other {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (c : Config k M.states) (bits : List Bool)
    (j : Fin k) (hj : ∀ r : Fin 3, j ≠ ports r) :
    ((lift3 M ports).run c bits).«stacks» j = c.«stacks» j := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [Machine.run.eq_def, ih]
      exact lift3_step_preserves_other M ports c b j hj

@[simp] theorem lift3_project_init {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (input : List Bool) :
    project ports ((lift3 M ports).init input) = M.init input := by
  change KS.W29.Config.mk (some M.initial)
      (fun j => if ports j = ports 0 then input else []) =
    KS.W29.Config.mk (some M.initial) (fun j => if j = 0 then input else [])
  congr 1
  funext j
  simp [ports.injective.eq_iff]

@[simp] theorem lift3_output_eq {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (input bits : List Bool) :
    (lift3 M ports).output input bits = M.output input bits := by
  change (project ports ((lift3 M ports).run ((lift3 M ports).init input) bits)).«stacks» 1 = _
  erw [lift3_project_run, lift3_project_init M ports input]
  rfl

@[simp] theorem lift3_runSeed_state {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (input : List Bool) {fuel : ℕ} (seed : FairSeed fuel) :
    ((lift3 M ports).runSeed input seed).state = (M.runSeed input seed).state := by
  change (project ports ((lift3 M ports).run ((lift3 M ports).init input)
    (List.ofFn seed))).state = _
  erw [lift3_project_run, lift3_project_init M ports input]
  rfl

@[simp] theorem lift3_haltsWithin_iff {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (input : List Bool) (fuel : ℕ) :
    (lift3 M ports).HaltsWithin input fuel ↔ M.HaltsWithin input fuel := by
  unfold Machine.HaltsWithin KS.W29.BinaryMachine.HaltsWithin
  constructor <;> intro h seed
  · rw [← lift3_runSeed_state M ports input seed]
    exact h seed
  · rw [lift3_runSeed_state M ports input seed]
    exact h seed

@[simp] theorem lift3_successCount_eq {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (input : List Bool) (fuel : ℕ) (good : List Bool → Prop) :
    (lift3 M ports).successCount input fuel good = M.successCount input fuel good := by
  classical
  unfold Machine.successCount KS.W29.BinaryMachine.successCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro seed _
  change good ((lift3 M ports).output input (List.ofFn seed)) ↔
    good (M.output input (List.ofFn seed))
  rw [lift3_output_eq M ports input (List.ofFn seed)]

@[simp] theorem lift3_succeedsTwoThirds_iff {k : ℕ} (M : KS.W29.BinaryMachine)
    (ports : Fin 3 ↪ Fin k) (input : List Bool) (fuel : ℕ) (good : List Bool → Prop) :
    (lift3 M ports).SucceedsTwoThirds input fuel good ↔
      M.SucceedsTwoThirds input fuel good := by
  unfold Machine.SucceedsTwoThirds KS.W29.BinaryMachine.SucceedsTwoThirds
  rw [lift3_successCount_eq M ports input fuel good]

def embed3 (M : KS.W29.BinaryMachine) : Machine := lift3 M (Function.Embedding.refl (Fin 3))

def ofThree {q : ℕ} (c : KS.W29.Config q) : Config 3 q := ⟨c.state, c.«stacks»⟩

@[simp] theorem project_ofThree {q : ℕ} (c : KS.W29.Config q) :
    project (Function.Embedding.refl (Fin 3)) (ofThree c) = c := by cases c; rfl

@[simp] theorem ofThree_project {q : ℕ} (c : Config 3 q) :
    ofThree (project (Function.Embedding.refl (Fin 3)) c) = c := by cases c; rfl

theorem embed3_run (M : KS.W29.BinaryMachine) (c : KS.W29.Config M.states)
    (bits : List Bool) :
    (embed3 M).run (ofThree c) bits = ofThree (M.run c bits) := by
  have h := lift3_project_run M (Function.Embedding.refl (Fin 3)) (ofThree c) bits
  change (lift3 M (Function.Embedding.refl (Fin 3))).run (ofThree c) bits = _
  exact (ofThree_project _).symm.trans (congrArg ofThree h)

@[simp] theorem embed3_output_eq (M : KS.W29.BinaryMachine) (input bits : List Bool) :
    (embed3 M).output input bits = M.output input bits := lift3_output_eq M _ input bits

@[simp] theorem embed3_haltsWithin_iff (M : KS.W29.BinaryMachine) (input : List Bool) (fuel : ℕ) :
    (embed3 M).HaltsWithin input fuel ↔ M.HaltsWithin input fuel :=
  lift3_haltsWithin_iff M _ input fuel

end KS.W01.FixedStack

end

end OAI
