import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedSequential

namespace OAI

section

namespace KS.W01.FixedStack

def portPreimage {k K : ℕ} (ports : Fin k ↪ Fin K) (j : Fin K) : Option (Fin k) :=
  (List.ofFn (fun i : Fin k => i)).find? (fun i => ports i == j)

@[simp] theorem portPreimage_on_port {k K : ℕ} (ports : Fin k ↪ Fin K) (i : Fin k) :
    portPreimage ports (ports i) = some i := by
  cases he : portPreimage ports (ports i) with
  | none =>
      unfold portPreimage at he
      have hn := List.find?_eq_none.mp he
      have hi : i ∈ List.ofFn (fun i : Fin k => i) := by simp
      have hf := hn i hi
      simp at hf
  | some r =>
      unfold portPreimage at he
      have hr := List.find?_some he
      have hri : ports r = ports i := by simpa using hr
      have h : r = i := ports.injective hri
      subst r
      rfl

@[simp] theorem portPreimage_off_port {k K : ℕ} (ports : Fin k ↪ Fin K) (j : Fin K)
    (hj : ∀ i : Fin k, j ≠ ports i) : portPreimage ports j = none := by
  unfold portPreimage
  apply List.find?_eq_none.mpr
  intro i _
  simpa using (Ne.symm (hj i))

def liftPortsInstruction {k K q : ℕ} (ports : Fin k ↪ Fin K)
    (i : Instruction k q) : Instruction K q :=
  ⟨i.next, Vector.ofFn (fun j => match portPreimage ports j with
    | none => .stay
    | some r => i.action r)⟩

@[simp] theorem liftPortsInstruction_on_port {k K q : ℕ} (ports : Fin k ↪ Fin K)
    (i : Instruction k q) (r : Fin k) :
    (liftPortsInstruction ports i).action (ports r) = i.action r := by
  simp [Instruction.action, liftPortsInstruction]

@[simp] theorem liftPortsInstruction_off_port {k K q : ℕ} (ports : Fin k ↪ Fin K)
    (i : Instruction k q) (j : Fin K) (hj : ∀ r : Fin k, j ≠ ports r) :
    (liftPortsInstruction ports i).action j = .stay := by
  simp [Instruction.action, liftPortsInstruction, portPreimage_off_port ports j hj]

def projectPorts {k K q : ℕ} (ports : Fin k ↪ Fin K) (c : Config K q) : Config k q :=
  ⟨c.state, fun j => c.«stacks» (ports j)⟩

def liftPortsDispatch {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (s : Fin M.states) (heads : Fin K → Fin 3) (b : Bool) : Instruction K M.states :=
  liftPortsInstruction ports (M.table.getD (tableIndex s (fun j => heads (ports j)) b).val
    (Instruction.halt M.stackCount M.states))

def liftPorts {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K) : Machine :=
  compile M.initial (ports M.inputStack) (ports M.outputStack) (liftPortsDispatch M ports)

theorem liftPorts_step {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (s : Fin M.states) («stacks» : Fin K → List Bool) (b : Bool) :
    (liftPorts M ports).step ⟨some s, «stacks»⟩ b =
      let c : Config K M.states := ⟨some s, «stacks»⟩
      let i := M.table.getD (tableIndex s (observedHeads (projectPorts ports c)) b).val
        (Instruction.halt M.stackCount M.states)
      Config.mk i.next (fun j => ((liftPortsInstruction ports i).action j).apply («stacks» j)) := by
  unfold liftPorts
  erw [step_compile]
  rfl

theorem liftPorts_project_step {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (c : Config K M.states) (b : Bool) :
    projectPorts ports ((liftPorts M ports).step c b) = M.step (projectPorts ports c) b := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      erw [liftPorts_step M ports s «stacks» b]
      change Config.mk _ _ = Config.mk _ _
      congr 1
      funext j
      dsimp only [projectPorts]
      rw [liftPortsInstruction_on_port ports _ j]

theorem liftPorts_step_preserves_other {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (c : Config K M.states) (b : Bool)
    (j : Fin K) (hj : ∀ r : Fin M.stackCount, j ≠ ports r) :
    ((liftPorts M ports).step c b).«stacks» j = c.«stacks» j := by
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      erw [liftPorts_step M ports s «stacks» b]
      change ((liftPortsInstruction ports _).action j).apply («stacks» j) = «stacks» j
      rw [liftPortsInstruction_off_port ports _ j hj]
      rfl

theorem liftPorts_project_run {K : ℕ} (M : Machine) (ports : Fin M.stackCount ↪ Fin K)
    (c : Config K M.states) (bits : List Bool) :
    projectPorts ports ((liftPorts M ports).run c bits) = M.run (projectPorts ports c) bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [Machine.run.eq_def, ih]
      erw [liftPorts_project_step M ports c b]
      rfl

theorem liftPorts_run_preserves_other {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (c : Config K M.states) (bits : List Bool)
    (j : Fin K) (hj : ∀ r : Fin M.stackCount, j ≠ ports r) :
    ((liftPorts M ports).run c bits).«stacks» j = c.«stacks» j := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      erw [Machine.run.eq_def, ih]
      exact liftPorts_step_preserves_other M ports c b j hj

@[simp] theorem liftPorts_project_init {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (input : List Bool) :
    projectPorts ports ((liftPorts M ports).init input) = M.init input := by
  change Config.mk (some M.initial)
      (fun j => if ports j = ports M.inputStack then input else []) =
    Config.mk (some M.initial) (fun j => if j = M.inputStack then input else [])
  congr 1
  funext j
  simp [ports.injective.eq_iff]

@[simp] theorem liftPorts_output_eq {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (input bits : List Bool) :
    (liftPorts M ports).output input bits = M.output input bits := by
  change (projectPorts ports ((liftPorts M ports).run ((liftPorts M ports).init input)
    bits)).«stacks» M.outputStack = _
  erw [liftPorts_project_run, liftPorts_project_init M ports input]
  rfl

@[simp] theorem liftPorts_runSeed_state {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (input : List Bool) {fuel : ℕ}
    (seed : KS.W29.FairSeed fuel) :
    ((liftPorts M ports).runSeed input seed).state = (M.runSeed input seed).state := by
  change (projectPorts ports ((liftPorts M ports).run ((liftPorts M ports).init input)
    (List.ofFn seed))).state = _
  erw [liftPorts_project_run, liftPorts_project_init M ports input]
  rfl

@[simp] theorem liftPorts_haltsWithin_iff {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (input : List Bool) (fuel : ℕ) :
    (liftPorts M ports).HaltsWithin input fuel ↔ M.HaltsWithin input fuel := by
  unfold Machine.HaltsWithin
  constructor <;> intro h seed
  · rw [← liftPorts_runSeed_state M ports input seed]
    exact h seed
  · rw [liftPorts_runSeed_state M ports input seed]
    exact h seed

@[simp] theorem liftPorts_successCount_eq {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (input : List Bool) (fuel : ℕ)
    (good : List Bool → Prop) :
    (liftPorts M ports).successCount input fuel good = M.successCount input fuel good := by
  classical
  unfold Machine.successCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro seed _
  rw [liftPorts_output_eq M ports input (List.ofFn seed)]

@[simp] theorem liftPorts_succeedsTwoThirds_iff {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (input : List Bool) (fuel : ℕ)
    (good : List Bool → Prop) :
    (liftPorts M ports).SucceedsTwoThirds input fuel good ↔
      M.SucceedsTwoThirds input fuel good := by
  unfold Machine.SucceedsTwoThirds
  rw [liftPorts_successCount_eq]

@[simp] theorem liftPorts_polynomialTime_iff {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) :
    (liftPorts M ports).PolynomialTime ↔ M.PolynomialTime := by
  simp only [Machine.PolynomialTime, liftPorts_haltsWithin_iff]

end KS.W01.FixedStack

namespace KS.W29.FixedSequential

def liftPorts {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K) : Program K :=
  ofMachine (KS.W01.FixedStack.liftPorts P.toMachine ports)

@[simp] theorem liftPorts_toMachine {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K) :
    (liftPorts P ports).toMachine = KS.W01.FixedStack.liftPorts P.toMachine ports :=
  toMachine_ofMachine _

@[simp] theorem liftPorts_input {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K) :
    (liftPorts P ports).input = ports P.input := rfl

@[simp] theorem liftPorts_output {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K) :
    (liftPorts P ports).output = ports P.output := rfl

theorem liftPorts_run_state {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K)
    (c : KS.W01.FixedStack.Config K P.states) (bits : List Bool) :
    ((liftPorts P ports).toMachine.run c bits).state =
      (P.toMachine.run (KS.W01.FixedStack.projectPorts ports c) bits).state := by
  change ((KS.W01.FixedStack.liftPorts P.toMachine ports).run c bits).state = _
  exact congrArg (fun d : KS.W01.FixedStack.Config k P.states => d.state)
    (KS.W01.FixedStack.liftPorts_project_run P.toMachine ports c bits)

theorem activeFor_liftPorts_iff {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K)
    (c : KS.W01.FixedStack.Config K P.states) (bits : List Bool) :
    ActiveFor (liftPorts P ports) c bits ↔
      ActiveFor P (KS.W01.FixedStack.projectPorts ports c) bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons b bs ih =>
      simp only [ActiveFor]
      have ht := ih ((KS.W01.FixedStack.liftPorts P.toMachine ports).step c b)
      erw [KS.W01.FixedStack.liftPorts_project_step P.toMachine ports c b] at ht
      exact and_congr Iff.rfl ht

theorem haltsAfter_liftPorts_iff {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K)
    (c : KS.W01.FixedStack.Config K P.states) (bits : List Bool) :
    HaltsAfter (liftPorts P ports) c bits ↔
      HaltsAfter P (KS.W01.FixedStack.projectPorts ports c) bits := by
  simp only [HaltsAfter, activeFor_liftPorts_iff, liftPorts_run_state]
  rfl

theorem haltsFromWithin_liftPorts_iff {k K : ℕ} (P : Program k) (ports : Fin k ↪ Fin K)
    (c : KS.W01.FixedStack.Config K P.states) (fuel : ℕ) :
    HaltsFromWithin (liftPorts P ports) c fuel ↔
      HaltsFromWithin P (KS.W01.FixedStack.projectPorts ports c) fuel := by
  unfold HaltsFromWithin
  constructor <;> intro h bits hlen
  · exact (liftPorts_run_state P ports c bits).symm.trans (h bits hlen)
  · exact (liftPorts_run_state P ports c bits).trans (h bits hlen)

end KS.W29.FixedSequential

end

end OAI
