import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TM0RapidPresentation
import OAI.Analysis.PeriodicLattice.Basic

namespace OAI

/-! The bounded rapid-machine presentation embeds into a ragged lattice
table by turning absent instructions into explicit transfers to a final
empty row. Thus its terminal-state test is exactly the lattice stop test. -/

namespace ForcedComputation.FiniteMachine

def latticeAction (M : RapidForcing.Machine) (r : Fin M.states) (a : Fin M.symbols) :
    PeriodicLattice.Instruction :=
  match M.transition r a with
  | none => ⟨M.states, a.val, 1⟩
  | some (s, b, d) => ⟨s.val, b.val, d⟩

def latticeMachine (M : RapidForcing.Machine) : PeriodicLattice.Machine where
  states := M.states + 1
  symbols := M.symbols
  start := M.initial.val
  table := List.ofFn fun r : Fin (M.states + 1) =>
    if h : r.val < M.states then
      List.ofFn fun a : Fin M.symbols => some (latticeAction M ⟨r.val, h⟩ a)
    else []

theorem latticeAction_bounds (M : RapidForcing.Machine) (r : Fin M.states)
    (a : Fin M.symbols) :
    (latticeAction M r a).nextState < M.states + 1 ∧
      (latticeAction M r a).writeSymbol < M.symbols := by
  cases hm : M.transition r a with
  | none =>
    simpa only [latticeAction, hm] using And.intro (Nat.lt_succ_self M.states) a.isLt
  | some v =>
    rcases v with ⟨s, b, d⟩
    simpa only [latticeAction, hm] using And.intro (Nat.lt_succ_of_lt s.isLt) b.isLt

theorem latticeMachine_lookup (M : RapidForcing.Machine)
    (r : Fin M.states) (a : Fin M.symbols) :
    (latticeMachine M).lookup r.val a.val = some (latticeAction M r a) := by
  change ((List.ofFn fun s : Fin (M.states + 1) =>
    if h : s.val < M.states then
      List.ofFn fun b : Fin M.symbols => some (latticeAction M ⟨s.val, h⟩ b)
    else []).getD r.val []).getD a.val none = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    Nat.lt_succ_of_lt r.isLt, r.isLt, a.isLt, ↓reduceDIte, Option.getD_some]

theorem latticeMachine_terminal (M : RapidForcing.Machine) (a : ℕ) :
    (latticeMachine M).lookup M.states a = none := by
  change ((List.ofFn fun s : Fin (M.states + 1) =>
    if h : s.val < M.states then
      List.ofFn fun b : Fin M.symbols => some (latticeAction M ⟨s.val, h⟩ b)
    else []).getD M.states []).getD a none = none
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    Nat.lt_succ_self, ↓reduceDIte, lt_self_iff_false, Option.getD_some,
    List.getElem?_nil, Option.getD_none]

theorem latticeMachine_wellFormed (M : RapidForcing.Machine) :
    (latticeMachine M).WellFormed := by
  refine ⟨Nat.succ_pos _, M.symbols_pos, Nat.lt_succ_of_lt M.initial.isLt,
    le_of_eq List.length_ofFn, ?_, ?_⟩
  · intro row hr
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hr
    split
    · exact le_of_eq List.length_ofFn
    · exact Nat.zero_le _
  · intro row hr entry he I hI
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hr
    split at he
    · obtain ⟨a, ha⟩ := List.mem_ofFn.mp he
      have hi : latticeAction M _ a = I := Option.some.inj (ha.trans hI)
      rw [← hi]
      exact latticeAction_bounds M _ a
    · simp only [List.not_mem_nil] at he

def eraseLattice {M : RapidForcing.Machine} (c : M.Config) :
    PeriodicLattice.Configuration :=
  ⟨c.state.val, c.head, fun j => (c.tape j).val⟩

theorem eraseLattice_step (M : RapidForcing.Machine) (c : M.Config) :
    eraseLattice (M.nextConfig c) =
      PeriodicLattice.machineStep (latticeMachine M) (eraseLattice c) := by
  by_cases hr : c.state.val < M.states
  · have hi := latticeMachine_lookup M ⟨c.state.val, hr⟩ (c.tape c.head)
    cases hm : M.transition ⟨c.state.val, hr⟩ (c.tape c.head) with
    | none =>
      simp only [RapidForcing.Machine.nextConfig, hr, ↓reduceDIte, hm,
        PeriodicLattice.machineStep, eraseLattice, hi, latticeAction, Fin.val_one,
        Nat.cast_one, sub_self, add_zero]
      congr 1
      funext j
      by_cases hj : j = c.head
      · subst j
        simp only [Function.update_self]
      · exact (Function.update_of_ne hj (c.tape c.head).val (fun j => (c.tape j).val)).symm
    | some v =>
      rcases v with ⟨s, b, d⟩
      simp only [RapidForcing.Machine.nextConfig, hr, ↓reduceDIte, hm,
        PeriodicLattice.machineStep, eraseLattice, hi, latticeAction, add_sub_assoc]
      congr 1
      funext j
      exact Function.apply_update (fun _ (a : Fin M.symbols) => a.val) c.tape c.head b j
  · have hs : c.state.val = M.states := by have := c.state.isLt; omega
    have hn : M.nextConfig c = c := by
      simp only [RapidForcing.Machine.nextConfig, hr, ↓reduceDIte]
    rw [hn]
    simp only [PeriodicLattice.machineStep, eraseLattice, hs, latticeMachine_terminal]

theorem eraseLattice_initial (M : RapidForcing.Machine) (w : M.Input) :
    eraseLattice (M.initialConfig w) =
      PeriodicLattice.initialConfiguration ⟨latticeMachine M, w.map Fin.val⟩ := by
  unfold eraseLattice RapidForcing.Machine.initialConfig PeriodicLattice.initialConfiguration
  congr 1
  funext j
  by_cases hj : 0 ≤ j
  · simp only [hj, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_map]
    exact (Option.getD_map Fin.val M.blank _).symm
  · simp [hj, RapidForcing.Machine.blank]

theorem eraseLattice_run (M : RapidForcing.Machine) (w : M.Input) (n : ℕ) :
    eraseLattice (M.run w n) =
      PeriodicLattice.execution ⟨latticeMachine M, w.map Fin.val⟩ n := by
  induction n with
  | zero => exact eraseLattice_initial M w
  | succ n ih =>
    have he := (eraseLattice_step M _).trans
      (congrArg (PeriodicLattice.machineStep (latticeMachine M)) ih)
    simpa only [RapidForcing.Machine.run, PeriodicLattice.execution,
      Function.iterate_succ_apply'] using he

theorem latticeMachine_halts_iff (M : RapidForcing.Machine) (w : M.Input) :
    PeriodicLattice.Halts ⟨latticeMachine M, w.map Fin.val⟩ ↔ M.Halts w := by
  change (∃ n, (latticeMachine M).lookup
    (PeriodicLattice.execution ⟨latticeMachine M, w.map Fin.val⟩ n).state
    ((PeriodicLattice.execution ⟨latticeMachine M, w.map Fin.val⟩ n).tape
      (PeriodicLattice.execution ⟨latticeMachine M, w.map Fin.val⟩ n).head) = none) ↔
    ∃ n, (M.run w n).state.val = M.states
  apply exists_congr
  intro n
  rw [← eraseLattice_run M w n]
  change (latticeMachine M).lookup (M.run w n).state.val
    ((M.run w n).tape (M.run w n).head).val = none ↔ (M.run w n).state.val = M.states
  by_cases hr : (M.run w n).state.val < M.states
  · have hi := latticeMachine_lookup M ⟨(M.run w n).state.val, hr⟩
      ((M.run w n).tape (M.run w n).head)
    change _ = none ↔ _
    rw [hi]
    simp only [reduceCtorEq, false_iff]
    exact ne_of_lt hr
  · have hs : (M.run w n).state.val = M.states := by
      have := (M.run w n).state.isLt
      omega
    change (latticeMachine M).lookup (M.run w n).state.val _ = none ↔ _
    simp only [hs, latticeMachine_terminal]

end ForcedComputation.FiniteMachine

end OAI
