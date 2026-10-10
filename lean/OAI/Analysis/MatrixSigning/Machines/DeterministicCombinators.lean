import Mathlib
import OAI.Analysis.MatrixSigning.Machines.Sequential
import OAI.Analysis.MatrixSigning.Machines.FixedLoop
import OAI.Analysis.MatrixSigning.Machines.FixedBranch
import OAI.Analysis.MatrixSigning.Machines.FixedStackPortLift
import OAI.Analysis.MatrixSigning.Machines.EntryPoint
import OAI.Analysis.MatrixSigning.Machines.Deterministic

namespace OAI

section

namespace KS.W29.Deterministic
open KS.W29.FixedSequential (Program)
open KS.W01.FixedStack (Config)

theorem coinIndependent_loop {k : Nat} (P : Program k)
    (guard : (Fin k → Fin 3) → Bool → KS.W29.FixedLoop.GuardInstruction k)
    (hP : CoinIndependent P) (hguard : ∀ heads a b, guard heads a = guard heads b) :
    CoinIndependent (KS.W29.FixedLoop.loop P guard) := by
  intro c a b
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      by_cases hs : s.val = 0
      · have he : s = KS.W29.FixedLoop.guardState P := Fin.ext hs
        erw [he, KS.W29.FixedLoop.step_guard, KS.W29.FixedLoop.step_guard]
        dsimp only
        erw [hguard _ a b]
      · have hbound : s.val < P.states + 1 := s.isLt
        let t : Fin P.states := ⟨s.val - 1, by omega⟩
        have he : s = KS.W29.FixedLoop.bodyState P t := by
          apply Fin.ext
          dsimp [KS.W29.FixedLoop.bodyState, t]
          omega
        erw [he, KS.W29.FixedLoop.step_body, KS.W29.FixedLoop.step_body, hP _ a b]

theorem coinIndependent_branch {k : Nat} (P Q : Program k) (output : Fin k)
    (select : (Fin k → Fin 3) → Bool → KS.W29.FixedBranch.SelectInstruction k)
    (hP : CoinIndependent P) (hQ : CoinIndependent Q)
    (hselect : ∀ heads a b, select heads a = select heads b) :
    CoinIndependent (KS.W29.FixedBranch.branch P Q output select) := by
  intro c a b
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      by_cases hs : s.val = 0
      · have he : s = KS.W29.FixedBranch.start P Q := Fin.ext hs
        erw [he, KS.W29.FixedBranch.step_start, KS.W29.FixedBranch.step_start]
        dsimp only
        erw [hselect _ a b]
      · by_cases hl : s.val < P.states + 1
        · let t : Fin P.states := ⟨s.val - 1, by omega⟩
          have he : s = KS.W29.FixedBranch.leftState P Q t := by
            apply Fin.ext
            dsimp [KS.W29.FixedBranch.leftState, t]
            omega
          erw [he, KS.W29.FixedBranch.step_left, KS.W29.FixedBranch.step_left, hP _ a b]
        · have hbound : s.val < P.states + Q.states + 1 := s.isLt
          let t : Fin Q.states := ⟨s.val - (P.states + 1), by omega⟩
          have he : s = KS.W29.FixedBranch.rightState P Q t := by
            apply Fin.ext
            dsimp [KS.W29.FixedBranch.rightState, t]
            omega
          erw [he, KS.W29.FixedBranch.step_right, KS.W29.FixedBranch.step_right, hQ _ a b]

theorem coinIndependent_liftPorts {k K : Nat} (P : Program k) (ports : Fin k ↪ Fin K)
    (hP : CoinIndependent P) : CoinIndependent (KS.W29.FixedSequential.liftPorts P ports) := by
  intro c a b
  change (KS.W01.FixedStack.liftPorts P.toMachine ports).step c a =
    (KS.W01.FixedStack.liftPorts P.toMachine ports).step c b
  have hp : KS.W01.FixedStack.projectPorts ports
      ((KS.W01.FixedStack.liftPorts P.toMachine ports).step c a) =
      KS.W01.FixedStack.projectPorts ports
      ((KS.W01.FixedStack.liftPorts P.toMachine ports).step c b) := by
    erw [KS.W01.FixedStack.liftPorts_project_step, KS.W01.FixedStack.liftPorts_project_step, hP _ a b]
  have hstate := congrArg (fun d : KS.W01.FixedStack.Config k P.states => d.state) hp
  have hstacks : ((KS.W01.FixedStack.liftPorts P.toMachine ports).step c a).«stacks» =
      ((KS.W01.FixedStack.liftPorts P.toMachine ports).step c b).«stacks» := by
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun d : KS.W01.FixedStack.Config k P.states => d.«stacks» i) hp
    · have hn : ∀ i, j ≠ ports i := by simpa only [not_exists] using hj
      erw [KS.W01.FixedStack.liftPorts_step_preserves_other _ _ _ _ _ hn,
        KS.W01.FixedStack.liftPorts_step_preserves_other _ _ _ _ _ hn]
  exact congrArg₂ KS.W01.FixedStack.Config.mk hstate hstacks

theorem coinIndependent_compile3 {q : Nat} (initial : Fin q)
    (dispatch : Fin q → Fin 27 → Bool → KS.W29.Instruction q)
    (h : ∀ s heads a b, dispatch s heads a = dispatch s heads b) :
    ∀ (c : KS.W29.Config q) (a b : Bool),
      (KS.W29.FiniteDispatch.compile initial dispatch).step c a =
      (KS.W29.FiniteDispatch.compile initial dispatch).step c b := by
  intro c a b
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some state =>
      erw [KS.W29.FiniteDispatch.step_compile, KS.W29.FiniteDispatch.step_compile]
      dsimp only
      erw [h state _ a b]

theorem coinIndependent_lift3 {K : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin K)
    (hM : ∀ (c : KS.W29.Config M.states) (a b : Bool), M.step c a = M.step c b) :
    CoinIndependent (KS.W29.FixedSequential.ofMachine (KS.W01.FixedStack.lift3 M ports)) := by
  intro c a b
  change (KS.W01.FixedStack.lift3 M ports).step c a = (KS.W01.FixedStack.lift3 M ports).step c b
  have hp : KS.W01.FixedStack.project ports ((KS.W01.FixedStack.lift3 M ports).step c a) =
      KS.W01.FixedStack.project ports ((KS.W01.FixedStack.lift3 M ports).step c b) := by
    erw [KS.W01.FixedStack.lift3_project_step, KS.W01.FixedStack.lift3_project_step, hM _ a b]
  have hstate := congrArg (fun d : KS.W29.Config M.states => d.state) hp
  have hstacks : ((KS.W01.FixedStack.lift3 M ports).step c a).«stacks» =
      ((KS.W01.FixedStack.lift3 M ports).step c b).«stacks» := by
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» i) hp
    · have hn : ∀ i, j ≠ ports i := by simpa only [not_exists] using hj
      have ha : ((KS.W01.FixedStack.lift3 M ports).step c a).«stacks» j = c.«stacks» j := by
        simpa only [KS.W01.FixedStack.Machine.run] using
          KS.W01.FixedStack.lift3_run_preserves_other M ports c [a] j hn
      have hb : ((KS.W01.FixedStack.lift3 M ports).step c b).«stacks» j = c.«stacks» j := by
        simpa only [KS.W01.FixedStack.Machine.run] using
          KS.W01.FixedStack.lift3_run_preserves_other M ports c [b] j hn
      exact ha.trans hb.symm
  exact congrArg₂ KS.W01.FixedStack.Config.mk hstate hstacks

theorem coinIndependent_compose3 (P Q : KS.W29.BinaryMachine)
    (hP : ∀ (c : KS.W29.Config P.states) (a b : Bool), P.step c a = P.step c b)
    (hQ : ∀ (c : KS.W29.Config Q.states) (a b : Bool), Q.step c a = Q.step c b) :
    ∀ (c : KS.W29.Config (KS.W29.Sequential.compose P Q).states) (a b : Bool),
      (KS.W29.Sequential.compose P Q).step c a = (KS.W29.Sequential.compose P Q).step c b := by
  intro c a b
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      by_cases hs : s.val < P.states
      · let t : Fin P.states := ⟨s.val, hs⟩
        have he : s = KS.W29.Sequential.leftState P Q t := Fin.ext rfl
        erw [he, KS.W29.Sequential.step_left, KS.W29.Sequential.step_left, hP _ a b]
      · have hbound : s.val < P.states + Q.states := s.isLt
        let t : Fin Q.states := ⟨s.val - P.states, by omega⟩
        have he : s = KS.W29.Sequential.rightState P Q t := by
          apply Fin.ext
          dsimp [KS.W29.Sequential.rightState, t]
          omega
        erw [he, KS.W29.Sequential.step_right, KS.W29.Sequential.step_right, hQ _ a b]

theorem coinIndependent_withEntry3 (P : KS.W29.BinaryMachine) (entry : Fin P.states)
    (hP : ∀ (c : KS.W29.Config P.states) (a b : Bool), P.step c a = P.step c b) :
    ∀ (c : KS.W29.Config P.states) (a b : Bool),
      (P.withEntry entry).step c a = (P.withEntry entry).step c b := by
  intro c a b
  exact (KS.W29.BinaryMachine.withEntry_step P entry c a).trans
    ((hP c a b).trans (KS.W29.BinaryMachine.withEntry_step P entry c b).symm)

end KS.W29.Deterministic

end

end OAI
