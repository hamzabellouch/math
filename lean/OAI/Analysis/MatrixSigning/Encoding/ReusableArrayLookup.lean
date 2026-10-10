import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves
import OAI.Analysis.MatrixSigning.Machines.MachineRoundTrip
import OAI.Analysis.MatrixSigning.Machines.FixedCopyRestore
import OAI.Analysis.MatrixSigning.Encoding.FramedArrayPorts

namespace OAI

namespace KS.W04.ReusableArrayLookup
open KS.W01.FixedStack
open KS.W29.FixedSequential
open KS.W03.MachineCombinators

def reoutput {k : Nat} (P : Program k) (output : Fin k) : Program k :=
  { P with output := output }

theorem step_reoutput {k : Nat} (P : Program k) (output : Fin k)
    (c : Config k P.states) (coin : Bool) :
    (reoutput P output).toMachine.step c coin = P.toMachine.step c coin := by
  cases c with
  | mk state bank => cases state <;> rfl

theorem run_reoutput {k : Nat} (P : Program k) (output : Fin k)
    (c : Config k P.states) (bits : List Bool) :
    (reoutput P output).toMachine.run c bits = P.toMachine.run c bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons coin bits ih =>
      erw [Machine.run.eq_2, step_reoutput]
      exact ih _

theorem run_halted_of_length_ge (M : Machine) (c result : Config M.stackCount M.states)
    (fuel : Nat) (hresult : result.state = none)
    (hexact : ∀ bits : List Bool, bits.length = fuel → M.run c bits = result)
    (bits : List Bool) (hlen : fuel ≤ bits.length) : M.run c bits = result := by
  have ht : (bits.take fuel).length = fuel := by
    simp [List.length_take, Nat.min_eq_left hlen]
  conv_lhs => rw [← List.take_append_drop fuel bits]
  rw [Machine.run_append, hexact _ ht, Machine.run_halted M result hresult]

theorem run_compose_bounded {k : Nat} (P Q : Program k)
    (initial middle final : Fin k → List Bool) (t₁ t₂ : Nat)
    (hP : ∀ bits : List Bool, t₁ ≤ bits.length →
      P.toMachine.run ⟨some P.initial, initial⟩ bits = ⟨none, middle⟩)
    (hQ : ∀ bits : List Bool, t₂ ≤ bits.length →
      Q.toMachine.run ⟨some Q.initial, middle⟩ bits = ⟨none, final⟩)
    (bits : List Bool) (hlen : t₁ + t₂ ≤ bits.length) :
    (compose P Q).toMachine.run ⟨some (compose P Q).initial, initial⟩ bits =
      ⟨none, final⟩ := by
  have hp : RunSpec P initial middle t₁ := fun b hb => hP b hb.ge
  have hq : RunSpec Q middle final t₂ := fun b hb => hQ b hb.ge
  exact (hp.compose hq).run_of_le bits hlen

def arrayStacks (source work payload scratch index : List Bool) : Fin 5 → List Bool :=
  fun j => if j = 0 then source else if j = 1 then work else if j = 2 then payload
    else if j = 3 then scratch else index

theorem config_ext {k q : Nat} {c d : Config k q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

def copyPorts : Fin 3 ↪ Fin 5 where
  toFun j := if j = 0 then 0 else if j = 1 then 1 else 3
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def lookupPorts : Fin 4 ↪ Fin 5 := ⟨Fin.succ, Fin.succ_injective 4⟩
def copyProgram : Program 5 := KS.W01.FixedCopy.program copyPorts
def lookupProgram : Program 5 := KS.W11.FramedArray.liftedLookup lookupPorts
def cleanupProgram : Program 5 := reoutput (BinaryStackMoves.clearProgram 1) 2
def lookupAndCleanup : Program 5 := compose lookupProgram cleanupProgram

def program : Program 5 := compose copyProgram lookupAndCleanup

theorem program_states : program.states = 9 := rfl

private theorem composed_table_length {k : Nat} (P Q : Program k) :
    (compose P Q).table.length=(P.states+Q.states)*(3^k*2) :=
  compile_table_length (leftState P Q P.initial) P.input Q.output (dispatch P Q)

theorem program_table_length : program.table.length = 4374 := by
  exact composed_table_length copyProgram lookupAndCleanup

@[simp] theorem program_input : program.input = 0 := rfl
@[simp] theorem program_output : program.output = 2 := rfl

private theorem arrayStacks_copy_update (source index : List Bool) :
    Function.update (arrayStacks source [] [] [] index) (1 : Fin 5) source =
      arrayStacks source source [] [] index := by
  funext j
  fin_cases j <;> rfl

theorem run_copy (source index bits : List Bool) (hlen : 2 * source.length + 2 ≤ bits.length) :
    copyProgram.toMachine.run
      ⟨some copyProgram.initial, arrayStacks source [] [] [] index⟩ bits =
      ⟨none, arrayStacks source source [] [] index⟩ := by
  have hs : RunSpec copyProgram (arrayStacks source [] [] [] index)
      (arrayStacks source source [] [] index) (2*source.length+2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine copyPorts)
    intro b hb
    have h := KS.W01.FixedCopy.run_copy_restore copyPorts
      (arrayStacks source [] [] [] index) source b rfl rfl rfl hb
    exact h.trans (congrArg (Config.mk (none : Option (Fin 2)))
      (arrayStacks_copy_update source index))
  exact hs.run_of_le bits hlen

theorem run_lookup (xs : List (List Bool)) (i : Nat) (hi : i < xs.length)
    (tail bits : List Bool)
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length + i + 1 ≤ bits.length) :
    lookupProgram.toMachine.run
      ⟨some lookupProgram.initial,
        arrayStacks (xs.flatMap KS.W01.frame ++ tail) (xs.flatMap KS.W01.frame ++ tail)
          [] [] (List.replicate i true)⟩ bits =
      ⟨none, arrayStacks (xs.flatMap KS.W01.frame ++ tail)
        ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) xs[i] [] []⟩ := by
  let c : Config 5 KS.W11.FramedArray.lookupProgram.states :=
    ⟨some lookupProgram.initial,
      arrayStacks (xs.flatMap KS.W01.frame ++ tail) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true)⟩
  have hc : projectPorts lookupPorts c = KS.W11.FramedArray.config
      (some KS.W11.FramedArray.lookupProgram.initial) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true) := by
    refine config_ext ?_ ?_
    · rfl
    intro j
    fin_cases j <;> rfl
  have h := KS.W11.FramedArray.run_lookup_ports lookupPorts xs i hi tail bits c hc hlen
  refine config_ext h.1 ?_
  intro j
  fin_cases j
  · have ho := h.2.2.2.2.2 (0 : Fin 5) (by intro r; fin_cases r <;> decide)
    exact ho
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

theorem run_cleanup (source work payload bits : List Bool) (hlen : work.length + 1 ≤ bits.length) :
    cleanupProgram.toMachine.run
      ⟨some cleanupProgram.initial, arrayStacks source work payload [] []⟩ bits =
      ⟨none, arrayStacks source [] payload [] []⟩ := by
  have hs : RunSpec (BinaryStackMoves.clearProgram (1 : Fin 5))
      (arrayStacks source work payload [] []) (arrayStacks source [] payload [] []) (work.length+1) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (BinaryStackMoves.clearMachine (1 : Fin 5))
    intro b hb
    have h := BinaryStackMoves.run_clear_stacks (1 : Fin 5)
      (arrayStacks source work payload [] []) b hb
    apply h.trans
    refine config_ext rfl ?_
    intro j
    fin_cases j <;> rfl
  erw [cleanupProgram,run_reoutput]
  exact hs.run_of_le bits hlen

theorem suffix_length_le (xs : List (List Bool)) (i : Nat) (tail : List Bool) :
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail).length ≤
      (xs.flatMap KS.W01.frame ++ tail).length := by
  have he := congrArg (fun ys : List (List Bool) => (ys.flatMap KS.W01.frame ++ tail).length)
    (List.take_append_drop (i + 1) xs)
  simp only [List.flatMap_append, List.length_append] at he ⊢
  omega

theorem run_program (xs : List (List Bool)) (i : Nat) (hi : i < xs.length)
    (tail bits : List Bool)
    (hlen : 5 * (xs.flatMap KS.W01.frame ++ tail).length + i + 4 ≤ bits.length) :
    program.toMachine.run
      ⟨some program.initial, arrayStacks (xs.flatMap KS.W01.frame ++ tail)
        [] [] [] (List.replicate i true)⟩ bits =
      ⟨none, arrayStacks (xs.flatMap KS.W01.frame ++ tail) [] xs[i] [] []⟩ := by
  let source := xs.flatMap KS.W01.frame ++ tail
  let initial := arrayStacks source [] [] [] (List.replicate i true)
  let copied := arrayStacks source source [] [] (List.replicate i true)
  let selected := arrayStacks source ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) xs[i] [] []
  let final := arrayStacks source [] xs[i] [] []
  have hrest : ∀ b : List Bool, (2 * source.length + i + 1) + (source.length + 1) ≤ b.length →
      lookupAndCleanup.toMachine.run ⟨some lookupAndCleanup.initial, copied⟩ b = ⟨none, final⟩ := by
    intro b hb
    apply run_compose_bounded lookupProgram cleanupProgram copied selected final
      (2 * source.length + i + 1) (source.length + 1)
    · exact fun b hb => run_lookup xs i hi tail b hb
    · intro b hb
      apply run_cleanup
      exact (Nat.add_le_add_right (suffix_length_le xs i tail) 1).trans hb
    · exact hb
  change (compose copyProgram lookupAndCleanup).toMachine.run
    ⟨some (compose copyProgram lookupAndCleanup).initial, initial⟩ bits = ⟨none, final⟩
  apply run_compose_bounded copyProgram lookupAndCleanup initial copied final
    (2 * source.length + 2) ((2 * source.length + i + 1) + (source.length + 1))
  · exact fun b hb => run_copy source (List.replicate i true) b hb
  · exact hrest
  · dsimp only [source]
    omega

theorem linear_time (xs : List (List Bool)) (i : Nat) (hi : i < xs.length) (tail : List Bool) :
    HaltsFromWithin program
      ⟨some program.initial, arrayStacks (xs.flatMap KS.W01.frame ++ tail)
        [] [] [] (List.replicate i true)⟩
      (5 * (xs.flatMap KS.W01.frame ++ tail).length + i + 4) := by
  intro bits hlen
  exact congrArg Config.state (run_program xs i hi tail bits hlen.ge)

def liftedProgram {k : Nat} (ports : Fin 5 ↪ Fin k) : Program k := liftPorts program ports

theorem run_program_ports {k : Nat} (ports : Fin 5 ↪ Fin k)
    (xs : List (List Bool)) (i : Nat) (hi : i < xs.length) (tail bits : List Bool)
    (c : Config k program.states)
    (hc : projectPorts ports c =
      ⟨some program.initial, arrayStacks (xs.flatMap KS.W01.frame ++ tail)
        [] [] [] (List.replicate i true)⟩)
    (hlen : 5 * (xs.flatMap KS.W01.frame ++ tail).length + i + 4 ≤ bits.length) :
    let result := (liftedProgram ports).toMachine.run c bits
    result.state = none ∧
      result.«stacks» (ports 0) = xs.flatMap KS.W01.frame ++ tail ∧
      result.«stacks» (ports 1) = [] ∧ result.«stacks» (ports 2) = xs[i] ∧
      result.«stacks» (ports 3) = [] ∧ result.«stacks» (ports 4) = [] ∧
      ∀ j, (∀ r, j ≠ ports r) → result.«stacks» j = c.«stacks» j := by
  have hp := KS.W01.FixedStack.liftPorts_project_run program.toMachine ports c bits
  erw [hc, run_program xs i hi tail bits hlen] at hp
  refine ⟨congrArg (fun d : Config 5 program.states => d.state) hp,
    congrArg (fun d : Config 5 program.states => d.«stacks» 0) hp,
    congrArg (fun d : Config 5 program.states => d.«stacks» 1) hp,
    congrArg (fun d : Config 5 program.states => d.«stacks» 2) hp,
    congrArg (fun d : Config 5 program.states => d.«stacks» 3) hp,
    congrArg (fun d : Config 5 program.states => d.«stacks» 4) hp, ?_⟩
  intro j hj
  exact KS.W01.FixedStack.liftPorts_run_preserves_other program.toMachine ports c bits j hj

end KS.W04.ReusableArrayLookup

end OAI
