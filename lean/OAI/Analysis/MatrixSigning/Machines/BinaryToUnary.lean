import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedStackPortLift
import OAI.Analysis.MatrixSigning.Machines.BinaryToUnaryRun

namespace OAI

namespace KS.W03.BinaryToUnary
open KS.W01.FixedStack KS.W03.UnaryArithmetic KS.W19

theorem run_input (xs coins : List Bool) (hlen : totalTicks xs ≤ coins.length) :
    machine.run (machine.init xs) coins =
      cfg none [] (List.replicate (bitsValue xs) true) [] := by
  have ht : (coins.take (totalTicks xs)).length = totalTicks xs := by
    simp only [List.length_take, Nat.min_eq_left hlen]
  conv_lhs => rw [← List.take_append_drop (totalTicks xs) coins]
  rw [Machine.run_append, run_input_exact xs _ ht]
  exact Machine.run_halted machine (cfg none [] (List.replicate (bitsValue xs) true) []) rfl
    (coins.drop (totalTicks xs))

theorem run_input_linear (xs coins : List Bool)
    (hlen : 4 * bitsValue xs + 4 * xs.length + 2 ≤ coins.length) :
    machine.run (machine.init xs) coins =
      cfg none [] (List.replicate (bitsValue xs) true) [] :=
  run_input xs coins ((totalTicks_le_linear xs).trans hlen)

theorem output_correct (xs coins : List Bool)
    (hlen : 5 * (bitsValue xs + xs.length + 1) ^ 2 ≤ coins.length) :
    machine.output xs coins = List.replicate (bitsValue xs) true := by
  unfold Machine.output
  rw [run_input xs coins ((totalTicks_le xs).trans hlen)]
  rfl

theorem halts_within (xs : List Bool) :
    machine.HaltsWithin xs (5 * (bitsValue xs + xs.length + 1) ^ 2) := by
  intro seed
  change (machine.run (machine.init xs) (List.ofFn seed)).state = none
  rw [run_input xs (List.ofFn seed) (by
    simpa only [List.length_ofFn] using totalTicks_le xs)]
  rfl

theorem uniform_binary_to_unary :
    ∃ M : Machine, M.stackCount = 3 ∧ M.states = 8 ∧
      ∀ n : ℕ, let xs := Computability.encodeNat n
        M.HaltsWithin xs (5 * (n + xs.length + 1) ^ 2) ∧
        ∀ coins : List Bool, 5 * (n + xs.length + 1) ^ 2 ≤ coins.length →
          M.output xs coins = List.replicate n true := by
  refine ⟨machine, rfl, rfl, ?_⟩
  intro n
  dsimp only
  constructor
  · simpa only [bitsValue_encodeNat] using halts_within (Computability.encodeNat n)
  · intro coins hcoins
    have h := output_correct (Computability.encodeNat n) coins
    simpa only [bitsValue_encodeNat] using h (by simpa only [bitsValue_encodeNat] using hcoins)

theorem run_on_ports_budget {K : ℕ} (ports : Fin 3 ↪ Fin K)
    (workTapes : Fin K → List Bool) (xs coins : List Bool)
    (hstart : (fun i => workTapes (ports i)) = ![xs, [], []])
    (hlen : totalTicks xs ≤ coins.length) :
    let result := (liftPorts machine ports).run ⟨some machine.initial, workTapes⟩ coins
    projectPorts ports result = cfg none [] (List.replicate (bitsValue xs) true) [] ∧
      ∀ j, (∀ i, j ≠ ports i) → result.«stacks» j = workTapes j := by
  dsimp only
  constructor
  · erw [liftPorts_project_run]
    change machine.run ⟨some machine.initial, fun i => workTapes (ports i)⟩ coins = _
    erw [hstart]
    have h := run_input xs coins hlen
    rw [init_eq] at h
    exact h
  · intro j hj
    exact liftPorts_run_preserves_other machine ports _ coins j hj

theorem run_on_ports {K : ℕ} (ports : Fin 3 ↪ Fin K)
    (workTapes : Fin K → List Bool) (xs coins : List Bool)
    (hstart : (fun i => workTapes (ports i)) = ![xs, [], []])
    (hlen : 5 * (bitsValue xs + xs.length + 1) ^ 2 ≤ coins.length) :
    let result := (liftPorts machine ports).run ⟨some machine.initial, workTapes⟩ coins
    projectPorts ports result = cfg none [] (List.replicate (bitsValue xs) true) [] ∧
      ∀ j, (∀ i, j ≠ ports i) → result.«stacks» j = workTapes j :=
  run_on_ports_budget ports workTapes xs coins hstart ((totalTicks_le xs).trans hlen)

theorem run_on_ports_linear {K : ℕ} (ports : Fin 3 ↪ Fin K)
    (workTapes : Fin K → List Bool) (xs coins : List Bool)
    (hstart : (fun i => workTapes (ports i)) = ![xs, [], []])
    (hlen : 4 * bitsValue xs + 4 * xs.length + 2 ≤ coins.length) :
    let result := (liftPorts machine ports).run ⟨some machine.initial, workTapes⟩ coins
    projectPorts ports result = cfg none [] (List.replicate (bitsValue xs) true) [] ∧
      ∀ j, (∀ i, j ≠ ports i) → result.«stacks» j = workTapes j :=
  run_on_ports_budget ports workTapes xs coins hstart ((totalTicks_le_linear xs).trans hlen)

end KS.W03.BinaryToUnary

end OAI
