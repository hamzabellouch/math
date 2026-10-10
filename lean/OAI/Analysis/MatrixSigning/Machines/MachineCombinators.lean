import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedLoop

namespace OAI

section

namespace KS.W03.MachineCombinators

open KS.W01.FixedStack
open KS.W29.FixedSequential

def RunSpec {k : ℕ} (P : Program k) (before after : Fin k → List Bool) (ticks : ℕ) : Prop :=
  ∀ bits : List Bool, bits.length = ticks →
    P.toMachine.run ⟨some P.initial, before⟩ bits = ⟨none, after⟩

theorem RunSpec.run_of_le {k : ℕ} {P : Program k} {before after : Fin k → List Bool}
    {ticks : ℕ} (h : RunSpec P before after ticks) (bits : List Bool)
    (hlen : ticks ≤ bits.length) :
    P.toMachine.run ⟨some P.initial, before⟩ bits = ⟨none, after⟩ := by
  have ht : (bits.take ticks).length = ticks := by
    simp only [List.length_take, Nat.min_eq_left hlen]
  have hs := h (bits.take ticks) ht
  conv_lhs => rw [← List.take_append_drop ticks bits]
  rw [Machine.run_append, hs, Machine.run_halted _ _ rfl]

theorem RunSpec.mono {k : ℕ} {P : Program k} {before after : Fin k → List Bool}
    {ticks larger : ℕ} (h : RunSpec P before after ticks) (hle : ticks ≤ larger) :
    RunSpec P before after larger := by
  intro bits hbits
  exact h.run_of_le bits (by simpa only [hbits] using hle)

theorem RunSpec.compose {k : ℕ} {P Q : Program k}
    {before middle after : Fin k → List Bool} {t₁ t₂ : ℕ}
    (hP : RunSpec P before middle t₁) (hQ : RunSpec Q middle after t₂) :
    RunSpec (KS.W29.FixedSequential.compose P Q) before after (t₁ + t₂) := by
  intro bits hbits
  let c : Config k P.states := ⟨some P.initial, before⟩
  have htake : (bits.take t₁).length = t₁ := by
    simp only [List.length_take, hbits]
    omega
  have hfirst : P.toMachine.run c (bits.take t₁) = ⟨none, middle⟩ := hP _ htake
  obtain ⟨first, leftover, heq, halt⟩ :=
    exists_halting_prefix P c (bits.take t₁) (congrArg Config.state hfirst)
  have hfl : first.length ≤ t₁ := by
    have hh := congrArg List.length heq
    simp only [List.length_append, htake] at hh
    omega
  have hfout : P.toMachine.run c first = ⟨none, middle⟩ := by
    erw [heq, Machine.run_append, Machine.run_halted _ _ halt.2] at hfirst
    exact hfirst
  have hwhole : bits = first ++ (leftover ++ bits.drop t₁) := by
    calc
      bits = bits.take t₁ ++ bits.drop t₁ := (List.take_append_drop t₁ bits).symm
      _ = first ++ (leftover ++ bits.drop t₁) := by rw [heq, List.append_assoc]
  have hremain : t₂ ≤ (leftover ++ bits.drop t₁).length := by
    have hh := congrArg List.length hwhole
    simp only [List.length_append, hbits] at hh
    simp only [List.length_append]
    omega
  change (KS.W29.FixedSequential.compose P Q).toMachine.run (liftLeft P Q c) bits = ⟨none, after⟩
  rw [hwhole, run_compose P Q c first _ halt, hfout,
    hQ.run_of_le _ hremain]
  rfl

theorem lift3_run_eq {k : ℕ} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : Config k M.states) (bits : List Bool) (out : Fin k → List Bool)
    (h : M.run (project ports c) bits = ⟨none, fun i => out (ports i)⟩)
    (hother : ∀ j, (∀ i, j ≠ ports i) → out j = c.«stacks» j) :
    (lift3 M ports).run c bits = ⟨none, out⟩ := by
  have hp := lift3_project_run M ports c bits
  rw [h] at hp
  have hs : ((lift3 M ports).run c bits).state = none :=
    congrArg (fun d : KS.W29.Config M.states => d.state) hp
  have hst : ((lift3 M ports).run c bits).«stacks» = out := by
    funext j
    by_cases hj : ∃ i, j = ports i
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun d : KS.W29.Config M.states => d.«stacks» i) hp
    · have hnone : ∀ i, j ≠ ports i := by simpa only [not_exists] using hj
      rw [lift3_run_preserves_other M ports c bits j hnone, hother j hnone]
  exact congrArg₂ Config.mk hs hst

theorem RunSpec.loop_body_then {k : ℕ} {P : Program k}
    {before after : Fin k → List Bool} {ticks : ℕ}
    (hP : RunSpec P before after ticks)
    (guard : (Fin k → Fin 3) → Bool → KS.W29.FixedLoop.GuardInstruction k)
    (bits : List Bool) (hlen : ticks ≤ bits.length) :
    ∃ rest : List Bool, bits.length - ticks ≤ rest.length ∧
      (KS.W29.FixedLoop.loop P guard).toMachine.run
        (KS.W29.FixedLoop.liftBody P ⟨some P.initial, before⟩) bits =
      (KS.W29.FixedLoop.loop P guard).toMachine.run
        ⟨some (KS.W29.FixedLoop.guardState P), after⟩ rest := by
  let c : Config k P.states := ⟨some P.initial, before⟩
  have htake : (bits.take ticks).length = ticks := by
    simp only [List.length_take, Nat.min_eq_left hlen]
  have hfull : P.toMachine.run c (bits.take ticks) = ⟨none, after⟩ := hP _ htake
  obtain ⟨first, leftover, heq, halt⟩ :=
    exists_halting_prefix P c (bits.take ticks) (congrArg Config.state hfull)
  have hout : P.toMachine.run c first = ⟨none, after⟩ := by
    erw [heq, Machine.run_append, Machine.run_halted _ _ halt.2] at hfull
    exact hfull
  have hwhole : bits = first ++ (leftover ++ bits.drop ticks) := by
    calc
      bits = bits.take ticks ++ bits.drop ticks := (List.take_append_drop ticks bits).symm
      _ = first ++ (leftover ++ bits.drop ticks) := by rw [heq, List.append_assoc]
  refine ⟨leftover ++ bits.drop ticks, ?_, ?_⟩
  · simp only [List.length_append, List.length_drop]
    omega
  · conv_lhs => rw [hwhole]
    rw [KS.W29.FixedLoop.run_body_then P guard c first _ halt, hout]

end KS.W03.MachineCombinators

end

end OAI
