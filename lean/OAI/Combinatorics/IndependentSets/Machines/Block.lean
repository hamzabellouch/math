import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineUnaryCounter
import OAI.Combinatorics.IndependentSets.Machines.PoweringMachineRow

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRow
open Turing
open MachineFixedBlockMap
open IndependentSetsGames.Foundations.PCP
section Block

variable {K Λ σ : Type} {N M : Nat}

def encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readEncodedSlots src (List.ofFn id)
    (writeEncodedSlots dst (fun state => F state.2) (List.ofFn id).reverse
      (.load (fun state => (state.1, emptyBuffer N)) next))

def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  encodedBlockStmt src dst F (finishAt exit)

theorem statementPushBound_encodedBlockAt (src dst : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) :
    Runtime.statementPushBound (encodedBlockAt (σ := σ) src dst F exit) = 2 * M := by
  cases exit <;> simp [encodedBlockAt, encodedBlockStmt,
    statementPushBound_readEncodedSlots, statementPushBound_writeEncodedSlots,
    finishAt, Runtime.statementPushBound]

variable [DecidableEq K]

theorem stepAux_encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst)) := by
  unfold encodedBlockStmt
  rw [stepAux_readEncodedAll src _ state bits tapes suffix hinput,
    stepAux_writeEncodedSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, stepAux_encodedBlockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

theorem step_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (hprogram : program label = encodedBlockAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program { l := some label, var := state, stk := tapes } =
      some { l := exit
             var := (state.1, emptyBuffer N)
             stk := Function.update (Function.update tapes src suffix) dst
               (encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  simp only [TM2.step, hprogram,
    stepAux_encodedBlockAt src dst F exit hne bits suffix state tapes hinput]

end Block

def rowAt {K Λ σ : Type} {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → GraphTables.Label) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer (inputSize t S)) :=
  encodedBlockAt src dst (rowBlock labelAt) exit

def machine {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit × Buffer (inputSize t S)
  initialState := ((), emptyBuffer (inputSize t S))
  m _ := rowAt false true labelAt none

theorem machine_statementPushBound {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label) :
    Runtime.statementPushBound ((machine (t := t) labelAt).m ()) = 2 * (q * q) :=
  statementPushBound_encodedBlockAt false true (rowBlock labelAt) none

def machineInTime {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (suffix : List Bool)
    (register : Buffer (inputSize t S)) (tapes : Bool → List Bool)
    (hinput : tapes false = encodeBits (List.ofFn bits) ++ suffix) :
    StateTransition.EvalsToInTime (machine (t := t) labelAt).step
      ⟨some (), ((), register), tapes⟩
      (some ⟨none, ((), emptyBuffer (inputSize t S)),
        Function.update (Function.update tapes false suffix) true
          (encodeBits (List.ofFn (rowBlock labelAt bits)) ++ tapes true)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step (fun _ : Unit => rowAt false true labelAt none)
        { l := some (), var := ((), register), stk := tapes } =
      some { l := none
             var := ((), emptyBuffer (inputSize t S))
             stk := Function.update (Function.update tapes false suffix) true
               (encodeBits (List.ofFn (rowBlock labelAt bits)) ++ tapes true) }
    exact step_encodedBlockAt false true (rowBlock labelAt) (none : Option Unit)
      (fun _ => rowAt false true labelAt none) () rfl (by decide)
      bits suffix ((), register) tapes hinput
  steps_le_m := le_rfl

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRow
namespace IndependentSetsGames.Foundations.Complexity.MachineCountedLoop

open Turing
open scoped BigOperators
open MachineUnaryCounter

variable {K Λ σ : Type} [DecidableEq K]

def guardConfiguration (counter : K) (guardLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some guardLabel, (ambient n, register n), counterTapes counter (base n) n suffix⟩

def bodyConfiguration (counter : K) (bodyLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (n + 1), none), counterTapes counter (base (n + 1)) n suffix⟩

def exitConfiguration (counter : K) (exitLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none), counterTapes counter (base 0) 0 suffix⟩

def BodyTraces (counter : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n →
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some (bodyConfiguration counter bodyLabel suffix ambient base r)) =
      some (guardConfiguration counter guardLabel suffix ambient register base r)

def totalSteps (cost : Nat → Nat) (n : Nat) : Nat :=
  (∑ r ∈ Finset.range n, cost r) + n + 1

@[simp] theorem totalSteps_zero (cost : Nat → Nat) : totalSteps cost 0 = 1 := by
  simp [totalSteps]

theorem totalSteps_succ (cost : Nat → Nat) (n : Nat) :
    totalSteps cost (n + 1) = (totalSteps cost n + cost n) + 1 := by
  simp only [totalSteps, Finset.sum_range_succ]
  omega

theorem loopTrace (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n) :
    (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
      (some (guardConfiguration counter guardLabel suffix ambient register base n)) =
      some (exitConfiguration counter exitLabel suffix ambient base) := by
  revert bodyTraces
  induction n with
  | zero =>
      intro _
      simpa only [totalSteps_zero, guardConfiguration, exitConfiguration] using
        guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
          (base 0) suffix (ambient 0) (register 0)
  | succ n ih =>
      intro bodyTraces
      rw [totalSteps_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n + cost n]
        (TM2.step program
          ⟨some guardLabel, (ambient (n + 1), register (n + 1)),
            counterTapes counter (base (n + 1)) (n + 1) suffix⟩) = _
      rw [guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
        (base (n + 1)) n suffix (ambient (n + 1)) (register (n + 1)),
        Function.iterate_add_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
        ((MachineComposition.advance (TM2.step program))^[cost n]
          (some (bodyConfiguration counter bodyLabel suffix ambient base n))) = _
      rw [bodyTraces n (Nat.lt_succ_self n)]
      exact ih (fun r hr => bodyTraces r (Nat.lt_trans hr (Nat.lt_succ_self n)))

theorem totalSteps_le (cost : Nat → Nat) (n B : Nat)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    totalSteps cost n ≤ n * (B + 1) + 1 := by
  have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
    calc
      (∑ r ∈ Finset.range n, cost r) ≤ ∑ _r ∈ Finset.range n, B :=
        Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
      _ = n * B := by simp
  simpa only [totalSteps, Nat.mul_add, Nat.mul_one] using
    Nat.add_le_add_right (Nat.add_le_add_right hsum n) 1

def loopInTime (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n B : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    StateTransition.EvalsToInTime (TM2.step program)
      (guardConfiguration counter guardLabel suffix ambient register base n)
      (some (exitConfiguration counter exitLabel suffix ambient base))
      (n * (B + 1) + 1) where
  steps := totalSteps cost n
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[totalSteps cost n] _ = _
    exact loopTrace counter guardLabel bodyLabel exitLabel program atGuard suffix
      ambient register base cost n bodyTraces
  steps_le_m := totalSteps_le cost n B bodyBound

omit [DecidableEq K] in

theorem baseFrame (base : Nat → K → List Bool) (frame : K → Prop) (n : Nat)
    (bodyFrame : ∀ r, r < n → ∀ k, frame k → base (r + 1) k = base r k) :
    ∀ k, frame k → base n k = base 0 k := by
  revert bodyFrame
  induction n with
  | zero => intro _ k _; rfl
  | succ n ih =>
      intro bodyFrame k hk
      exact (bodyFrame n (Nat.lt_succ_self n) k hk).trans
        (ih (fun r hr => bodyFrame r (Nat.lt_trans hr (Nat.lt_succ_self n))) k hk)

theorem counterFrame (counter : K) (suffix : List Bool)
    (base : Nat → K → List Bool) (frame : K → Prop) (n : Nat)
    (counterOutside : ∀ k, frame k → k ≠ counter)
    (bodyFrame : ∀ r, r < n → ∀ k, frame k → base (r + 1) k = base r k) :
    ∀ k, frame k →
      counterTapes counter (base n) n suffix k = counterTapes counter (base 0) 0 suffix k := by
  intro k hk
  rw [counterTapes_other counter k (counterOutside k hk),
    counterTapes_other counter k (counterOutside k hk)]
  exact baseFrame base frame n bodyFrame k hk

theorem loopTrace_framed (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n)
    (frame : K → Prop) (counterOutside : ∀ k, frame k → k ≠ counter)
    (bodyFrame : ∀ r, r < n → ∀ k, frame k → base (r + 1) k = base r k) :
    ((MachineComposition.advance (TM2.step program))^[totalSteps cost n]
      (some (guardConfiguration counter guardLabel suffix ambient register base n)) =
      some (exitConfiguration counter exitLabel suffix ambient base)) ∧
    (∀ k, frame k →
      (guardConfiguration counter guardLabel suffix ambient register base n).stk k =
        (exitConfiguration counter exitLabel suffix ambient base).stk k) :=
  ⟨loopTrace counter guardLabel bodyLabel exitLabel program atGuard suffix
      ambient register base cost n bodyTraces,
    counterFrame counter suffix base frame n counterOutside bodyFrame⟩

end IndependentSetsGames.Foundations.Complexity.MachineCountedLoop

end OAI
