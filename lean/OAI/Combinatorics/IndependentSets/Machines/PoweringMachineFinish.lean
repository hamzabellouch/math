import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineDrainMany

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Alphabet (_ : K) := Bool

abbrev Label (enumeration : Fin N ≃ K) (output : K) :=
  MachineUnaryAffineAt.Label ⊕ (MachineUnaryAffineAt.Label ⊕
    MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output))

def copyInstruction (source scratch output : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output 0 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch output 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

def instruction (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (labels : Label enumeration output → Λ) :
    Label enumeration output → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .inl l => copyInstruction headerD scratch output (fun q => labels (.inl q))
      (some (labels (.inr (.inl .seed)))) l
  | .inr (.inl l) => copyInstruction headerV scratch output
      (fun q => labels (.inr (.inl q)))
      (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
        (fun q => labels (.inr (.inr q))) none) l
  | .inr (.inr l) => MachineDrainMany.instruction
      (MachineDrainMany.workTapes enumeration output) (fun q => labels (.inr (.inr q))) none l

def program (enumeration : Fin N ≃ K) (headerV headerD output scratch : K) :
    Label enumeration output →
      TM2.Stmt (Alphabet (K := K)) (Label enumeration output) (σ × Option Bool) :=
  instruction enumeration headerV headerD output scratch id

def afterD (output : K) (base : K → List Bool) (m : Nat) : K → List Bool :=
  Function.update base output (encodeWord m ++ base output)

def afterHeaders (output : K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update base output (encodeWords [n, m] ++ base output)

@[simp] theorem afterHeaders_output (output : K) (base : K → List Bool) (n m : Nat) :
    afterHeaders output base n m output = encodeWords [n, m] ++ base output := by
  simp only [afterHeaders, Function.update_self]

theorem afterHeaders_other (output : K) (base : K → List Bool) (n m : Nat)
    (k : K) (hk : k ≠ output) : afterHeaders output base n m k = base k :=
  Function.update_of_ne hk _ _

def copySteps (n m : Nat) : Nat := (2 * (m + 1) + 1) + (2 * (n + 1) + 1)

theorem copySteps_eq (n m : Nat) : copySteps n m = 2 * (n + m) + 6 := by
  unfold copySteps
  omega

def steps (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + MachineDrainMany.steps (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m)

def budget (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + (MachineDrainMany.lengthSum (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) + (MachineDrainMany.workTapes enumeration output).length)

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem traceAt (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (labels : Label enumeration output → Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, target (labels l) =
      instruction enumeration headerV headerD output scratch labels l)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps enumeration output base n m]
      (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ := by
  have hd := MachineUnaryAffineAt.seededAffineTrace headerD scratch output hds hdo hso 1 0
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (.inr (.inl .seed)))) target
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base m suffixD wordD scratchEmpty ambient register
  simp only [Nat.one_mul, Nat.add_zero] at hd
  change (advance (TM2.step target))^[2 * (m + 1) + 1]
    (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
    some ⟨some (labels (.inr (.inl .seed))), (ambient, none), afterD output base m⟩ at hd
  have wordV' : afterD output base m headerV = encodeWord n ++ suffixV := by
    simpa only [afterD, Function.update_of_ne hvo] using wordV
  have scratchEmpty' : afterD output base m scratch = [] := by
    simpa only [afterD, Function.update_of_ne hso] using scratchEmpty
  have hv := MachineUnaryAffineAt.seededAffineTrace headerV scratch output hvs hvo hso 1 0
    (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
    (labels (.inr (.inl .restore)))
    (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
      (fun q => labels (.inr (.inr q))) none)
    target (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
    (atLabels (.inr (.inl .restore))) (afterD output base m) n suffixV
    wordV' scratchEmpty' ambient none
  simp only [Nat.one_mul, Nat.add_zero] at hv
  have copied : Function.update (afterD output base m) output
      (encodeWord n ++ afterD output base m output) = afterHeaders output base n m := by
    simp only [afterD, afterHeaders, Function.update_self, Function.update_idem,
      encodeWords, List.append_nil, List.append_assoc]
  rw [copied] at hv
  have cleaned := MachineDrainMany.cleanupTrace enumeration output
    (fun q => labels (.inr (.inr q))) target (fun l => atLabels (.inr (.inr l)))
    (afterHeaders output base n m) ambient
  rw [afterHeaders_output] at cleaned
  have total := trace_trans _ (trace_trans _ hd hv) cleaned
  simpa only [steps, copySteps] using total

theorem trace (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program enumeration headerV headerD output scratch)))^[
      steps enumeration output base n m]
      (some ⟨some (.inl .seed), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ :=
  traceAt enumeration headerV headerD output scratch hvs hvo hds hdo hso id
    (program enumeration headerV headerD output scratch) (fun _ => rfl)
    base n m suffixV suffixD wordV wordD scratchEmpty ambient register

theorem steps_le_budget (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m : Nat) :
    steps enumeration output base n m ≤ budget enumeration output base n m :=
  Nat.add_le_add_left (MachineDrainMany.steps_le
    (MachineDrainMany.workTapes enumeration output) (afterHeaders output base n m)) _

theorem afterHeaders_length_le (output : K) (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) (k : K) :
    (afterHeaders output base n m k).length ≤ bound + n + m + 2 := by
  by_cases hk : k = output
  · subst k
    rw [afterHeaders_output]
    have hb := bounded output
    simp only [List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  · rw [afterHeaders_other output base n m k hk]
    have hb := bounded k
    omega

theorem steps_le_uniform (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    steps enumeration output base n m ≤ 2 * (n + m) + 6 + N * (bound + n + m + 3) := by
  have hc := MachineDrainMany.steps_le_uniform (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) (bound + n + m + 2)
    (afterHeaders_length_le output base n m bound bounded)
  have hl := MachineDrainMany.workTapes_length_le enumeration output
  have hm := Nat.mul_le_mul_right (bound + n + m + 3) hl
  rw [show bound + n + m + 2 + 1 = bound + n + m + 3 by omega] at hc
  unfold steps
  rw [copySteps_eq]
  exact Nat.add_le_add_left (hc.trans hm) _

def execution (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program enumeration headerV headerD output scratch))
      ⟨some (.inl .seed), (ambient, register), base⟩
      (some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩)
      (budget enumeration output base n m) where
  steps := steps enumeration output base n m
  evals_in_steps := trace enumeration headerV headerD output scratch hvs hvo hds hdo hso
    base n m suffixV suffixD wordV wordD scratchEmpty ambient register
  steps_le_m := steps_le_budget enumeration output base n m

end IndependentSetsGames.Foundations.Complexity.PoweringMachineFinish

end OAI
