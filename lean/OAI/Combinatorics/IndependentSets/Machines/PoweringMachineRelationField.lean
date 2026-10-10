import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PoweringOpinions
import OAI.Combinatorics.IndependentSets.Machines.PoweringGlobalEnumeration

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := MachineUnaryEqualityBit.State A
abbrev Label (path : List (Fin d)) := PoweringMachineWord.Label path.length ⊕ MachineAffineLookup.Label

def lookupTapes (placement : PoweringMachineTapes.Tape max → K) (i : Fin 5) : K :=
  placement (PoweringMachineTapes.relationPlacement max i.succ)

omit [DecidableEq K] in
theorem lookupTapes_injective (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) : Function.Injective (lookupTapes placement) := by
  intro i j h
  exact (Fin.succ_injective _) ((PoweringMachineTapes.relationPlacement_injective max) (distinct h))

omit [DecidableEq K] in
theorem source_outside_lookup (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) :
    ∀ i, placement (.inl 6) ≠ lookupTapes placement i := by
  intro i h
  have heq : PoweringMachineTapes.relationPlacement max 0 = PoweringMachineTapes.relationPlacement max i.succ := by
    simpa [PoweringMachineTapes.leftEndpoint] using distinct h
  have hi := (PoweringMachineTapes.relationPlacement_injective max) heq
  have hv := congrArg Fin.val hi
  simp at hv

def endpoint (table : PortTables.Table n d) (vertex : Fin n) (path : List (Fin d)) : Fin n :=
  PoweringWalks.walkEnd (PortTables.portGraph table) vertex path

theorem endpoint_eq_wordEnd (table : PortTables.Table n d) (vertex : Fin n)
    (path : List (Fin d)) :
    endpoint table vertex path =
      PoweringWalks.wordEnd (PortTables.portGraph table) path.length vertex path.get := by
  rw [PoweringReach.wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
  rfl

def bit (table : PortTables.Table n d) (vertex : Fin n) (path : List (Fin d))
    (port : Fin d) (left right : PortTables.Label) : Nat :=
  GraphTables.bitWord (PortTables.accepts table (endpoint table vertex path, port) left right)

def instruction (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ) :
    Label path → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
      path.get (fun z => labels (.inl z)) (some (labels (.inr .seed))) q
  | .inr q => PoweringMachineRelation.instruction (placement (.inl 6)) (lookupTapes placement)
      port (GraphTables.relationIndex (left, right)) (fun z => labels (.inr z)) exit q

def afterWord (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (table : PortTables.Table n d)
    (vertex : Fin n) (base : K → List Bool) : K → List Bool :=
  PoweringMachineWord.finalTapes table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    vertex path.get base

def finalTapes (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (lookupTapes placement)
    (afterWord placement path lengthBound table vertex base) (PortTables.tableWords table)
    (PoweringMachineRelation.address (endpoint table vertex path) port
      (GraphTables.relationIndex (left, right))) (bit table vertex path port left right)

def steps (path : List (Fin d)) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) : Nat :=
  PoweringMachineWord.steps table path.length vertex path.get +
    MachineAffineLookup.steps (PortTables.tableWords table) (endpoint table vertex path).val
      (4098 * d) (4098 * port.val + 4 + (GraphTables.relationIndex (left, right)).val)

theorem afterWord_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4) (h₆ : role ≠ 6) :
    afterWord placement path lengthBound table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  apply PoweringMachineWord.finalTapes_other
  · intro h; exact h₂ (by simpa [PoweringMachineTapes.query] using distinct h)
  · intro h; exact h₃ (by simpa [PoweringMachineTapes.scan] using distinct h)
  · intro h; exact h₄ (by simpa [PoweringMachineTapes.reverse] using distinct h)
  · intro h; exact h₆ (by simpa [PoweringMachineTapes.leftEndpoint] using distinct h)
  · intro i h
    have heq := distinct h
    simp at heq

theorem finalTapes_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4)
    (h₆ : role ≠ 6) (h₁₀ : role ≠ 10) :
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  calc
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
        afterWord placement path lengthBound table vertex base (placement (.inl role)) := by
      apply MachineAffineLookup.finalTapes_other
      · intro h; exact h₂ (by simpa [lookupTapes, PoweringMachineTapes.query] using distinct h)
      · intro h; exact h₃ (by simpa [lookupTapes, PoweringMachineTapes.scan] using distinct h)
      · intro h; exact h₁₀ (by simpa [lookupTapes, PoweringMachineTapes.rowOutput] using distinct h)
    _ = _ := afterWord_frame placement distinct path lengthBound table vertex base role h₂ h₃ h₄ h₆

theorem finalTapes_other (placement : PoweringMachineTapes.Tape max → K)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (k : K) (outside : ∀ i, k ≠ placement i) :
    finalTapes placement path lengthBound port left right table vertex base k = base k := by
  calc
    finalTapes placement path lengthBound port left right table vertex base k =
        afterWord placement path lengthBound table vertex base k :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ (outside _) (outside _) (outside _)
    _ = base k := PoweringMachineWord.finalTapes_other _ _ _ _ _ _ _
      (outside _) (outside _) (outside _) (outside _) (fun i => outside _)

theorem fieldTrace (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement path lengthBound port left right labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 5)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix) (ambient : A) :
    (advance (TM2.step program))^[steps path port left right table vertex]
      (some ⟨some (labels (.inl (PoweringMachineWord.entry path.length))), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes placement path lengthBound port left right table vertex base⟩ ∧
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl 10)) =
      encodeWord (bit table vertex path port left right) ++ base (placement (.inl 10)) := by
  have hword := PoweringMachineWord.wordTrace table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective lengthBound false)) vertex path.get
    (fun q => labels (.inl q)) (some (labels (.inr .seed))) program
    (fun q => atLabels (.inl q)) base (by simpa [PoweringMachineTapes.table] using tableWord)
    (by simpa [PoweringMachineTapes.scratch] using scratchEmpty) suffix
    (by simpa [PoweringMachineTapes.start] using sourceWord) (ambient, false, none) none
  let mid := afterWord placement path lengthBound table vertex base
  have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 0
      (by decide) (by decide) (by decide) (by decide)]
    exact tableWord
  have hmidScratch : mid (placement (.inl 5)) = [] := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 5
      (by decide) (by decide) (by decide) (by decide)]
    exact scratchEmpty
  have hmidOutput : mid (placement (.inl 10)) = base (placement (.inl 10)) :=
    afterWord_frame placement distinct path lengthBound table vertex base 10
      (by decide) (by decide) (by decide) (by decide)
  have hmidEndpoint : mid (placement (.inl 6)) = encodeWord (endpoint table vertex path).val ++
      base (placement (.inl 6)) := by
    dsimp only [mid, afterWord]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five, PoweringMachineTapes.endpoint_false,
      PoweringMachineTapes.leftEndpoint, ← endpoint_eq_wordEnd] using hword.2
  have hrelation := PoweringMachineRelation.relationTrace (placement (.inl 6)) (lookupTapes placement)
    (lookupTapes_injective placement distinct) (source_outside_lookup placement distinct)
    port (GraphTables.relationIndex (left, right)) (fun q => labels (.inr q)) exit program
    (fun q => atLabels (.inr q)) table (endpoint table vertex path) mid
    (by simpa [lookupTapes, PoweringMachineTapes.table] using hmidTable)
    (by simpa [lookupTapes, PoweringMachineTapes.scratch] using hmidScratch)
    (base (placement (.inl 6))) hmidEndpoint (ambient, false, none) none
  constructor
  · simp only [MachineUnaryEqualityBit.clean]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, hword.1]
    exact hrelation
  · change MachineAffineLookup.finalTapes (lookupTapes placement) _ _ _ _ (lookupTapes placement 3) = _
    rw [MachineAffineLookup.finalTapes_output]
    change encodeWord (bit table vertex path port left right) ++ mid (placement (.inl 10)) = _
    rw [hmidOutput]

theorem steps_le (path : List (Fin d)) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) :
    steps path port left right table vertex ≤
      (14 * path.length + 9) * (PortTables.tableBits table).length + 12 * path.length + 9 := by
  have hw := PoweringMachineWord.steps_le table path.length vertex path.get
  have hr := PoweringMachineRelation.steps_le table (endpoint table vertex path) port
    (GraphTables.relationIndex (left, right))
  simp only [steps, Nat.add_mul, Nat.mul_assoc] at hw ⊢
  omega

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRelationField

end OAI
