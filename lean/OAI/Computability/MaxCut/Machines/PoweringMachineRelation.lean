import Mathlib
import OAI.Computability.MaxCut.Machines.PoweringMachineRotor

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def address (vertex : Fin n) (port : Fin d) (position : Fin 4096) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 4 + position.val)

def value (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) : Nat :=
  GraphTables.bitWord table.relations[PortTables.rowIndex n d (vertex, port)][position]

theorem selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) :
    (PortTables.tableWords table)[address vertex port position]? =
      some (value table vertex port position) := by
  have h := PortTableLookup.relation_word table (PortTables.rowIndex n d (vertex, port)) position
  have hindex : address vertex port position =
      4 + 4098 * (PortTables.rowIndex n d (vertex, port)).val + position.val := by
    simp only [address, PortTables.rowIndex_val, Nat.mul_add, Nat.mul_assoc]
    omega
  rw [hindex]
  exact h

def instruction (source : K) (tape : Fin 5 → K) (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ) :
    MachineAffineLookup.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineAffineLookup.instruction source tape (4098 * d)
    (4098 * port.val + 4 + position.val) labels exit

/-- Actual predicate access, with serialization selection discharged. -/
theorem relationTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape port position labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table) (scratchEmpty : base (tape 4) = [])
    (suffix : List Bool) (sourceWord : base source = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (PortTables.tableWords table)
      vertex.val (4098 * d) (4098 * port.val + 4 + position.val)]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), MachineAffineLookup.finalTapes tape base
        (PortTables.tableWords table) (address vertex port position) (value table vertex port position)⟩ :=
  MachineAffineLookup.affineLookupTrace source tape distinct outside
    (4098 * d) (4098 * port.val + 4 + position.val) labels exit program atLabels
    base (PortTables.tableWords table) tableWord scratchEmpty vertex.val suffix sourceWord
    (value table vertex port position) (selected table vertex port position) ambient register

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) :
    MachineAffineLookup.steps (PortTables.tableWords table) vertex.val
      (4098 * d) (4098 * port.val + 4 + position.val) ≤
      7 * (PortTables.tableBits table).length + 6 :=
  MachineAffineLookup.steps_le_table (PortTables.tableWords table) vertex.val
    (4098 * d) (4098 * port.val + 4 + position.val) (value table vertex port position)
    (selected table vertex port position)
    (Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table))

/-- The semantic two-label predicate is the field used by the row producer. -/
theorem value_eq_accepts (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (left right : PortTables.Label) :
    value table vertex port (GraphTables.relationIndex (left, right)) =
      GraphTables.bitWord (PortTables.accepts table (vertex, port) left right) := rfl

def machine (degree : Nat) (port : Fin degree) (position : Fin 4096) : FinTM2 :=
  MachineAffineLookup.machine (4098 * degree) (4098 * port.val + 4 + position.val)

end MaxCutGames.Foundations.Complexity.PoweringMachineRelation

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRelationField

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

/-- Table, start, scratch and both comparison stacks satisfy these numerical
inequalities, so their contents are preserved without an emptiness premise. -/
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

/-- Any caller tape outside the shared placement is preserved, including a
separate accumulator for already completed output rows. -/
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

end MaxCutGames.Foundations.Complexity.PoweringMachineRelationField

/-!
# Actual producer for equality of two bounded walk endpoints

The two port words are fixed finite control. Each executes against the live
rotor table from the same preserved starting vertex. Their endpoint fields
are compared by the physical unary equality primitive. The emitted field is
the Boolean equality of the two actual walk endpoints.

Work tapes may retain arbitrary histories. The table, start, scratch and two
comparison copies satisfy exact frame theorems. There is no execution or
running-time premise in the composite trace theorem.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape := PoweringMachineTapes.Tape
abbrev State := MachineUnaryEqualityBit.State
abbrev Label (l r : Nat) :=
  PoweringMachineWord.Label l ⊕ PoweringMachineWord.Label r ⊕ MachineUnaryEqualityBit.Label

def entry (l r : Nat) : Label l r := .inl (PoweringMachineWord.entry l)

def instruction (hl : l ≤ max) (hr : r ≤ max) (placement : Tape max → K)
    (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ) :
    Label l r → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction l
      (placement ∘ PoweringMachineTapes.wordPlacement hl false) left
      (fun z => labels (.inl z))
      (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) q
  | .inr (.inl q) => PoweringMachineWord.instruction r
      (placement ∘ PoweringMachineTapes.wordPlacement hr true) right
      (fun z => labels (.inr (.inl z)))
      (some (labels (.inr (.inr .seedLeft)))) q
  | .inr (.inr q) => MachineUnaryEqualityBit.instruction
      (placement ∘ PoweringMachineTapes.equalityPlacement max)
      (fun z => labels (.inr (.inr z))) exit q

def endpoint (graph : PortTables.Table n d) {t : Nat} (vertex : Fin n)
    (ports : Fin t → Fin d) : Fin n :=
  PoweringWalks.wordEnd (PortTables.portGraph graph) t vertex ports

def resultBit (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) : Bool :=
  decide (endpoint graph vertex left = endpoint graph vertex right)

def wordTapes (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (target : Bool) (vertex : Fin n)
    (ports : Fin t → Fin d) (base : K → List Bool) : K → List Bool :=
  PoweringMachineWord.finalTapes graph t
    (placement ∘ PoweringMachineTapes.wordPlacement h target) vertex ports base

def finalTapes (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool) :
    K → List Bool :=
  let afterLeft := wordTapes graph hl placement false vertex left base
  let afterBoth := wordTapes graph hr placement true vertex right afterLeft
  Function.update afterBoth (placement (.inl 10))
    (MachineUnaryEqualityBit.bitEncoding (resultBit graph vertex left right) ++
      afterBoth (placement (.inl 10)))

def steps (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) : Nat :=
  PoweringMachineWord.steps graph l vertex left +
    PoweringMachineWord.steps graph r vertex right +
    MachineUnaryEqualityBit.steps (endpoint graph vertex left).val
      (endpoint graph vertex right).val

theorem steps_le (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) :
    steps graph vertex left right ≤
      (14 * (l + r) + 10) * (PortTables.tableBits graph).length + 12 * (l + r) + 15 := by
  have hl := PoweringMachineWord.steps_le graph l vertex left
  have hr := PoweringMachineWord.steps_le graph r vertex right
  have he := MachineUnaryEqualityBit.steps_le
    (endpoint graph vertex left).val (endpoint graph vertex right).val
  have hleft := Nat.le_trans (Nat.le_of_lt (endpoint graph vertex left).isLt)
    (PortTables.vertices_le_tableBits_length graph)
  have hright := Nat.le_trans (Nat.le_of_lt (endpoint graph vertex right).isLt)
    (PortTables.vertices_le_tableBits_length graph)
  unfold steps
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hl hr ⊢
  omega

/-- The only variable-size work areas changed by a word are the declared
query, scan, reverse, selected endpoint, and trajectory tapes. -/
theorem wordTapes_other (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (target : Bool) (vertex : Fin n)
    (ports : Fin t → Fin d) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 2)) (hscan : k ≠ placement (.inl 3))
    (hreverse : k ≠ placement (.inl 4))
    (houtput : k ≠ placement (PoweringMachineTapes.endpoint max target))
    (hpositions : ∀ i : Fin max, k ≠ placement (.inr i)) :
    wordTapes graph h placement target vertex ports base k = base k := by
  apply PoweringMachineWord.finalTapes_other
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_one,
      PoweringMachineTapes.query] using hquery
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_two,
      PoweringMachineTapes.scan] using hscan
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_three,
      PoweringMachineTapes.reverse] using hreverse
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five] using houtput
  · intro i
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_succ] using
      hpositions (Fin.castLE h i)

theorem wordTapes_role (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (target : Bool) (vertex : Fin n) (ports : Fin t → Fin d)
    (base : K → List Bool) (j : Fin 11)
    (hquery : j ≠ 2) (hscan : j ≠ 3) (hreverse : j ≠ 4)
    (houtput : j ≠ if target then 7 else 6) :
    wordTapes graph h placement target vertex ports base (placement (.inl j)) =
      base (placement (.inl j)) := by
  apply wordTapes_other
  · intro he
    exact hquery (Sum.inl.inj (distinct he))
  · intro he
    exact hscan (Sum.inl.inj (distinct he))
  · intro he
    exact hreverse (Sum.inl.inj (distinct he))
  · intro he
    apply houtput
    cases target <;> exact Sum.inl.inj (distinct he)
  · intro i he
    cases distinct he

theorem finalTapes_other (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 2)) (hscan : k ≠ placement (.inl 3))
    (hreverse : k ≠ placement (.inl 4)) (hleft : k ≠ placement (.inl 6))
    (hright : k ≠ placement (.inl 7)) (hrow : k ≠ placement (.inl 10))
    (hpositions : ∀ i : Fin max, k ≠ placement (.inr i)) :
    finalTapes graph hl hr placement vertex left right base k = base k := by
  unfold finalTapes
  rw [Function.update_of_ne hrow]
  rw [wordTapes_other graph hr placement true vertex right _ k
    hquery hscan hreverse hright hpositions]
  exact wordTapes_other graph hl placement false vertex left base k
    hquery hscan hreverse hleft hpositions

/-- This single statement covers table 0, start 1, scratch 5, and copies 8/9. -/
theorem finalTapes_role (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool)
    (j : Fin 11) (hrole : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 8 ∨ j = 9) :
    finalTapes graph hl hr placement vertex left right base (placement (.inl j)) =
      base (placement (.inl j)) := by
  apply finalTapes_other
  all_goals first
    | (intro he; have hij := Sum.inl.inj (distinct he); rcases hrole with rfl | rfl | rfl | rfl | rfl <;> simp at hij)
    | (intro i he; cases distinct he)

theorem finalTapes_output (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool) :
    finalTapes graph hl hr placement vertex left right base (placement (.inl 10)) =
      MachineUnaryEqualityBit.bitEncoding (resultBit graph vertex left right) ++
        base (placement (.inl 10)) := by
  unfold finalTapes
  rw [Function.update_self,
    wordTapes_role graph hr placement distinct true vertex right _ 10
      (by decide) (by decide) (by decide) (by decide),
    wordTapes_role graph hl placement distinct false vertex left base 10
      (by decide) (by decide) (by decide) (by decide)]

private theorem joinTrace_inline_PoweringMachineEqualityField {X : Type*} {f : X → X} {a b c : X} {u v : Nat}
    (first : f^[u] a = b) (second : f^[v] b = c) : f^[u + v] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem fieldTrace (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ q, program (labels q) = instruction hl hr placement left right labels exit q)
    (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits graph)
    (scratchEmpty : base (placement (.inl 5)) = [])
    (leftCopyEmpty : base (placement (.inl 8)) = [])
    (rightCopyEmpty : base (placement (.inl 9)) = [])
    (suffix : List Bool) (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix)
    (ambient : A) :
    (advance (TM2.step program))^[steps graph vertex left right]
      (some ⟨some (labels (entry l r)), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph hl hr placement vertex left right base⟩ := by
  let afterLeft := wordTapes graph hl placement false vertex left base
  let afterBoth := wordTapes graph hr placement true vertex right afterLeft
  have leftFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h6 : j ≠ 6) :
      afterLeft (placement (.inl j)) = base (placement (.inl j)) :=
    wordTapes_role graph hl placement distinct false vertex left base j h2 h3 h4 h6
  have rightFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h7 : j ≠ 7) :
      afterBoth (placement (.inl j)) = afterLeft (placement (.inl j)) :=
    wordTapes_role graph hr placement distinct true vertex right afterLeft j h2 h3 h4 h7
  have bothFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4)
      (h6 : j ≠ 6) (h7 : j ≠ 7) :
      afterBoth (placement (.inl j)) = base (placement (.inl j)) :=
    (rightFrame j h2 h3 h4 h7).trans (leftFrame j h2 h3 h4 h6)
  have leftRun := PoweringMachineWord.wordTrace graph l
    (placement ∘ PoweringMachineTapes.wordPlacement hl false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective hl false)) vertex left
    (fun q => labels (.inl q))
    (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) program
    (fun q => atLabels (.inl q)) base
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_zero,
      PoweringMachineTapes.table] using tableWord)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_four,
      PoweringMachineTapes.scratch] using scratchEmpty)
    suffix (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_first,
      PoweringMachineTapes.start] using sourceWord)
    (ambient, false, none) none
  have rightTable : afterLeft (placement (.inl 0)) = PortTables.tableBits graph :=
    (leftFrame 0 (by decide) (by decide) (by decide) (by decide)).trans tableWord
  have rightScratch : afterLeft (placement (.inl 5)) = [] :=
    (leftFrame 5 (by decide) (by decide) (by decide) (by decide)).trans scratchEmpty
  have rightSource : afterLeft (placement (.inl 1)) = encodeWord vertex.val ++ suffix :=
    (leftFrame 1 (by decide) (by decide) (by decide) (by decide)).trans sourceWord
  have rightRun := PoweringMachineWord.wordTrace graph r
    (placement ∘ PoweringMachineTapes.wordPlacement hr true)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective hr true)) vertex right
    (fun q => labels (.inr (.inl q))) (some (labels (.inr (.inr .seedLeft)))) program
    (fun q => atLabels (.inr (.inl q))) afterLeft
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_zero,
      PoweringMachineTapes.table] using rightTable)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_four,
      PoweringMachineTapes.scratch] using rightScratch)
    suffix (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_first,
      PoweringMachineTapes.start] using rightSource)
    (ambient, false, none) none
  have leftEndpoint : afterBoth (placement (.inl 6)) =
      encodeWord (endpoint graph vertex left).val ++ base (placement (.inl 6)) := by
    rw [rightFrame 6 (by decide) (by decide) (by decide) (by decide)]
    dsimp only [afterLeft, wordTapes]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five,
      PoweringMachineTapes.endpoint_false, PoweringMachineTapes.leftEndpoint,
      wordTapes, endpoint] using leftRun.2
  have rightEndpoint : afterBoth (placement (.inl 7)) =
      encodeWord (endpoint graph vertex right).val ++ afterLeft (placement (.inl 7)) := by
    dsimp only [afterBoth, wordTapes]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five,
      PoweringMachineTapes.endpoint_true, PoweringMachineTapes.rightEndpoint,
      wordTapes, endpoint] using rightRun.2
  have copiesLeft : afterBoth (placement (.inl 8)) = [] :=
    (bothFrame 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans leftCopyEmpty
  have copiesRight : afterBoth (placement (.inl 9)) = [] :=
    (bothFrame 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans rightCopyEmpty
  have scratchBoth : afterBoth (placement (.inl 5)) = [] :=
    (bothFrame 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratchEmpty
  have equalityRun := MachineUnaryEqualityBit.equalityTrace
    (placement ∘ PoweringMachineTapes.equalityPlacement max)
    (distinct.comp (PoweringMachineTapes.equalityPlacement_injective max))
    (fun q => labels (.inr (.inr q))) exit program (fun q => atLabels (.inr (.inr q)))
    afterBoth (endpoint graph vertex left).val (endpoint graph vertex right).val
    (base (placement (.inl 6))) (afterLeft (placement (.inl 7)))
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_zero,
      PoweringMachineTapes.leftEndpoint] using leftEndpoint)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_one,
      PoweringMachineTapes.rightEndpoint] using rightEndpoint)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_two,
      PoweringMachineTapes.leftCopy] using copiesLeft)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_three,
      PoweringMachineTapes.rightCopy] using copiesRight)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_four,
      PoweringMachineTapes.scratch] using scratchBoth)
    ambient
  have joined := joinTrace_inline_PoweringMachineEqualityField (joinTrace_inline_PoweringMachineEqualityField leftRun.1 rightRun.1) equalityRun
  simpa only [steps, entry, MachineUnaryEqualityBit.clean, Function.comp_apply,
    PoweringMachineTapes.equalityPlacement_five, PoweringMachineTapes.rowOutput,
    finalTapes, resultBit, Fin.ext_iff,
    afterLeft, afterBoth, wordTapes] using joined

def fieldInTime (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ q, program (labels q) = instruction hl hr placement left right labels exit q)
    (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits graph)
    (scratchEmpty : base (placement (.inl 5)) = [])
    (leftCopyEmpty : base (placement (.inl 8)) = [])
    (rightCopyEmpty : base (placement (.inl 9)) = [])
    (suffix : List Bool) (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix)
    (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry l r)), MachineUnaryEqualityBit.clean ambient, base⟩
      (some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph hl hr placement vertex left right base⟩)
      ((14 * (l + r) + 10) * (PortTables.tableBits graph).length + 12 * (l + r) + 15) where
  steps := steps graph vertex left right
  evals_in_steps := fieldTrace graph hl hr placement distinct vertex left right labels exit program
    atLabels base tableWord scratchEmpty leftCopyEmpty rightCopyEmpty suffix sourceWord ambient
  steps_le_m := steps_le graph vertex left right

def machine (degree : Nat) (hl : l ≤ max) (hr : r ≤ max)
    (left : Fin l → Fin degree) (right : Fin r → Fin degree) : FinTM2 where
  K := Tape max
  k₀ := .inl 0
  k₁ := .inl 10
  Γ _ := Bool
  Λ := Label l r
  main := entry l r
  σ := State Unit
  initialState := MachineUnaryEqualityBit.clean ()
  m := instruction hl hr id left right id none

end MaxCutGames.Foundations.Complexity.PoweringMachineEqualityField

end OAI
