import OAI.Computability.PerfectCompleteness.Foundations.DescriptorKeyTemplate
import OAI.Computability.PerfectCompleteness.Machines.CanonicalEndpointMachine
import OAI.Computability.PerfectCompleteness.Machines.DescriptorProjectionMachine

namespace OAI


namespace PerfectCompleteness.CompletedEdgeMachine


open Turing UniqueGamesTheorem.Foundations.Complexity
open CanonicalKeys
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t q : Nat} {rows repeats : Nat → Nat}
  (hq : 0 < q)
  (large : CanonicalKeyEncoding.partitionWidth (TreeCanonical.locationCount branch n t) ≤ q)

local notation "width" => TreeCanonical.locationCount branch n t

variable (descriptor : SignedCompletionSchedule.Descriptor
  (rows := rows) (repeats := repeats) hq large)

def key (side : Side) (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : Key width :=
  DescriptorKeyTemplate.recover side (DescriptorKeyTemplate.ofDescriptor hq large side descriptor)
    ids vars

def edge (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) :
    Edge (leftPrefix.length + 1) (rightPrefix.length + 1) q where
  left := CanonicalOnlineNames.onlineName leftPrefix (key hq large descriptor .left ids vars)
  right := CanonicalOnlineNames.onlineName rightPrefix (key hq large descriptor .right ids vars)
  projection := DescriptorProjectionMachine.projection hq large descriptor

def edgeBits (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : List Bool :=
  encodeWords (Encoding.edgeWords (edge hq large descriptor leftPrefix rightPrefix ids vars))

theorem edgeBits_eq (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) :
    edgeBits hq large descriptor leftPrefix rightPrefix ids vars =
      encodeWord (CanonicalOnlineNames.onlineID leftPrefix (key hq large descriptor .left ids vars)) ++
      encodeWord (CanonicalOnlineNames.onlineID rightPrefix (key hq large descriptor .right ids vars)) ++
      DescriptorProjectionMachine.outputBits hq large descriptor := by
  simp only [edgeBits, edge, Encoding.edgeWords, CanonicalOnlineNames.onlineName_val,
    encodeWords_append, encodeWords, List.append_nil, DescriptorProjectionMachine.outputBits,
    DescriptorProjectionMachine.outputWords, List.append_assoc]

def leftMap (i : Fin 8) : Fin 10 := ⟨i.val, lt_trans i.isLt (by decide)⟩

def rightMap (i : Fin 8) : Fin 10 := if i = 1 then 8 else leftMap i

theorem leftMap_injective : Function.Injective leftMap := by decide
theorem rightMap_injective : Function.Injective rightMap := by decide

theorem forward_ne_left : ∀ i, (9 : Fin 10) ≠ leftMap i := by decide
theorem forward_ne_right : ∀ i, (9 : Fin 10) ≠ rightMap i := by decide

private theorem leftMap_work : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 →
    leftMap i ≠ 1 ∧ leftMap i ≠ 7 ∧ leftMap i ≠ 8 := by decide

private theorem rightMap_work : ∀ i : Fin 8, 2 ≤ i.val → i.val ≤ 6 →
    rightMap i ≠ 1 ∧ rightMap i ≠ 7 ∧ rightMap i ≠ 8 := by decide

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := CanonicalEndpointMachine.State A
abbrev clean (ambient : A) : State A := CanonicalEndpointMachine.clean ambient

def leftTapes (work : Fin 10 → K) : Fin 8 → K := fun i => work (leftMap i)
def rightTapes (work : Fin 10 → K) : Fin 8 → K := fun i => work (rightMap i)

inductive Label (locations : Nat)
  | left (label : CanonicalEndpointMachine.Label locations)
  | right (label : CanonicalEndpointMachine.Label locations)
  | projection
  deriving DecidableEq, Fintype

def main (locations : Nat) : Label locations := .left (CanonicalEndpointMachine.main locations)

variable [Fintype A] [DecidableEq A]

def instruction (source : Fin width → Fin 6 → K) (work : Fin 10 → K)
    (labels : Label width → Λ) (done : Λ) (rejected : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .left label =>
      let template := DescriptorKeyTemplate.ofDescriptor hq large .left descriptor
      CanonicalEndpointMachine.instruction template.shapes template.modes .left template.partition
        source (work 9) (leftTapes work) (fun l => labels (.left l))
        (some (labels (.right (CanonicalEndpointMachine.main width)))) rejected label
  | .right label =>
      let template := DescriptorKeyTemplate.ofDescriptor hq large .right descriptor
      CanonicalEndpointMachine.instruction template.shapes template.modes .right template.partition
        source (work 9) (rightTapes work) (fun l => labels (.right l))
        (some (labels .projection)) rejected label
  | .projection =>
      DescriptorProjectionMachine.reverseStatement hq large
        (fun _ : State A => descriptor) (work 7) done

def finalTapes (work : Fin 10 → K) (base : K → List Bool)
    (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update base (work 1) (BinaryNameSearch.stream (CanonicalVertexNames.tokens
        (leftPrefix ++ [key hq large descriptor .left ids vars]))))
      (work 8) (BinaryNameSearch.stream (CanonicalVertexNames.tokens
        (rightPrefix ++ [key hq large descriptor .right ids vars]))))
    (work 7) ((edgeBits hq large descriptor leftPrefix rightPrefix ids vars).reverse ++ base (work 7))

def budget (source : Fin width → Fin 6 → K) (base : K → List Bool)
    (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) : Nat :=
  CanonicalEndpointMachine.budget source base leftPrefix (key hq large descriptor .left ids vars) +
    CanonicalEndpointMachine.budget source base rightPrefix (key hq large descriptor .right ids vars) + 1

def edgeInTime (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat)
    (source : Fin width → Fin 6 → K) (sourceDistinct : ∀ i, Function.Injective (source i))
    (work : Fin 10 → K) (workDistinct : Function.Injective work)
    (sharedScratch : ∀ i, source i 4 = work 5) (sharedOutput : ∀ i, source i 5 = work 9)
    (sourceAvoid : ∀ i field j, KeyMetadataMachine.idTape (source i) field ≠ work j)
    (labels : Label width → Λ) (done : Λ) (rejected : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction hq large descriptor source work labels done rejected l)
    (base : K → List Bool) (ambient : A) (leftPrefix rightPrefix : List (Key width))
    (sourceWords : ∀ i field, base (KeyMetadataMachine.idTape (source i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids i) (vars i) field))
    (leftDictionary : base (work 1) = BinaryNameSearch.stream (CanonicalVertexNames.tokens leftPrefix))
    (rightDictionary : base (work 8) = BinaryNameSearch.stream (CanonicalVertexNames.tokens rightPrefix))
    (empty : ∀ j : Fin 10, j ≠ 1 → j ≠ 7 → j ≠ 8 → base (work j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (main width)), clean ambient, base⟩
      (some ⟨some done, clean ambient,
        finalTapes hq large descriptor work base leftPrefix rightPrefix ids vars⟩)
      (budget hq large descriptor source base leftPrefix rightPrefix ids vars) := by
  let leftKey := key hq large descriptor .left ids vars
  let rightKey := key hq large descriptor .right ids vars
  let leftTemplate := DescriptorKeyTemplate.ofDescriptor hq large .left descriptor
  let rightTemplate := DescriptorKeyTemplate.ofDescriptor hq large .right descriptor
  let first := CanonicalEndpointMachine.finalTapes (leftTapes work) base leftPrefix leftKey
  let second := CanonicalEndpointMachine.finalTapes (rightTapes work) first rightPrefix rightKey
  have hd (i j : Fin 10) (different : i ≠ j) : work i ≠ work j :=
    fun same => different (workDistinct same)
  have leftEmpty (i : Fin 8) (lo : 2 ≤ i.val) (hi : i.val ≤ 6) :
      base (leftTapes work i) = [] := by
    obtain ⟨h1, h7, h8⟩ := leftMap_work i lo hi
    exact empty (leftMap i) h1 h7 h8
  have leftRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (main width)), clean ambient, base⟩
      (some ⟨some (labels (.right (CanonicalEndpointMachine.main width))), clean ambient, first⟩)
      (CanonicalEndpointMachine.budget source base leftPrefix leftKey) := by
    exact CanonicalEndpointMachine.endpointInTime
      leftTemplate.shapes leftTemplate.modes .left leftTemplate.partition ids vars
      source sourceDistinct (work 9) (leftTapes work)
      (workDistinct.comp leftMap_injective)
      (fun i same => forward_ne_left i (workDistinct same)) sharedScratch sharedOutput
      (fun l => labels (.left l)) (some (labels (.right (CanonicalEndpointMachine.main width))))
      rejected program (fun l => atLabels (.left l)) base ambient leftPrefix sourceWords
      (empty 9 (by decide) (by decide) (by decide))
      (empty 0 (by decide) (by decide) (by decide)) leftDictionary leftEmpty
  have firstAt (i : Fin 10) (h1 : i ≠ 1) (h7 : i ≠ 7) : first (work i) = base (work i) :=
    CanonicalEndpointMachine.finalTapes_frame (leftTapes work) base leftPrefix leftKey
      (work i) (hd i 1 h1) (hd i 7 h7)
  have firstSource (i : Fin width) (field : Fin 4) :
      first (KeyMetadataMachine.idTape (source i) field) =
        base (KeyMetadataMachine.idTape (source i) field) :=
    CanonicalEndpointMachine.finalTapes_sources source (leftTapes work) base leftPrefix leftKey
      (fun i field => sourceAvoid i field 1) (fun i field => sourceAvoid i field 7) i field
  have rightEmpty (i : Fin 8) (lo : 2 ≤ i.val) (hi : i.val ≤ 6) :
      first (rightTapes work i) = [] := by
    obtain ⟨h1, h7, h8⟩ := rightMap_work i lo hi
    exact (firstAt (rightMap i) h1 h7).trans (empty (rightMap i) h1 h7 h8)
  have firstSourceLength : CanonicalKeyMachine.sourceLength source first =
      CanonicalKeyMachine.sourceLength source base := by
    simp only [CanonicalKeyMachine.sourceLength, KeyMetadataMachine.sourceLength, firstSource]
  have rightRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.right (CanonicalEndpointMachine.main width))), clean ambient, first⟩
      (some ⟨some (labels .projection), clean ambient, second⟩)
      (CanonicalEndpointMachine.budget source base rightPrefix rightKey) := by
    have run := CanonicalEndpointMachine.endpointInTime
      rightTemplate.shapes rightTemplate.modes .right rightTemplate.partition ids vars
      source sourceDistinct (work 9) (rightTapes work)
      (workDistinct.comp rightMap_injective)
      (fun i same => forward_ne_right i (workDistinct same)) sharedScratch sharedOutput
      (fun l => labels (.right l)) (some (labels .projection)) rejected program
      (fun l => atLabels (.right l)) first ambient rightPrefix
      (fun i field => (firstSource i field).trans (sourceWords i field))
      ((firstAt 9 (by decide) (by decide)).trans (empty 9 (by decide) (by decide) (by decide)))
      ((firstAt 0 (by decide) (by decide)).trans (empty 0 (by decide) (by decide) (by decide)))
      ((firstAt 8 (by decide) (by decide)).trans rightDictionary) rightEmpty
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.right (CanonicalEndpointMachine.main width))), clean ambient, first⟩
      (some ⟨some (labels .projection), clean ambient, second⟩)
      (CanonicalEndpointMachine.budget source first rightPrefix rightKey) at run
    simpa only [CanonicalEndpointMachine.budget, firstSourceLength] using run
  have projectionRun := DescriptorProjectionMachine.reverseEmitInTime hq large
    (fun _ : State A => descriptor) (work 7) program (labels .projection) done
    (atLabels .projection) (clean ambient) second
  have finalEq : Function.update second (work 7)
      ((DescriptorProjectionMachine.outputBits hq large descriptor).reverse ++ second (work 7)) =
      finalTapes hq large descriptor work base leftPrefix rightPrefix ids vars := by
    funext k
    by_cases hk : k = work 7
    · subst k
      simp [first, second, finalTapes, CanonicalEndpointMachine.finalTapes,
        edgeBits_eq, leftKey, rightKey, leftTapes, rightTapes, leftMap, rightMap,
        List.reverse_append, List.append_assoc]
    · simp [first, second, finalTapes, CanonicalEndpointMachine.finalTapes,
        leftKey, rightKey, leftTapes, rightTapes, leftMap, rightMap,
        Function.update_apply, hk]
  rw [finalEq] at projectionRun
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ leftRun rightRun) projectionRun
  simpa only [budget, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem finalTapes_frame (work : Fin 10 → K) (base : K → List Bool)
    (leftPrefix rightPrefix : List (Key width))
    (ids : Fin width → Nat) (vars : Fin width → Fin 3 → Nat) (k : K)
    (notLeft : k ≠ work 1) (notRight : k ≠ work 8) (notOutput : k ≠ work 7) :
    finalTapes hq large descriptor work base leftPrefix rightPrefix ids vars k = base k := by
  simp only [finalTapes, Function.update_of_ne notOutput,
    Function.update_of_ne notRight, Function.update_of_ne notLeft]

theorem label_finite : Finite (Label width) := inferInstance
omit [Fintype A] [DecidableEq A] in
theorem state_finite [Finite A] : Finite (State A) := inferInstance
omit [DecidableEq K] in
theorem workAlphabet_finite (k : K) : Finite (Alphabet k) := inferInstance

end
end PerfectCompleteness.CompletedEdgeMachine

end OAI
