import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas
import OAI.Computability.UniqueGames.Reduction.FixedOutcomes
import OAI.Computability.UniqueGames.Reduction.MachineAddressEdgeLemmas
import OAI.Computability.UniqueGames.Reduction.OutputTranslationsLemmas

namespace OAI


namespace UniqueGamesTheorem.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

abbrev Spec (k : Nat) := MachineOutcomeRows.Spec (4*k) (1+9*k)
abbrev Values (k : Nat) := MachineOutcomeRows.Values (1+9*k)
abbrev Parameter (k : Nat) {sourceDimension targetDimension : Nat}
    (T : NoiseTables.Table sourceDimension targetDimension) :=
  FixedOutcomes.Parameter k sourceDimension targetDimension (Fin T.vectors.length)

def bitVector {k : Nat} (b : Fin k → Bool) : Fin k → F2 := fun j => ofBit (b j)

def rightMap {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T) :
    ActualGame.Map k s d := p.1 + p.2.2.smulRight (T.vectors.get p.2.1)

def row {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) : Spec k where
  left := CanonicalBodyMachine.template (p.1 (ActualHomogeneous.hBasis k))
    (ActualCanonical.standardTriple p.1) (bitVector b)
  right := CanonicalBodyMachine.template (rightMap T p (ActualHomogeneous.hBasis k))
    (ActualCanonical.standardTriple (rightMap T p)) (bitVector b)
  permutation := encodeWords (AddressByteSemantics.permutationWords p.1 (rightMap T p) (bitVector b))

def rows (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    List (MachineOutcomeRows.Row k (4*k) (1+9*k)) :=
  (FixedOutcomes.tableParams k T).map (row T)

@[simp] theorem row_left_length {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) : (row T p b).left.length = 1+9*k :=
  CanonicalBodyMachine.template_length _ _ _

@[simp] theorem row_right_length {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) : (row T p b).right.length = 1+9*k :=
  CanonicalBodyMachine.template_length _ _ _

@[simp] theorem rows_length (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    (rows k T).length = 2^((2*k+1)*(s+d+1)) * T.vectors.length := by
  simp only [rows, List.length_map, FixedOutcomes.tableParams_length]

@[simp] theorem selected_rows (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (b : Fin k → Bool) :
    MachineOutcomeRows.selected (rows k T) b =
      (FixedOutcomes.tableParams k T).map (fun p => row T p b) := by
  simp only [MachineOutcomeRows.selected, rows, List.map_map, Function.comp_def]

/-- A total proof-side interpretation. The fallback handles arbitrary malformed
static specs; actual canonical rows always take the checked decoding branch. -/
def interpreted (width : Nat) (bits : List Bool) : {words : List Nat // words.length = width} :=
  let words := (decodeWords bits).getD []
  if h : words.length = width then ⟨words, h⟩
  else ⟨List.replicate width 0, List.length_replicate⟩

theorem interpreted_encoded (width : Nat) (words : List Nat) (hlen : words.length = width) :
    (interpreted width (encodeWords words)).val = words := by
  simp [interpreted, hlen]

def values {k : Nat} (fields : Fin k → Fin 4 → Nat) (spec : Spec k) : Values k where
  left := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields))).val
  right := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields))).val
  left_length := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields))).property
  right_length := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields))).property

theorem row_left_output {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    MachineFieldTemplate.templateOutput (row T p b).left (CanonicalBodyMachine.savedFields fields) =
      encodeWords (AddressByteSemantics.queryWords fields p.1 (bitVector b)) :=
  CanonicalBodyMachine.templateOutput_lowerTemplate fields _

theorem row_right_output {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    MachineFieldTemplate.templateOutput (row T p b).right (CanonicalBodyMachine.savedFields fields) =
      encodeWords (AddressByteSemantics.queryWords fields (rightMap T p) (bitVector b)) :=
  CanonicalBodyMachine.templateOutput_lowerTemplate fields _

@[simp] theorem values_row_left {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    (values fields (row T p b)).left =
      AddressByteSemantics.queryWords fields p.1 (bitVector b) := by
  change (interpreted (1+9*k) _).val = _
  rw [row_left_output]
  exact interpreted_encoded _ _ (AddressByteSemantics.queryWords_length _ _ _)

@[simp] theorem values_row_right {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    (values fields (row T p b)).right =
      AddressByteSemantics.queryWords fields (rightMap T p) (bitVector b) := by
  change (interpreted (1+9*k) _).val = _
  rw [row_right_output]
  exact interpreted_encoded _ _ (AddressByteSemantics.queryWords_length _ _ _)

theorem correct_rows {k s d : Nat} (T : NoiseTables.Table s d)
    (fields : Fin k → Fin 4 → Nat) (b : Fin k → Bool) :
    ∀ spec ∈ MachineOutcomeRows.selected (rows k T) b,
      MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields) =
        encodeWords (values fields spec).left ∧
      MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields) =
        encodeWords (values fields spec).right := by
  rw [selected_rows]
  intro spec hspec
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hspec
  constructor
  · rw [values_row_left]
    exact row_left_output T p b fields
  · rw [values_row_right]
    exact row_right_output T p b fields

theorem payload_row {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat)
    (B C : Nat) :
    MachineOutcomeRows.payload B C (values fields) (row T p b) =
      AddressByteSemantics.edgeBits B C fields p.1 (rightMap T p) (bitVector b) := by
  unfold MachineOutcomeRows.payload MachineAddressEdge.edgeBits
  rw [values_row_left, values_row_right, AddressByteSemantics.edgeBits_split]
  rfl

def rhsBits (S : Source) {k : Nat} (U : ActualGame.Question S k) : Fin k → Bool :=
  fun j => (S.equation (U j)).rhs

@[simp] theorem bitVector_rhsBits (S : Source) {k : Nat} (U : ActualGame.Question S k) :
    bitVector (rhsBits S U) = fun j => ActualGame.rhs S (U j) := rfl

theorem rightMap_actual (S : Source) {k s d : Nat} (T : NoiseTables.Table s d)
    (U : ActualGame.Question S k) (p : Parameter k T) :
    rightMap T p =
      (ActualGame.rightQuery S k (TableReduction.tableSkeleton T) (FixedOutcomes.assemble U p)).2 := rfl

/-- Each static row emits exactly the concrete game's constraint encoding. -/
theorem payload_row_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) (p : Parameter k T) :
    MachineOutcomeRows.payload
        (CanonicalAddress.base S.variables S.occurrences s d) (AddressGame.bodyCapacity S k s d)
        (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))
        (row T p (rhsBits S U)) =
      encodeWords (constraintWords (AddressGame.addressEdge S k (TableReduction.tableSkeleton T)
        (FixedOutcomes.assemble U p))) := by
  rw [payload_row, bitVector_rhsBits, rightMap_actual S T U p]
  exact (AddressByteSemantics.addressEdge_bits S k (TableReduction.tableSkeleton T)
    (FixedOutcomes.assemble U p)).symm

def tupleBits (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (U : ActualGame.Question S k) : List Bool :=
  (FixedOutcomes.tableParams k T).flatMap (fun p =>
    encodeWords (constraintWords (AddressGame.addressEdge S k (TableReduction.tableSkeleton T)
      (FixedOutcomes.assemble U p))))

theorem tuplePayload_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) :
    (MachineOutcomeRows.selected (rows k T) (rhsBits S U)).flatMap
        (MachineOutcomeRows.payload
          (CanonicalAddress.base S.variables S.occurrences s d) (AddressGame.bodyCapacity S k s d)
          (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))) =
      tupleBits S k T U := by
  rw [selected_rows, List.flatMap_map]
  simp only [payload_row_actual, tupleBits]
  rfl

private theorem encodeWords_flatMap {Item : Type*} (items : List Item)
    (words : Item → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons x items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

/-- Complete output-byte factorization used by the actual outer loop. -/
theorem gameBits_factor (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    gameBits (AddressGame.tableOutput S k T) =
      encodeWords [(AddressGame.tableOutput S k T).vertices, 2^s,
        (AddressGame.tableOutput S k T).constraints.length] ++
      (FixedOutcomes.occurrenceTuples S.occurrences k).flatMap (tupleBits S k T) := by
  rw [gameBits, gameWords, encodeWords_append, encodeWords_flatMap]
  rw [FixedOutcomes.tableOutput_constraints]
  erw [List.flatMap_assoc]
  congr 1
  apply List.flatMap_congr
  intro U _
  erw [List.flatMap_map]
  rfl

end UniqueGamesTheorem.Reduction.AddressOutcomeSpecs

end OAI
