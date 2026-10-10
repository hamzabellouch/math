import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas
import OAI.Computability.UniqueGames.Reduction.EncodingLemmas
import OAI.Computability.UniqueGames.Reduction.OuterCompletenessLemmas
import OAI.Computability.UniqueGames.Reduction.RealTargetLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.OutputTranslations

open Integration.BinaryLinear
open ActualSource
open Foundations.Target

/-- A forward table translates every binary vector by the same offset sum. -/
theorem translationTable_vector {s : Nat} (a b x : Vector s) :
    (Encoding.translationTable a b).images[Encoding.alphabetEquiv s x] =
      Encoding.alphabetEquiv s (x + (a + b)) := by
  simpa only [add_assoc] using Encoding.translationTable_images a b x

/-- The same law on every numbered alphabet label, in fixed vector coordinates. -/
theorem translationTable_coordinates {s : Nat} (a b : Vector s) (label : Fin (2^s)) :
    (Encoding.alphabetEquiv s).symm ((Encoding.translationTable a b).images[label]) =
      (Encoding.alphabetEquiv s).symm label + (a + b) := by
  have h := translationTable_vector a b ((Encoding.alphabetEquiv s).symm label)
  simpa only [Encoding.alphabetEquiv_apply_symm_apply,
    Encoding.alphabetEquiv_symm_apply_apply] using
    congrArg (Encoding.alphabetEquiv s).symm h

/-- Every actual explicit edge has a concrete translation vector. -/
theorem explicitEdge_vector (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    ∃ shift : Vector s, ∀ x : Vector s,
      (ActualGame.explicitEdge S k g ω).permutation.images[Encoding.alphabetEquiv s x] =
        Encoding.alphabetEquiv s (x + shift) := by
  refine ⟨ActualGame.offset S k s d (ActualGame.leftQuery S k g ω) +
    ActualGame.offset S k s d (ActualGame.rightQuery S k g ω), ?_⟩
  intro x
  exact translationTable_vector _ _ x

theorem explicitEdge_coordinates (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    ∃ shift : Vector s, ∀ label : Fin (2^s),
      (Encoding.alphabetEquiv s).symm
          ((ActualGame.explicitEdge S k g ω).permutation.images[label]) =
        (Encoding.alphabetEquiv s).symm label + shift := by
  refine ⟨ActualGame.offset S k s d (ActualGame.leftQuery S k g ω) +
    ActualGame.offset S k s d (ActualGame.rightQuery S k g ω), ?_⟩
  intro label
  exact translationTable_coordinates _ _ label

/-- All emitted occurrences, including parallel edges and repeated noise values,
use translations in the same alphabet coordinates. -/
theorem outputInstanceWithEnumeration_vector (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    ∀ constraint ∈ (ActualGame.outputInstanceWithEnumeration S k g en).constraints,
      ∃ shift : Vector s, ∀ x : Vector s,
        constraint.permutation.images[Encoding.alphabetEquiv s x] =
          Encoding.alphabetEquiv s (x + shift) := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  exact explicitEdge_vector S k g ω

theorem outputInstanceWithEnumeration_coordinates (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    ∀ constraint ∈ (ActualGame.outputInstanceWithEnumeration S k g en).constraints,
      ∃ shift : Vector s, ∀ label : Fin (2^s),
        (Encoding.alphabetEquiv s).symm (constraint.permutation.images[label]) =
          (Encoding.alphabetEquiv s).symm label + shift := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  exact explicitEdge_coordinates S k g ω

/-- Erasing the correcting-map witness leaves the translation promise intact. -/
theorem tableOutput_vector (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    ∀ constraint ∈ (Integration.TableReduction.output S k T).constraints,
      ∃ shift : Vector s, ∀ x : Vector s,
        constraint.permutation.images[Encoding.alphabetEquiv s x] =
          Encoding.alphabetEquiv s (x + shift) :=
  outputInstanceWithEnumeration_vector S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

theorem tableOutput_coordinates (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    ∀ constraint ∈ (Integration.TableReduction.output S k T).constraints,
      ∃ shift : Vector s, ∀ label : Fin (2^s),
        (Encoding.alphabetEquiv s).symm (constraint.permutation.images[label]) =
          (Encoding.alphabetEquiv s).symm label + shift :=
  outputInstanceWithEnumeration_coordinates S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

theorem uniformOutput_vector {n s d : Nat}
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) (k : Nat)
    (T : Integration.NoiseTables.Table s d) :
    ∀ constraint ∈ (UniformReduction.output es hne k T).constraints,
      ∃ shift : Vector s, ∀ x : Vector s,
        constraint.permutation.images[Encoding.alphabetEquiv s x] =
          Encoding.alphabetEquiv s (x + shift) :=
  tableOutput_vector (UniformReduction.source es hne) k T

theorem uniformOutput_coordinates {n s d : Nat}
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) (k : Nat)
    (T : Integration.NoiseTables.Table s d) :
    ∀ constraint ∈ (UniformReduction.output es hne k T).constraints,
      ∃ shift : Vector s, ∀ label : Fin (2^s),
        (Encoding.alphabetEquiv s).symm (constraint.permutation.images[label]) =
          (Encoding.alphabetEquiv s).symm label + shift :=
  tableOutput_coordinates (UniformReduction.source es hne) k T

end UniqueGamesTheorem.Reduction.OutputTranslations

end

section

/-! Executable direct addresses for the actual canonical game. Every original
edge occurrence and its translation table is retained, in the same order.
Addresses not representing realized bodies are isolated vertices. No vertex
list, duplicate removal, or inverse enumeration is evaluated by the output. -/

namespace UniqueGamesTheorem.Reduction.AddressGame

open ActualSource
open Foundations.Target
open Integration.VertexEmbedding

abbrev bodyCapacity (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.variables S.occurrences k s d

def vertexCount (S : Source) (k s d : Nat) : Nat := 2 * bodyCapacity S k s d

/-- Both bipartite sides remain distinct address blocks. -/
def vertexAddress (S : Source) (k s d : Nat) (v : ActualGame.TwoSidedVertex S k s d) :
    Fin (vertexCount S k s d) :=
  Encoding.sideEquiv (bodyCapacity S k s d) (v.1, CanonicalAddress.bodyAddress v.2.val)

theorem vertexAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (vertexAddress S k s d) := by
  intro v w h
  have hp := (Encoding.sideEquiv (bodyCapacity S k s d)).injective h
  apply Prod.ext
  · exact congrArg (fun p : Bool × Fin (bodyCapacity S k s d) => p.1) hp
  · apply Subtype.ext
    exact CanonicalAddress.bodyAddress_injective
      (congrArg (fun p : Bool × Fin (bodyCapacity S k s d) => p.2) hp)

/-- This is the endpoint routine used at runtime: canonicalize, serialize,
apply Horner radix arithmetic, and add the side block. -/
def queryAddress (S : Source) (k s d : Nat) (side : Bool) (q : ActualGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  Encoding.sideEquiv (bodyCapacity S k s d)
    (side, CanonicalAddress.bodyAddress (ActualOrbit.body (ActualGame.canonical S k s d) q))

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat) (side : Bool)
    (q : ActualGame.Query S k s d) :
    vertexAddress S k s d (side, ActualGame.vertex S k s d q) =
      queryAddress S k s d side q := rfl

/-- Proof adapter only: the output constructor does not call this inverse. -/
def explicitToAddress (S : Source) (k s d : Nat) :
    Fin (ActualGame.explicitVertexCount S k s d) → Fin (vertexCount S k s d) :=
  fun i => vertexAddress S k s d ((ActualGame.explicitVertexEncoding S k s d).symm i)

theorem explicitToAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (explicitToAddress S k s d) :=
  (vertexAddress_injective S k s d).comp (ActualGame.explicitVertexEncoding S k s d).symm.injective

@[simp] theorem explicitToAddress_apply (S : Source) (k s d : Nat)
    (v : ActualGame.TwoSidedVertex S k s d) :
    explicitToAddress S k s d (ActualGame.explicitVertexEncoding S k s d v) =
      vertexAddress S k s d v := by
  simp only [explicitToAddress, Equiv.symm_apply_apply]

/-- The corresponding injection from the original semantic vertex space. -/
noncomputable def semanticToAddress (S : Source) (k s d : Nat) :
    Fin (ActualGame.vertexCount S k s d) → Fin (vertexCount S k s d) :=
  fun i => vertexAddress S k s d ((ActualGame.vertexEncoding S k s d).symm i)

theorem semanticToAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (semanticToAddress S k s d) :=
  (vertexAddress_injective S k s d).comp (ActualGame.vertexEncoding S k s d).symm.injective

@[simp] theorem semanticToAddress_apply (S : Source) (k s d : Nat)
    (v : ActualGame.TwoSidedVertex S k s d) :
    semanticToAddress S k s d (ActualGame.vertexEncoding S k s d v) =
      vertexAddress S k s d v := by
  simp only [semanticToAddress, Equiv.symm_apply_apply]

def addressEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : ActualGame.Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := queryAddress S k s d false (ActualGame.leftQuery S k g ω)
  target := queryAddress S k s d true (ActualGame.rightQuery S k g ω)
  permutation := Encoding.translationTable
    (ActualGame.offset S k s d (ActualGame.leftQuery S k g ω))
    (ActualGame.offset S k s d (ActualGame.rightQuery S k g ω))

theorem addressEdge_eq_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    addressEdge S k g ω = embedConstraint (explicitToAddress S k s d)
      (ActualGame.explicitEdge S k g ω) := by
  simp only [addressEdge, embedConstraint, ActualGame.explicitEdge,
    explicitToAddress_apply, vertexAddress_query]

theorem addressEdge_eq_semantic_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    addressEdge S k g ω = embedConstraint (semanticToAddress S k s d)
      (ActualGame.edge S k g ω) := by
  simp only [addressEdge, embedConstraint, ActualGame.edge,
    semanticToAddress_apply, vertexAddress_query]

@[simp] theorem addressEdge_permutation (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    (addressEdge S k g ω).permutation = (ActualGame.explicitEdge S k g ω).permutation := rfl

/-- Only canonical words, bounded radix arithmetic, and the explicit outcome
list occur in the runtime path. The correcting function is not inspected. -/
def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (addressEdge S k g)
  nonempty h := by
    have hempty := List.map_eq_nil_iff.mp h
    apply (ActualGame.outputInstanceWithEnumeration S k g en).nonempty
    change (ActualGame.explicitOutcomes S k g en).map (ActualGame.explicitEdge S k g) = []
    rw [hempty]
    rfl

/-- An exact instance equality, retaining the explicit edge-list order. -/
theorem outputInstance_eq_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    outputInstance S k g en =
      embedInstance (ActualGame.outputInstanceWithEnumeration S k g en)
        (explicitToAddress S k s d) (explicitToAddress_injective S k s d) := by
  unfold outputInstance embedInstance ActualGame.outputInstanceWithEnumeration
  congr 1
  simp only [List.map_map, Function.comp_def, ← addressEdge_eq_embed]

@[simp] theorem outputInstance_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstance S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstance, List.length_map, ActualGame.explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

theorem outputInstance_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g en).constraints =
      countSatisfied (labeling ∘ explicitToAddress S k s d)
        (ActualGame.outputInstanceWithEnumeration S k g en).constraints := by
  simpa only [outputInstance, ActualGame.outputInstanceWithEnumeration, List.map_map,
    Function.comp_def, ← addressEdge_eq_embed] using
    count_map (explicitToAddress S k s d)
      ((ActualGame.explicitOutcomes S k g en).map (ActualGame.explicitEdge S k g)) labeling

theorem completeAt_outputInstance_iff_explicit (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    CompleteAt error (outputInstance S k g en) ↔
      CompleteAt error (ActualGame.outputInstanceWithEnumeration S k g en) := by
  rw [outputInstance_eq_embed]
  exact completeAt_embed_iff error _ _ _ (by positivity)

theorem soundAt_outputInstance_iff_explicit (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    SoundAt error (outputInstance S k g en) ↔
      SoundAt error (ActualGame.outputInstanceWithEnumeration S k g en) := by
  rw [outputInstance_eq_embed]
  exact soundAt_embed_iff error _ _ _ (by positivity)

theorem completeAt_outputInstance_iff (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    CompleteAt error (outputInstance S k g en) ↔ CompleteAt error (ActualGame.outputInstance S k g) :=
  (completeAt_outputInstance_iff_explicit error S k g en).trans
    (ActualGame.completeAt_outputInstanceWithEnumeration_iff error S k g en)

theorem soundAt_outputInstance_iff (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    SoundAt error (outputInstance S k g en) ↔ SoundAt error (ActualGame.outputInstance S k g) :=
  (soundAt_outputInstance_iff_explicit error S k g en).trans
    (ActualGame.soundAt_outputInstanceWithEnumeration_iff error S k g en)

theorem outputInstance_translations (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (outputInstance S k g en) := by
  rw [outputInstance_eq_embed]
  exact (isTranslationInstance_embed_iff (Encoding.alphabetEquiv s).symm
    (ActualGame.outputInstanceWithEnumeration S k g en) (explicitToAddress S k s d)
    (explicitToAddress_injective S k s d)).2
    (OutputTranslations.outputInstanceWithEnumeration_coordinates S k g en)

/-- The concrete vector-table interface contains no correcting-map witness. -/
def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

theorem completeAt_tableOutput_iff (error : RationalError) (S : Source) (k : Nat)
    {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    CompleteAt error (tableOutput S k T) ↔ CompleteAt error (Integration.TableReduction.output S k T) :=
  completeAt_outputInstance_iff_explicit error S k _ _

theorem soundAt_tableOutput_iff (error : RationalError) (S : Source) (k : Nat)
    {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    SoundAt error (tableOutput S k T) ↔ SoundAt error (Integration.TableReduction.output S k T) :=
  soundAt_outputInstance_iff_explicit error S k _ _

theorem tableOutput_translations (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm (tableOutput S k T) :=
  outputInstance_translations S k _ _

/-- Exact polynomial bound for the complete two-sided address space. -/
theorem vertexCount_eq_polynomial (S : Source) (k s d : Nat) :
    vertexCount S k s d = 2 * (CanonicalAddress.capacityPolynomial k s d).eval
      (S.variables + S.occurrences) := by
  rw [CanonicalAddress.capacityPolynomial_eval]
  rfl

end UniqueGamesTheorem.Reduction.AddressGame

end

section

namespace UniqueGamesTheorem.Reduction.AddressByteSemantics

open Integration.BinaryLinear Foundations.Complexity ActualSource

def queryWords {k s d : Nat} (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) : List Nat :=
  CanonicalBodyTemplate.evalTemplate fields
    (CanonicalBodyTemplate.template (X (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple X) b)

def queryRank {k s d : Nat} (base : Nat) (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) : Nat :=
  CanonicalAddress.radix base (queryWords fields X b)

def permutationWords {k s d : Nat} (X Y : ActualGame.Map k s d)
    (b : Fin k → F2) : List Nat :=
  tableWords (Encoding.translationTable
    (CanonicalBodyTemplate.alphabetOffset (X (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple X) b)
    (CanonicalBodyTemplate.alphabetOffset (Y (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple Y) b))

def edgeWords {k s d : Nat} (base capacity : Nat) (fields : Fin k → Fin 4 → Nat)
    (X Y : ActualGame.Map k s d) (b : Fin k → F2) : List Nat :=
  [queryRank base fields X b, capacity + queryRank base fields Y b] ++
    permutationWords X Y b

def edgeBits {k s d : Nat} (base capacity : Nat) (fields : Fin k → Fin 4 → Nat)
    (X Y : ActualGame.Map k s d) (b : Fin k → F2) : List Bool :=
  encodeWords (edgeWords base capacity fields X Y b)

@[simp] theorem queryWords_length {k s d : Nat} (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) :
    (queryWords fields X b).length = 1 + 9*k := by
  simp only [queryWords, CanonicalBodyTemplate.evalTemplate, List.length_map,
    CanonicalBodyTemplate.template_length]

@[simp] theorem permutationWords_length {k s d : Nat} (X Y : ActualGame.Map k s d)
    (b : Fin k → F2) : (permutationWords X Y b).length = 2^s :=
  tableWords_length _

theorem queryWords_actual (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    queryWords (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) =
      CanonicalEncoding.bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q) :=
  CanonicalBodyTemplate.eval_actualQuery S q

theorem queryAddress_false (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d false q).val =
      queryRank (CanonicalAddress.base S.variables S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_false_val _

theorem queryAddress_true (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d true q).val =
      AddressGame.bodyCapacity S k s d +
      queryRank (CanonicalAddress.base S.variables S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_true_val _

/-- Exact full serialized edge, including every forward permutation image. -/
theorem addressEdge_words (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    constraintWords (AddressGame.addressEdge S k g omega) =
      edgeWords (CanonicalAddress.base S.variables S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  unfold constraintWords
  change [ (AddressGame.queryAddress S k s d false (ActualGame.leftQuery S k g omega)).val,
      (AddressGame.queryAddress S k s d true (ActualGame.rightQuery S k g omega)).val ] ++ _ = _
  rw [queryAddress_false, queryAddress_true]
  rfl

theorem addressEdge_bits (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    encodeWords (constraintWords (AddressGame.addressEdge S k g omega)) =
      edgeBits (CanonicalAddress.base S.variables S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  rw [addressEdge_words]
  rfl

/-- The actual edge emitter's three payloads concatenate to the codec exactly. -/
theorem edgeBits_split {k s d : Nat} (base capacity : Nat)
    (fields : Fin k → Fin 4 → Nat) (X Y : ActualGame.Map k s d) (b : Fin k → F2) :
    edgeBits base capacity fields X Y b =
      encodeWords [queryRank base fields X b, capacity + queryRank base fields Y b] ++
        encodeWords (permutationWords X Y b) := by
  exact encodeWords_append _ _

end UniqueGamesTheorem.Reduction.AddressByteSemantics

end

end OAI
