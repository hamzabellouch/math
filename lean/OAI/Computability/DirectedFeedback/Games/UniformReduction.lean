import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineOutcomeRows

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.UniformReduction

open ActualSource
open DFVSGames.Integration
open DFVSGames.Foundations.Target

variable {n s d : Nat}

def rawSource (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) : Source :=
  Source.ofList es hne

def source (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) : Source :=
  FiniteSource.cloned (rawSource es hne)

def output (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) : Instance (2 ^ s) :=
  TableReduction.output (source es hne) k T

def satisfaction (es : List (CloneGap.Equation (Fin n))) (A : Fin n → Bool) : ℚ :=
  (es.countP (fun e => CloneGap.satisfied e A) : ℚ) / es.length

theorem source_variables (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).«variables» = n * 48 := rfl

theorem source_occurrences (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).occurrences = es.length * CloneGap.distinctTriples.length := by
  exact FiniteSource.cloned_length (rawSource es hne)

theorem source_occurrences_le (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).occurrences ≤ 110592 * es.length := by
  have hd : CloneGap.distinctTriples.length ≤ 110592 := by
    exact Nat.le_trans (List.length_filter_le _ CloneGap.triples)
      (by simp [CloneGap.length_triples])
  rw [source_occurrences]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left es.length hd

theorem source_distinct (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).DistinctNames := FiniteSource.cloned_distinct (rawSource es hne)

theorem output_constraint_count (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (output es hne k T).constraints.length =
      (es.length * CloneGap.distinctTriples.length) ^ k *
        2 ^ ((2 * k + 1) * (s + d + 1)) * T.vectors.length := by
  unfold output TableReduction.output
  erw [ActualGame.outputInstanceWithEnumeration_length]
  simp only [TableReduction.tableEnumeration, source_occurrences, Explicit.edgeCount]
  erw [List.length_finRange]

theorem output_vertex_count (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (output es hne k T).vertices =
      2 * (ActualGame.explicitBodies (source es hne) k s d).length := rfl

def liftAssignment (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) : Fin (source es hne).«variables» → Bool :=
  fun z => A ((FiniteSource.nameEquiv (rawSource es hne)).symm z).1

theorem source_failure_preserved (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) :
    (source es hne).failure (liftAssignment es hne A) = (rawSource es hne).failure A :=
  Preprocessing.cloned_failure_eq (rawSource es hne) A

theorem raw_failure_add_satisfaction (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) :
    (rawSource es hne).failure A + satisfaction es A = 1 := by
  have h := SourceProbability.failure_add_satisfaction (rawSource es hne) A
  have hl : (rawSource es hne).sourceList = es := Source.sourceList_ofList es hne
  have ho : (rawSource es hne).occurrences = es.length := rfl
  rw [hl, ho] at h
  exact h

theorem source_complete (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hsource : ∃ A : Fin n → Bool, 1 - ξ ≤ satisfaction es A) :
    ∃ A : Fin (source es hne).«variables» → Bool, (source es hne).failure A ≤ ξ := by
  obtain ⟨A, hA⟩ := hsource
  refine ⟨liftAssignment es hne A, ?_⟩
  rw [source_failure_preserved]
  have hsum := raw_failure_add_satisfaction es hne A
  linarith

theorem raw_quarter_count_gap (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    ∀ A : Fin (rawSource es hne).«variables» → Bool,
      (rawSource es hne).sourceList.length ≤
        4 * (rawSource es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) := by
  intro A
  apply (SourceProbability.quarter_gap_iff (rawSource es hne) A).mp
  have hsum := raw_failure_add_satisfaction es hne A
  have hs := hsource A
  linarith

theorem source_sound (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    ∀ A : Fin (source es hne).«variables» → Bool,
      (1 / 64 : ℚ) ≤ (source es hne).failure A := by
  intro A
  have hgap := raw_quarter_count_gap es hne ξ hξ hsource
  have hc := FiniteSource.cloned_gap (rawSource es hne) hgap A
  change (source es hne).sourceList.length ≤
    64 * (source es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) at hc
  rw [SourceProbability.Source_failure_eq_count]
  have hn : (0 : ℚ) < (source es hne).occurrences := by
    exact_mod_cast (source es hne).nonempty
  apply (le_div_iff₀ hn).mpr
  rw [Source.sourceList_length] at hc
  have hc' : ((source es hne).occurrences : ℚ) ≤
      64 * ((source es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) := by
    exact_mod_cast hc
  linarith

theorem sourceGame_sound (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    (IncidenceProbability.FoundationBridge.sourceGame (source es hne)).value ≤
      (191 : ℝ) / 192 := by
  have h := IncidenceProbability.FoundationBridge.source_value_le_one_sub_gap_third
    (source es hne) (source_distinct es hne) (1 / 64 : ℝ) (fun A => by
      have hrat := source_sound es hne ξ hξ hsource A
      have hr : ((1 / 64 : ℚ) : ℝ) ≤ ((source es hne).failure A : ℝ) := by
        exact_mod_cast hrat
      norm_num at hr ⊢
      exact hr)
  norm_num at h ⊢
  exact h

theorem completeAt_of_parameters (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (error : RationalError) (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ FinalParameters.gamma (GapSemantics.errorValue error) k)
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (hstable : (T.gadget f hf).stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool, 1 - ξ ≤ satisfaction es A) :
    CompleteAt error (output es hne k T) := by
  obtain ⟨A, hA⟩ := source_complete es hne ξ hsource
  apply (TableReduction.completeAt_output_iff error (source es hne) k T f hf).mpr
  apply ActualCompleteness.actual_completeAt (source es hne) k (T.gadget f hf) A error
  have hm := mul_le_mul_of_nonneg_left (hA.trans hξ) (show (0 : ℚ) ≤ k by positivity)
  calc
    (k : ℚ) * (source es hne).failure A + (T.gadget f hf).stabilityError / 2 ≤
        (k : ℚ) * FinalParameters.gamma (GapSemantics.errorValue error) k +
          (GapSemantics.errorValue error / 2) / 2 := by linarith
    _ = GapSemantics.errorValue error / 2 := FinalParameters.completeness_budget hk
    _ ≤ GapSemantics.errorValue error := by
      have hpos := GapSemantics.errorValue_pos error
      linarith

end DFVSGames.Reduction.UniformReduction
end

section

namespace DFVSGames.Reduction.OutputTranslations

open Integration.BinaryLinear
open ActualSource
open Foundations.Target

theorem translationTable_vector {s : Nat} (a b x : Vector s) :
    (Encoding.translationTable a b).images[Encoding.alphabetEquiv s x] =
      Encoding.alphabetEquiv s (x + (a + b)) := by
  simpa only [add_assoc] using Encoding.translationTable_images a b x

theorem translationTable_coordinates {s : Nat} (a b : Vector s) (label : Fin (2^s)) :
    (Encoding.alphabetEquiv s).symm ((Encoding.translationTable a b).images[label]) =
      (Encoding.alphabetEquiv s).symm label + (a + b) := by
  have h := translationTable_vector a b ((Encoding.alphabetEquiv s).symm label)
  simpa only [Encoding.alphabetEquiv_apply_symm_apply,
    Encoding.alphabetEquiv_symm_apply_apply] using
    congrArg (Encoding.alphabetEquiv s).symm h

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

end DFVSGames.Reduction.OutputTranslations
end

section

namespace DFVSGames.Reduction.AddressGame

open ActualSource
open Foundations.Target
open Integration.VertexEmbedding

abbrev bodyCapacity (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.«variables» S.occurrences k s d

def vertexCount (S : Source) (k s d : Nat) : Nat := 2 * bodyCapacity S k s d

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

def queryAddress (S : Source) (k s d : Nat) (side : Bool) (q : ActualGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  Encoding.sideEquiv (bodyCapacity S k s d)
    (side, CanonicalAddress.bodyAddress (ActualOrbit.body (ActualGame.canonical S k s d) q))

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat) (side : Bool)
    (q : ActualGame.Query S k s d) :
    vertexAddress S k s d (side, ActualGame.vertex S k s d q) =
      queryAddress S k s d side q := rfl

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

theorem vertexCount_eq_polynomial (S : Source) (k s d : Nat) :
    vertexCount S k s d = 2 * (CanonicalAddress.capacityPolynomial k s d).eval
      (S.«variables» + S.occurrences) := by
  rw [CanonicalAddress.capacityPolynomial_eval]
  rfl

end DFVSGames.Reduction.AddressGame
end

section

namespace DFVSGames.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration _root_.OAI.DFVSGames.Reduction.Explicit

variable {N : Type*}

abbrev Parameter (k s d : Nat) (N : Type*) :=
  (E k →ₗ[F2] ActualEnumeration.Ambient s d) × (N × (E k →ₗ[F2] F2))

def occurrenceTuples (m k : Nat) : List (Fin k → Fin m) :=
  functions (List.finRange m) k

def fixedParams (k s d : Nat) (indices : List N) : List (Parameter k s d N) :=
  pairs (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

def assemble {m k s d : Nat} (U : Fin k → Fin m) (p : Parameter k s d N) :
    Query m k s d × (N × (E k →ₗ[F2] F2)) :=
  ((U, p.1), p.2)

def outcomeEquiv (m k s d : Nat) (N : Type*) :
    (Query m k s d × (N × (E k →ₗ[F2] F2))) ≃
      ((Fin k → Fin m) × Parameter k s d N) :=
  Equiv.prodAssoc _ _ _

private theorem pairs_associate_inline_FixedOutcomes {α β γ : Type*}
    (xs : List α) (ys : List β) (zs : List γ) :
    pairs (pairs xs ys) zs =
      xs.flatMap (fun x => (pairs ys zs).map (fun p => ((x, p.1), p.2))) := by
  simp only [pairs, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

theorem indexedOutcomes_factor (m k s d : Nat) (indices : List N) :
    ActualEnumeration.indexedOutcomes m k s d indices =
      (occurrenceTuples m k).flatMap (fun U => (fixedParams k s d indices).map (assemble U)) := by
  exact pairs_associate_inline_FixedOutcomes (functions (List.finRange m) k)
    (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

theorem indexedOutcomes_reassociate (m k s d : Nat) (indices : List N) :
    (ActualEnumeration.indexedOutcomes m k s d indices).map (outcomeEquiv m k s d N) =
      pairs (occurrenceTuples m k) (fixedParams k s d indices) := by
  rw [indexedOutcomes_factor]
  simp only [pairs, List.map_flatMap, List.map_map, Function.comp_def,
    assemble, outcomeEquiv, Equiv.prodAssoc_apply]

theorem occurrenceTuples_length (m k : Nat) : (occurrenceTuples m k).length = m^k := by
  simp only [occurrenceTuples, length_functions, List.length_finRange]

theorem fixedParams_length (k s d : Nat) (indices : List N) :
    (fixedParams k s d indices).length = 2^((2*k+1)*(s+d+1)) * indices.length := by
  simp only [fixedParams, length_pairs, length_allLinearMaps, length_ambientVectors,
    List.length_cons, List.length_nil, ← pow_mul]
  change 2^((s+d)*(2*k+1)) * (indices.length * 2^(2*k+1)) =
    2^((2*k+1)*(s+d+1)) * indices.length
  rw [show (2*k+1)*(s+d+1) = (s+d)*(2*k+1)+(2*k+1) by ring, pow_add]
  ring

theorem fixedParams_nonempty (k s d : Nat) {indices : List N} (hne : indices ≠ []) :
    fixedParams k s d indices ≠ [] := by
  apply List.length_pos_iff.mp
  rw [fixedParams_length]
  exact Nat.mul_pos (Nat.two_pow_pos _) (List.length_pos_iff.mpr hne)

abbrev CoefficientParameter (k s d : Nat) (N : Type*) :=
  Coefficients k (ActualEnumeration.Ambient s d) × (N × Coefficients k F2)

def coefficientValues {R : Type*} (k : Nat) (values : List R) : List (Coefficients k R) :=
  pairs values (functions (pairs values values) k)

def fixedCoefficientParams (k s d : Nat) (indices : List N) :
    List (CoefficientParameter k s d N) :=
  pairs (coefficientValues k (ambientVectors s d))
    (pairs indices (coefficientValues k ([0, 1] : List F2)))

def fromCoefficientParameter {k s d : Nat} (p : CoefficientParameter k s d N) :
    Parameter k s d N :=
  (coefficientEquiv k _ p.1, (p.2.1, coefficientEquiv k F2 p.2.2))

theorem fixedCoefficientParams_map (k s d : Nat) (indices : List N) :
    (fixedCoefficientParams k s d indices).map fromCoefficientParameter =
      fixedParams k s d indices := by
  simp only [fixedCoefficientParams, fixedParams, coefficientValues, allLinearMaps,
    pairs, List.map_flatMap, List.flatMap_assoc, List.flatMap_map, List.map_map, Function.comp_def,
    fromCoefficientParameter]

theorem fixedCoefficientParams_length (k s d : Nat) (indices : List N) :
    (fixedCoefficientParams k s d indices).length =
      2^((2*k+1)*(s+d+1)) * indices.length := by
  rw [← fixedParams_length k s d indices, ← fixedCoefficientParams_map, List.length_map]

def tableParams (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    List (Parameter k s d (Fin T.vectors.length)) :=
  fixedParams k s d (List.finRange T.vectors.length)

theorem tableParams_length (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    (tableParams k T).length = 2^((2*k+1)*(s+d+1)) * T.vectors.length := by
  simp only [tableParams, fixedParams_length, List.length_finRange]

theorem outputInstance_constraints (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (AddressGame.outputInstance S k g en).constraints =
      (occurrenceTuples S.occurrences k).flatMap (fun U =>
        (fixedParams k s d en.indices).map (fun p =>
          AddressGame.addressEdge S k g (assemble U p))) := by
  change (ActualEnumeration.indexedOutcomes S.occurrences k s d en.indices).map
    (AddressGame.addressEdge S k g) = _
  rw [indexedOutcomes_factor]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

theorem tableOutput_constraints (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints =
      (occurrenceTuples S.occurrences k).flatMap (fun U =>
        (tableParams k T).map (fun p => AddressGame.addressEdge S k
          (Integration.TableReduction.tableSkeleton T) (assemble U p))) :=
  outputInstance_constraints S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

end DFVSGames.Reduction.FixedOutcomes
end

section

namespace DFVSGames.Reduction.AddressByteSemantics

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
      queryRank (CanonicalAddress.base S.«variables» S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_false_val _

theorem queryAddress_true (S : Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    (AddressGame.queryAddress S k s d true q).val =
      AddressGame.bodyCapacity S k s d +
      queryRank (CanonicalAddress.base S.«variables» S.occurrences s d)
        (CanonicalBodyTemplate.sourceFields q.1 (ActualGame.names S)) q.2
        (fun j => ActualGame.rhs S (q.1 j)) := by
  rw [queryRank, queryWords_actual]
  exact Encoding.sideEquiv_true_val _

theorem addressEdge_words (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (omega : ActualGame.Outcome S k g) :
    constraintWords (AddressGame.addressEdge S k g omega) =
      edgeWords (CanonicalAddress.base S.«variables» S.occurrences s d)
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
      edgeBits (CanonicalAddress.base S.«variables» S.occurrences s d)
        (AddressGame.bodyCapacity S k s d)
        (CanonicalBodyTemplate.sourceFields omega.1.1 (ActualGame.names S))
        omega.1.2 (ActualGame.rightQuery S k g omega).2
        (fun j => ActualGame.rhs S (omega.1.1 j)) := by
  rw [addressEdge_words]
  rfl

theorem edgeBits_split {k s d : Nat} (base capacity : Nat)
    (fields : Fin k → Fin 4 → Nat) (X Y : ActualGame.Map k s d) (b : Fin k → F2) :
    edgeBits base capacity fields X Y b =
      encodeWords [queryRank base fields X b, capacity + queryRank base fields Y b] ++
        encodeWords (permutationWords X Y b) := by
  exact encodeWords_append _ _

end DFVSGames.Reduction.AddressByteSemantics
end

section

namespace DFVSGames.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

abbrev Spec (k : Nat) := MachineOutcomeRows.Spec (4*k) (1+9*k)
abbrev Values (k : Nat) := MachineOutcomeRows.Values (1+9*k)
abbrev Parameter (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :=
  FixedOutcomes.Parameter k s d (Fin T.vectors.length)

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

theorem payload_row_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) (p : Parameter k T) :
    MachineOutcomeRows.payload
        (CanonicalAddress.base S.«variables» S.occurrences s d) (AddressGame.bodyCapacity S k s d)
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
          (CanonicalAddress.base S.«variables» S.occurrences s d) (AddressGame.bodyCapacity S k s d)
          (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))) =
      tupleBits S k T U := by
  rw [selected_rows, List.flatMap_map]
  simp only [payload_row_actual, tupleBits]
  rfl

private theorem encodeWords_flatMap_inline_AddressOutcomeSpecs {α : Type*}
    (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons x items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem gameBits_factor (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    gameBits (AddressGame.tableOutput S k T) =
      encodeWords [(AddressGame.tableOutput S k T).vertices, 2^s,
        (AddressGame.tableOutput S k T).constraints.length] ++
      (FixedOutcomes.occurrenceTuples S.occurrences k).flatMap (tupleBits S k T) := by
  rw [gameBits, gameWords, encodeWords_append, encodeWords_flatMap_inline_AddressOutcomeSpecs]
  congr 1
  change (AddressGame.tableOutput S k T).constraints.flatMap
    (fun edge : Foundations.Target.Constraint (AddressGame.vertexCount S k s d) (2^s) =>
      encodeWords (constraintWords edge)) = _
  rw [FixedOutcomes.tableOutput_constraints]
  dsimp only [TableReduction.tableSkeleton, NoiseTables.Table.gadget]
  simp only [List.flatMap_assoc, List.flatMap_map]
  rfl

end DFVSGames.Reduction.AddressOutcomeSpecs
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
