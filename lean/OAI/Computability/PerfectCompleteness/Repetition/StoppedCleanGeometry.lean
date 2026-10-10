import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionCutSplit
import OAI.Computability.PerfectCompleteness.Decoding.DecoderSourcePullback
import OAI.Computability.PerfectCompleteness.Decoding.FixedDecoderCleanRateLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayInteriorExteriorLemmas
import OAI.Computability.PerfectCompleteness.Machines.WholeArrayInteriorOwnInputLaw
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerReplayTransportLemmas

namespace OAI

section

namespace PerfectCompleteness.StoppedCleanGeometry

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat}

def descendant : {N j i : Nat} → (p : Path branch N (j + 1)) →
    (q : Path branch (j + 1) (i + 1)) → i < j →
    HierarchicalFrozenTables.LowerNodes (WholeArrayInteriorExterior.upperNode p) (i + 1)
  | _, _, _, .refl _, q, hij =>
      ⟨⟨WholeArrayInteriorExterior.upperNode q,
          (WholeArrayInteriorExterior.upperNode_height q).trans_lt (Nat.succ_lt_succ hij)⟩,
        WholeArrayInteriorExterior.upperNode_height q⟩
  | _, _, _, .step _ p, q, hij => descendant p q hij

theorem lowerNode_descendant : {N j i : Nat} → (p : Path branch N (j + 1)) →
    (q : Path branch (j + 1) (i + 1)) → (hij : i < j) →
    HierarchicalLeftDecoder.LowerNode (WholeArrayInteriorExterior.upperNode p) (i + 1)
        (descendant p q hij) = WholeArrayInteriorExterior.upperNode (p.append q)
  | _, _, _, .refl _, _, _ => rfl
  | N + 1, _, _, .step child p, q, hij =>
      congrArg (fun node : Nodes branch N =>
        (Sum.inr (child, node) : Nodes branch (N + 1))) (lowerNode_descendant p q hij)

variable {N j i : Nat} (p : Path branch N (j + 1))
  (q : Path branch (j + 1) (i + 1)) (hij : i < j)

def cut : OwnInputReference.Cut (WholeArrayInteriorExterior.upperNode p)
    (HierarchicalLeftDecoder.LowerNode (WholeArrayInteriorExterior.upperNode p) (i + 1)
      (descendant p q hij)) :=
  DecoderSourcePullback.selectedCut (WholeArrayInteriorExterior.upperNode p) (i + 1)
    (descendant p q hij)

@[simp] theorem lowerHeight :
    Nodes.height (HierarchicalLeftDecoder.LowerNode
      (WholeArrayInteriorExterior.upperNode p) (i + 1) (descendant p q hij)) = i + 1 :=
  CleanDecoderContext.lowerHeight (WholeArrayInteriorExterior.upperNode p) (descendant p q hij)

theorem fullPath_spec : {N j i : Nat} → (p : Path branch N (j + 1)) →
    (q : Path branch (j + 1) (i + 1)) → (hij : i < j) →
    (⟨Nodes.height (HierarchicalLeftDecoder.LowerNode
        (WholeArrayInteriorExterior.upperNode p) (i + 1) (descendant p q hij)),
      WholeArrayInteriorOwnInputLaw.fullPath (WholeArrayInteriorExterior.upperNode p)
        (HierarchicalLeftDecoder.LowerNode (WholeArrayInteriorExterior.upperNode p) (i + 1)
          (descendant p q hij)) (cut p q hij)⟩ : Σ height, Path branch N height) =
      ⟨i + 1, p.append q⟩
  | _, _, _, .refl _, q, _ => WholeArrayInteriorExterior.upperNode_spec q
  | N + 1, _, _, .step child p, q, hij =>
      congrArg (fun z : Σ height, Path branch N height =>
        (⟨z.1, Path.step child z.2⟩ : Σ height, Path branch (N + 1) height))
          (fullPath_spec p q hij)

private theorem append_cast_heq {N a b c : Nat} (pref : Path branch N a)
    (suffix : Path branch a b) (h : b = c) :
    HEq (pref.append (h ▸ suffix)) (pref.append suffix) := by
  cases h
  rfl

theorem cleanPath_eq :
    CleanRecordDecoderInput.path (WholeArrayInteriorExterior.upperNode p)
      (descendant p q hij) (cut p q hij) = p.append q := by
  apply eq_of_heq
  exact (append_cast_heq (Nodes.path (WholeArrayInteriorExterior.upperNode p))
    (cut p q hij).path
    (CleanDecoderContext.lowerHeight (WholeArrayInteriorExterior.upperNode p)
      (descendant p q hij))).trans ((Sigma.mk.inj (fullPath_spec p q hij)).2)

def firstLeaf (hbranch : ∀ k, 0 < branch k) : (height : Nat) → Slots branch height
  | 0 => ()
  | height + 1 => (⟨0, hbranch height⟩, firstLeaf hbranch height)

section Fixed

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (input : List Bool) {N j i : Nat}
  (p : Path (FixedParameters.branch parameters) N (j + 1))
  (q : Path (FixedParameters.branch parameters) (j + 1) (i + 1))

abbrev OutsideQuestions := SourceQuestionCutSplit.OutsideQuestions (p.append q)
  (FixedRows.sourceLength parameters.plan hδ)
  (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length

def fixedOutside (external : OutsideQuestions parameters input p q) :=
  sourceSlots (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (PreliminarySampler.endpoints
      (SourceQuestionCutSplit.join (p.append q) (fun _ _ => 0) external))

def placeholder : Slots (FixedParameters.branch parameters) (i + 1) →
    Fin (FixedRows.sourceLength parameters.plan hδ) → MixedSupport.Slot :=
  fun _ _ => SourceKeys.slot (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) (.clause 0)

theorem fixedOutside_at (external : OutsideQuestions parameters input p q)
    (leaf : SourceQuestionCutSplit.OutsideLeaf (p.append q))
    (coordinate : Fin (FixedRows.sourceLength parameters.plan hδ)) :
    fixedOutside parameters input p q external leaf.val coordinate =
      SourceKeys.slot (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
        (.clause (external leaf coordinate)) := by
  unfold fixedOutside sourceSlots PreliminarySampler.endpoints
  rw [SourceQuestionCutSplit.join_outside]

abbrev Exterior (external : OutsideQuestions parameters input p q) :=
  WholeCutGrouping.Exterior (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (p.append q) (fixedOutside parameters input p q external)

variable (hij : i < j) (external : OutsideQuestions parameters input p q)

def filledExteriorEquiv : Exterior parameters input p q external ≃
    CleanPhysicalReplay.Exterior (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (p.append q) (fixedOutside parameters input p q external)
      (placeholder parameters input (i := i)) :=
  WholeCutExteriorTransport.equiv (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (p.append q) (fixedOutside parameters input p q external)
    (CutSlotAssembly.fill (p.append q) (fixedOutside parameters input p q external)
      (placeholder parameters input (i := i)))
    (fun leaf hleaf => (CutSlotAssembly.fill_outside (p.append q)
      (fixedOutside parameters input p q external) (placeholder parameters input (i := i))
      leaf hleaf).symm)

def exteriorEquiv : Exterior parameters input p q external ≃
    CleanPhysicalReplay.Exterior (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (CleanRecordDecoderInput.path (WholeArrayInteriorExterior.upperNode p)
        (descendant p q hij) (cut p q hij)) (fixedOutside parameters input p q external)
      (placeholder parameters input (i := i)) :=
  (filledExteriorEquiv parameters input p q external).trans
    (Equiv.cast (congrArg (fun path : Path (FixedParameters.branch parameters) N (i + 1) =>
    CleanPhysicalReplay.Exterior (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      path (fixedOutside parameters input p q external)
      (placeholder parameters input (i := i)))
    (cleanPath_eq p q hij).symm))

theorem exteriorEquiv_law :
    (FiniteDistribution.uniform (Exterior parameters input p q external)).pushforward
        (exteriorEquiv parameters input p q hij external) = FiniteDistribution.uniform _ := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (exteriorEquiv parameters input p q hij external)

def geometry (exterior : Exterior parameters input p q external) :
    FixedDecoderCleanRate.Geometry parameters N i (WholeArrayInteriorExterior.upperNode p)
      (descendant p q hij) where
  designated := fun _ => firstLeaf (FixedParameters.branch_pos parameters) i
  cut := cut p q hij
  outside := fixedOutside parameters input p q external
  placeholder := placeholder parameters input
  exterior := exteriorEquiv parameters input p q hij external exterior

theorem geometry_path (exterior : Exterior parameters input p q external) :
    CleanRecordDecoderInput.path (WholeArrayInteriorExterior.upperNode p) (descendant p q hij)
      (geometry parameters input p q hij external exterior).cut = p.append q :=
  cleanPath_eq p q hij

end Fixed
end
end PerfectCompleteness.StoppedCleanGeometry

end

end OAI
