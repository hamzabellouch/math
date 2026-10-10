import OAI.Computability.PerfectCompleteness.Decoding.CleanDecoderSeedLawLemmas
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedExperiment

namespace OAI

section

namespace PerfectCompleteness.SlotProjectedExperiment

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

def selectSlot : MixedSupport.Slot → Fin 3 → MixedSupport.Slot
  | .clause _ ids _, position => .bit (ids position)
  | .bit id, _ => .bit id

def selectProjection (s : MixedSupport.Slot) (position : Fin 3) :
    MixedSupport.Projection s (selectSlot s position) := by
  cases s with
  | clause occurrence ids signs => exact .select occurrence ids signs position
  | bit id => exact .keep (.bit id)

def flaggedSlot (s : MixedSupport.Slot) (position : Fin 3) : Bool → MixedSupport.Slot
  | false => s
  | true => selectSlot s position

def flaggedProjection (s : MixedSupport.Slot) (position : Fin 3) :
    (b : Bool) → MixedSupport.Projection s (flaggedSlot s position b)
  | false => .keep s
  | true => selectProjection s position

variable {branch : Nat → Nat} {n i j t v m : Nat}

def mixedInside (slots : Slots branch (i + 1) → Fin t → MixedSupport.Slot)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i)) :
    Slots branch (i + 1) → Fin t → MixedSupport.Slot :=
  fun leaf a => flaggedSlot (slots leaf a) (choices leaf.1 leaf.2 a) (flags leaf.1)

def insideProjection (slots : Slots branch (i + 1) → Fin t → MixedSupport.Slot)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i)) :
    ∀ leaf a, MixedSupport.Projection (slots leaf a) (mixedInside slots choices flags leaf a) :=
  fun leaf a => flaggedProjection (slots leaf a) (choices leaf.1 leaf.2 a) (flags leaf.1)

abbrev Inner (rows : Nat → Nat) :=
  StoppedProjectedExperiment.Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows

abbrev innerLaw (rows : Nat → Nat) (hij : i < j)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (flag : Fin (branch i) → FiniteDistribution Bool) :=
  StoppedProjectedExperiment.innerLaw (n := n) (t := t) rows hij hbranch hrows flag

variable (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (pref : GeometricCutSplit.Prefix branch n (j + 1))

def upperPath := GeometricCutSplit.prefixPath hupper pref

abbrev lowerPath (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  StoppedProjectedExperiment.lowerPath rows hij k

def stoppedPath (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  (upperPath hupper pref).append (lowerPath rows hij k)

def upper := WholeArrayInteriorExterior.upperNode (upperPath hupper pref)

def lower (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :=
  WholeArrayInteriorExterior.upperNode (stoppedPath rows hupper hij pref k)

@[simp] theorem upper_height : Nodes.height (upper hupper pref) = j + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

@[simp] theorem lower_height
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Nodes.height (lower rows hupper hij pref k) = i + 1 :=
  WholeArrayInteriorExterior.upperNode_height _

def cut (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    OwnInputReference.Cut (upper hupper pref) (lower rows hupper hij pref k) :=
  StoppedOwnInputGeometry.cutOfBelow
    (StoppedProjectedExperiment.below_append hij (upperPath hupper pref) (lowerPath rows hij k))

def direction (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Block rows (lower rows hupper hij pref k) :=
  let level : Fin n := ⟨i, Nat.lt_of_lt_of_le (Nat.lt_trans hij (Nat.lt_succ_self j)) hupper⟩
  (PrefixTests.nodeDirection rows level
    ⟨lower rows hupper hij pref k, lower_height rows hupper hij pref k⟩ (k.2.2 level)).val

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)

def inside (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Slots branch (i + 1) → Fin t → MixedSupport.Slot :=
  fun leaf a => slots ((stoppedPath rows hupper hij pref k).slotEmbedding leaf) a

def projectedSlots (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill (stoppedPath rows hupper hij pref k) slots
    (mixedInside (inside rows hupper hij pref slots k) k.2.1.1 k.2.1.2)

theorem fill_inside (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    CutSlotAssembly.fill (stoppedPath rows hupper hij pref k) slots
      (inside rows hupper hij pref slots k) = slots :=
  CutSlotAssembly.fill_restrict (stoppedPath rows hupper hij pref k) slots

def projection (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    ∀ leaf a, MixedSupport.Projection (slots leaf a)
      (projectedSlots rows hupper hij pref slots k leaf a) :=
  fun leaf a => CutProjectionAssembly.castProjection
    (congrFun (congrFun (fill_inside rows hupper hij pref slots k) leaf) a) rfl
    (CutProjectionAssembly.fillProjection (stoppedPath rows hupper hij pref k) slots
      (inside rows hupper hij pref slots k)
      (mixedInside (inside rows hupper hij pref slots k) k.2.1.1 k.2.1.2)
      (insideProjection (inside rows hupper hij pref slots k) k.2.1.1 k.2.1.2) leaf a)

abbrev Sample := HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
  (projectedSlots rows hupper hij pref slots) (upper hupper pref)
  (lower rows hupper hij pref) (cut rows hupper hij pref)

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

abbrev experiment :=
  HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
    slots (projectedSlots rows hupper hij pref slots) (projection rows hupper hij pref slots)
    (upper hupper pref) (i + 1) (lower rows hupper hij pref)
    (cut rows hupper hij pref) (direction rows hupper hij pref)
    (innerLaw rows hij hbranch hrows flag) σ

def family : OriginalDecoderMark.Family branch rows n t
    (Sample rows repeats hupper hij pref) where
  original slots := (experiment rows repeats hupper hij pref slots hbranch hrows flag σ).original
  arrays slots := (experiment rows repeats hupper hij pref slots hbranch hrows flag σ).arrays
  lowerEvent slots := HierarchicalAdviceExperiment.lowerEvent
    (experiment rows repeats hupper hij pref slots hbranch hrows flag σ)

theorem mark_eq (κ : ℝ)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots (upper hupper pref))
    (X : HierarchicalFrozenTables.QuotientMatrix slots (upper hupper pref) (i + 1) background) :
    OriginalDecoderMark.mark (family rows repeats hupper hij pref hbranch hrows flag σ)
      (upper hupper pref) (i + 1) κ slots background X ↔
    HierarchicalUsefulness.mark slots (upper hupper pref) (i + 1)
      (experiment rows repeats hupper hij pref slots hbranch hrows flag σ).original
      (experiment rows repeats hupper hij pref slots hbranch hrows flag σ).arrays
      (HierarchicalAdviceExperiment.lowerEvent
        (experiment rows repeats hupper hij pref slots hbranch hrows flag σ)) κ
      ⟨background, X⟩ = true := Iff.rfl

section Source

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch i) → Slots branch i)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := i) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
  (flags : SourceProjectedTag.Flags (branch := branch) (n := i))

private theorem tree_sources (leaf : Slots branch (i + 1)) (a : Fin t) :
    SourceChildKernel.tree designated leaf.1
      (SourceQuestionKernelJoint.sources designated q choices leaf.1) leaf.2 a =
      (q leaf a, choices leaf.1 leaf.2 a) := by
  rcases leaf with ⟨child, tail⟩
  have h := SourceQuestionPositionSplit.child_tree_join designated q
    (SourceQuestionPositionSplit.byChild.symm choices) child tail a
  change SourceChildKernel.tree designated child
    (SourceQuestionKernelJoint.sources designated q choices child) tail a =
      (q (child, tail) a, choices child tail a) at h
  exact h

theorem mixedInside_source :
    mixedInside (SourceProjectedTag.originalSlots clauses q) choices flags =
      SourceProjectedTag.mixedInside clauses designated q choices flags := by
  funext leaf a
  have htree := tree_sources designated q choices leaf a
  cases hf : flags leaf.1 <;>
    simp only [mixedInside, flaggedSlot, selectSlot, SourceProjectedTag.mixedInside,
      SourceProjectedTag.originalSlots, sourceSlots, PreliminarySampler.endpoints,
      SourceChildKernel.mixedSlots, SourceChildKernel.nativeSlots,
      ProjectedCardinality.projectedSlots, SourceChildKernel.ids,
      SourceClause.occurrenceVariable, SourceKeys.slot, hf, htree]

private theorem projection_family_heq
    {left right₁ right₂ : Slots branch (i + 1) → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (p₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hp : ∀ leaf a, HEq (p₁ leaf a) (p₂ leaf a)) : HEq p₁ p₂ := by
  subst right₂
  apply heq_of_eq
  funext leaf a
  exact eq_of_heq (hp leaf a)

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private theorem flagged_occurrence_heq
    {e e' : SourceClause.Occurrence m} (h : e = e') (b : Bool) :
    HEq (flaggedProjection (SourceKeys.slot clauses (.clause e.1)) e.2 b)
      (flaggedProjection (SourceKeys.slot clauses (.clause e'.1)) e'.2 b) := by
  cases h
  rfl

private theorem child_projection_as_flagged (child : Fin (branch i))
    (s : SourceChildKernel.Source (m := m) (t := t) designated child)
    (b : Bool) (leaf : Slots branch i) (a : Fin t) :
    HEq (SourceChildKernel.projection clauses designated child s b leaf a)
      (flaggedProjection
        (SourceKeys.slot clauses (.clause (SourceChildKernel.tree designated child s leaf a).1))
        (SourceChildKernel.tree designated child s leaf a).2 b) := by
  cases b <;> rfl

theorem insideProjection_source :
    HEq (insideProjection (SourceProjectedTag.originalSlots clauses q) choices flags)
      (SourceProjectedTag.projection clauses designated q choices flags) := by
  apply projection_family_heq (mixedInside_source clauses designated q choices flags)
  intro leaf a
  have htree := tree_sources designated q choices leaf a
  have hcast : HEq (SourceProjectedTag.projection clauses designated q choices flags leaf a)
      (SourceChildKernel.projection clauses designated leaf.1
        (SourceQuestionKernelJoint.sources designated q choices leaf.1)
        (flags leaf.1) leaf.2 a) := by
    unfold SourceProjectedTag.projection
    dsimp only [id]
    exact mpr_heq _ _
  have hflagged := flagged_occurrence_heq clauses htree.symm (flags leaf.1)
  have hchild := child_projection_as_flagged clauses designated leaf.1
    (SourceQuestionKernelJoint.sources designated q choices leaf.1)
    (flags leaf.1) leaf.2 a
  exact hflagged.trans (hchild.symm.trans hcast.symm)

variable (originalQuestions : PreliminarySampler.Questions branch n t m)

theorem projectedSlots_source
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    projectedSlots rows hupper hij pref
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) k =
      StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated
        (originalQuestions, pref) k := by
  unfold projectedSlots StoppedProjectedExperiment.projectedSlots
  exact congrArg (CutSlotAssembly.fill (stoppedPath rows hupper hij pref k)
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)))
    (mixedInside_source clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij (originalQuestions, pref) k)
      k.2.1.1 k.2.1.2)

private theorem filled_projection_heq (p : Path branch n (i + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right₁ right₂ : Slots branch (i + 1) → Fin t → MixedSupport.Slot)
    (hleft : CutSlotAssembly.fill p outside left = outside) (hr : right₁ = right₂)
    (p₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (p₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hp : HEq p₁ p₂) :
    HEq (fun leaf a => CutProjectionAssembly.castProjection
        (congrFun (congrFun hleft leaf) a) rfl
        (CutProjectionAssembly.fillProjection p outside left right₁ p₁ leaf a))
      (fun leaf a => CutProjectionAssembly.castProjection
        (congrFun (congrFun hleft leaf) a) rfl
        (CutProjectionAssembly.fillProjection p outside left right₂ p₂ leaf a)) := by
  subst right₂
  have hp' : p₁ = p₂ := eq_of_heq hp
  subst p₂
  rfl

theorem projection_source
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    HEq (projection rows hupper hij pref
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) k)
      (StoppedProjectedExperiment.projection clauses rows hupper hij designated
        (originalQuestions, pref) k) := by
  exact filled_projection_heq (stoppedPath rows hupper hij pref k)
    (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions))
    (SourceProjectedTag.originalSlots clauses
      (StoppedProjectedExperiment.cutQuestions rows hupper hij (originalQuestions, pref) k))
    _ _ (StoppedProjectedExperiment.fill_native clauses rows hupper hij (originalQuestions, pref) k)
    (mixedInside_source clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij (originalQuestions, pref) k)
      k.2.1.1 k.2.1.2) _ _
    (insideProjection_source clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij (originalQuestions, pref) k)
      k.2.1.1 k.2.1.2)

private theorem tagged_projection_heq {K : Type*}
    {left : Slots branch n → Fin t → MixedSupport.Slot}
    {right₁ right₂ : K → Slots branch n → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ k leaf a, MixedSupport.Projection (left leaf a) (right₁ k leaf a))
    (p₂ : ∀ k leaf a, MixedSupport.Projection (left leaf a) (right₂ k leaf a))
    (hp : ∀ k, HEq (p₁ k) (p₂ k)) : HEq p₁ p₂ := by
  subst right₂
  apply heq_of_eq
  funext k
  exact eq_of_heq (hp k)

private theorem projected_experiment_heq {K : Type*} [Fintype K]
    (native : Slots branch n → Fin t → MixedSupport.Slot)
    {right₁ right₂ : K → Slots branch n → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ k leaf a, MixedSupport.Projection (native leaf a) (right₁ k leaf a))
    (p₂ : ∀ k leaf a, MixedSupport.Projection (native leaf a) (right₂ k leaf a))
    (hp : HEq p₁ p₂) (upperNode : Nodes branch n) (lowerLevel : Nat)
    (lowerNode : K → Nodes branch n)
    (cuts : ∀ k, OwnInputReference.Cut upperNode (lowerNode k))
    (directions : ∀ k, Block rows (lowerNode k)) (μ : FiniteDistribution K) :
    HEq (HierarchicalProjectedExperiment.experiment (repeats := repeats)
      native right₁ p₁ upperNode lowerLevel lowerNode cuts directions μ σ)
      (HierarchicalProjectedExperiment.experiment (repeats := repeats)
        native right₂ p₂ upperNode lowerLevel lowerNode cuts directions μ σ) := by
  subst right₂
  have hp' : p₁ = p₂ := eq_of_heq hp
  subst p₂
  rfl

theorem experiment_source :
    HEq (experiment rows repeats hupper hij pref
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) hbranch hrows flag σ)
      (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ (originalQuestions, pref)) := by
  have hs := funext (projectedSlots_source rows hupper hij pref clauses designated originalQuestions)
  have hp := tagged_projection_heq hs _ _
    (projection_source rows hupper hij pref clauses designated originalQuestions)
  exact projected_experiment_heq rows repeats σ _ hs _ _ hp _ _ _ _ _ _

private theorem projection_data_congr {K : Type*} {α : Sort*}
    {native : Slots branch n → Fin t → MixedSupport.Slot}
    {right₁ right₂ : K → Slots branch n → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ k leaf a, MixedSupport.Projection (native leaf a) (right₁ k leaf a))
    (p₂ : ∀ k leaf a, MixedSupport.Projection (native leaf a) (right₂ k leaf a))
    (hp : HEq p₁ p₂)
    (f : (right : K → Slots branch n → Fin t → MixedSupport.Slot) →
      (∀ k leaf a, MixedSupport.Projection (native leaf a) (right k leaf a)) → α) :
    f right₁ p₁ = f right₂ p₂ := by
  subst right₂
  have hp' : p₁ = p₂ := eq_of_heq hp
  subst p₂
  rfl

theorem mark_source (κ : ℝ)
    (background : HierarchicalMatrixTable.Background (rows := rows)
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) (upper hupper pref))
    (X : HierarchicalFrozenTables.QuotientMatrix
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions))
      (upper hupper pref) (i + 1) background) :
    OriginalDecoderMark.mark (family rows repeats hupper hij pref hbranch hrows flag σ)
      (upper hupper pref) (i + 1) κ
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) background X ↔
    HierarchicalUsefulness.mark
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) (upper hupper pref) (i + 1)
      (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ (originalQuestions, pref)).original
      (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ (originalQuestions, pref)).arrays
      (HierarchicalAdviceExperiment.lowerEvent
        (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
          hbranch hrows flag σ (originalQuestions, pref))) κ ⟨background, X⟩ = true := by
  have hs := funext (projectedSlots_source rows hupper hij pref clauses designated originalQuestions)
  have hp := tagged_projection_heq hs _ _
    (projection_source rows hupper hij pref clauses designated originalQuestions)
  have hm := projection_data_congr hs _ _ hp (fun right proj =>
    let S := HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) right proj
      (upper hupper pref) (i + 1) (lower rows hupper hij pref)
      (cut rows hupper hij pref) (direction rows hupper hij pref)
      (innerLaw rows hij hbranch hrows flag) σ
    HierarchicalUsefulness.mark S.slots S.upper S.lowerLevel S.original S.arrays
      (HierarchicalAdviceExperiment.lowerEvent S) κ ⟨background, X⟩)
  exact Iff.of_eq (congrArg (fun b : Bool => b = true) hm)

end Source

end
end PerfectCompleteness.SlotProjectedExperiment

end

end OAI
