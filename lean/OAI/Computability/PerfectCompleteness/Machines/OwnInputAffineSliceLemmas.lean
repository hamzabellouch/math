import OAI.Computability.PerfectCompleteness.Algebra.TensorAffineHeavyWitness
import OAI.Computability.PerfectCompleteness.Algebra.TensorBucketEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalPrediction
import OAI.Computability.PerfectCompleteness.Machines.OwnInputReferenceLemmas

namespace OAI


namespace PerfectCompleteness.OwnInputAffineSlice

noncomputable section

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

abbrev F2 := ZMod 2

section FiniteLaws

variable {A B T : Type*} [Fintype A] [Fintype B] [Fintype T]

theorem probability_product_and (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (hidden : A → Bool) (visible : B → Bool) :
    (μ.product ν).probability (fun x => hidden x.1 && visible x.2) =
      μ.probability hidden * ν.probability visible := by
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro v _
  cases hidden h <;> cases visible v <;> simp

theorem product_slice_positive (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (g : A → T) (slice : T → Bool) (visible : B → Bool)
    (positive : 0 < (μ.product ν).probability
      (fun x => slice (g x.1) && visible x.2)) :
    0 < (μ.pushforward g).probability slice := by
  rw [FiniteDistribution.probability_pushforward]
  by_contra hn
  have hz : μ.probability (fun h => slice (g h)) = 0 :=
    le_antisymm (le_of_not_gt hn) (μ.probability_nonnegative _)
  have hp := positive
  rw [probability_product_and μ ν (fun h : A => slice (g h)) visible, hz, zero_mul] at hp
  exact (lt_irrefl 0) hp

theorem condition_product_hidden (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (g : A → T) (slice : T → Bool) (visible : B → Bool)
    (positive : 0 < (μ.product ν).probability
      (fun x => slice (g x.1) && visible x.2)) :
    ((μ.product ν).condition (fun x => slice (g x.1) && visible x.2) positive).pushforward
        (fun x => g x.1) =
      (μ.pushforward g).condition slice (product_slice_positive μ ν g slice visible positive) := by
  have hv : ν.probability visible ≠ 0 := by
    intro hv
    have hp := positive
    rw [probability_product_and μ ν (fun h : A => slice (g h)) visible, hv, mul_zero] at hp
    exact (lt_irrefl 0) hp
  apply FiniteDistribution.eq_of_weight_eq
  intro t
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton]
  simp only [FiniteDistribution.probability_pushforward,
    FiniteDistribution.probability_condition]
  have hevent :
      (fun x : A × B => (slice (g x.1) && visible x.2) && decide (g x.1 = t)) =
      (fun x : A × B => (slice (g x.1) && decide (g x.1 = t)) && visible x.2) := by
    funext x
    cases hs : slice (g x.1) <;> cases he : visible x.2 <;>
      cases ht : decide (g x.1 = t) <;> rfl
  rw [hevent,
    probability_product_and μ ν (fun h : A => slice (g h) && decide (g h = t)) visible,
    probability_product_and μ ν (fun h : A => slice (g h)) visible]
  exact mul_div_mul_right _ _ hv

theorem probability_condition_congr (μ : FiniteDistribution A)
    (given event event' : A → Bool) (positive : 0 < μ.probability given)
    (agree : ∀ x, given x = true → event x = event' x) :
    (μ.condition given positive).probability event =
      (μ.condition given positive).probability event' := by
  rw [FiniteDistribution.probability_condition, FiniteDistribution.probability_condition]
  congr 1
  congr 1
  funext x
  by_cases hx : given x = true
  · rw [agree x hx]
  · simp [hx]

end FiniteLaws

section TensorMatch

variable {ℓ : Nat} {H : Type*} [AddCommGroup H] [Module F2 H]
  [Finite H] [FiniteDimensional F2 H]

def tensorSlice (W : Submodule F2 (Fin ℓ → F2))
    (Q : Submodule F2 (Module.Dual F2 H)) (target : Q →ₗ[F2] W)
    (X : W ⊗[F2] H) : Bool :=
  decide (TensorRestriction.restrictionMap Q X = target)

theorem probability_condition_eq_conditionalMatch
    (W : Submodule F2 (Fin ℓ → F2)) (μ : FiniteDistribution (W ⊗[F2] H))
    (G : (W ⊗[F2] H) → (Fin ℓ → F2))
    (Q : Submodule F2 (Module.Dual F2 H)) (target : Q →ₗ[F2] W)
    (z : Module.Dual F2 H) (offset : Fin ℓ → F2)
    (positive : 0 < μ.probability (tensorSlice W Q target)) :
    (μ.condition (tensorSlice W Q target) positive).probability
        (fun X => decide (G X = offset + TensorBucketEvaluation.tensorOutputLinear W z X)) =
      TensorAffineHeavyWitness.conditionalMatch W μ G Q target z offset := by
  rw [FiniteDistribution.probability_condition]
  unfold TensorAffineHeavyWitness.conditionalMatch AffineLinearHeavyWitness.conditionalMatch
  congr 1
  · unfold FiniteDistribution.probability FiniteDistribution.expectation
    apply Finset.sum_congr rfl
    intro X _
    by_cases hslice : TensorRestriction.restrictionMap Q X = target <;>
      by_cases hmatch : G X = offset + TensorBucketEvaluation.tensorOutputLinear W z X <;>
      simp [tensorSlice, hslice, hmatch]
  · simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
      tensorSlice, decide_eq_true_eq, mul_ite, mul_one, mul_zero]

end TensorMatch

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper))

abbrev VisibleSample (repeats : Nat → Nat) (cut : Cut upper lower) :=
  HiddenBucketBias.VisibleTape W (ScalarSample slots upper lower repeats cut) ×
    Exterior slots rows upper lower

def visibleLaw (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower)) :
    FiniteDistribution (VisibleSample slots rows upper lower W repeats cut) :=
  (HiddenBucketBias.visibleTapeLaw W
    (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))).product
      externalLaw

def hiddenOutput (repeats : Nat → Nat) (cut : Cut upper lower)
    (sample : RawSample slots rows upper lower W repeats cut) :
    W ⊗[F2] UpperSpace slots upper :=
  HiddenBucketBias.hiddenSum W
    (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) sample.1

def jointEvent (repeats : Nat → Nat) (cut : Cut upper lower)
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (sample : RawSample slots rows upper lower W repeats cut) : Bool :=
  tensorSlice W Q target (hiddenOutput slots rows upper lower W repeats cut sample) &&
    visible sample.2

theorem joint_probability (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W) :
    (rawLaw slots rows upper lower W repeats cut externalLaw).probability
        (jointEvent slots rows upper lower W repeats cut visible Q target) =
      (referenceLaw slots rows upper lower W repeats cut).probability (tensorSlice W Q target) *
        (visibleLaw slots rows upper lower W repeats cut externalLaw).probability visible := by
  exact (probability_product_and
    (HiddenBucketBias.hiddenTapeLaw W
      (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (visibleLaw slots rows upper lower W repeats cut externalLaw)
    (fun h => tensorSlice W Q target (HiddenBucketBias.hiddenSum W
      (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) h))
    visible).trans (by rw [referenceLaw, HiddenBucketBias.recursiveLaw,
      HiddenBucketBias.law, FiniteDistribution.probability_pushforward])

theorem slice_probability_pos (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (jointEvent slots rows upper lower W repeats cut visible Q target)) :
    0 < (referenceLaw slots rows upper lower W repeats cut).probability (tensorSlice W Q target) := by
  exact product_slice_positive
    (HiddenBucketBias.hiddenTapeLaw W
      (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (visibleLaw slots rows upper lower W repeats cut externalLaw)
    (HiddenBucketBias.hiddenSum W
      (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (tensorSlice W Q target) visible positive

theorem conditional_referenceLaw (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (jointEvent slots rows upper lower W repeats cut visible Q target)) :
    ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
      (jointEvent slots rows upper lower W repeats cut visible Q target) positive).pushforward
        (hiddenOutput slots rows upper lower W repeats cut) =
      (referenceLaw slots rows upper lower W repeats cut).condition (tensorSlice W Q target)
        (slice_probability_pos slots rows upper lower W repeats cut externalLaw
          visible Q target positive) := by
  exact condition_product_hidden
    (HiddenBucketBias.hiddenTapeLaw W
      (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (visibleLaw slots rows upper lower W repeats cut externalLaw)
    (HiddenBucketBias.hiddenSum W
      (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (tensorSlice W Q target) visible positive

theorem conditional_observed_response_probability
    (a : LowerVector rows lower) (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (jointEvent slots rows upper lower W repeats cut visible Q target))
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (observed : Input slots rows upper lower W a)
    (z : Module.Dual F2 (UpperSpace slots upper)) (offset : UpperVector rows upper) :
    ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
      (jointEvent slots rows upper lower W repeats cut visible Q target) positive).probability
      (fun x => decide (response slots rows upper lower W a labeling observed
          (hiddenOutput slots rows upper lower W repeats cut x) =
        offset + TensorBucketEvaluation.tensorOutputLinear W z
          (hiddenOutput slots rows upper lower W repeats cut x))) =
      TensorAffineHeavyWitness.conditionalMatch W
        (referenceLaw slots rows upper lower W repeats cut)
        (response slots rows upper lower W a labeling observed) Q target z offset := by
  have h := congrArg (fun μ : FiniteDistribution (W ⊗[F2] UpperSpace slots upper) =>
    μ.probability (fun X => decide (response slots rows upper lower W a labeling observed X =
      offset + TensorBucketEvaluation.tensorOutputLinear W z X)))
    (conditional_referenceLaw slots rows upper lower W repeats cut externalLaw
      visible Q target positive)
  rw [FiniteDistribution.probability_pushforward] at h
  exact h.trans (probability_condition_eq_conditionalMatch W
    (referenceLaw slots rows upper lower W repeats cut)
    (response slots rows upper lower W a labeling observed) Q target z offset
    (slice_probability_pos slots rows upper lower W repeats cut externalLaw visible Q target positive))

theorem conditional_response_probability
    (a : LowerVector rows lower) (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (jointEvent slots rows upper lower W repeats cut visible Q target))
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (observed : Input slots rows upper lower W a)
    (fixes_input : ∀ data, visible data = true →
      readInput slots rows upper lower W a
        (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
        data = observed)
    (z : Module.Dual F2 (UpperSpace slots upper)) (offset : UpperVector rows upper) :
    ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
      (jointEvent slots rows upper lower W repeats cut visible Q target) positive).probability
      (fun x => decide (response slots rows upper lower W a labeling
          (readInput slots rows upper lower W a
            (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) x.2)
          (hiddenOutput slots rows upper lower W repeats cut x) =
        offset + TensorBucketEvaluation.tensorOutputLinear W z
          (hiddenOutput slots rows upper lower W repeats cut x))) =
      TensorAffineHeavyWitness.conditionalMatch W
        (referenceLaw slots rows upper lower W repeats cut)
        (response slots rows upper lower W a labeling observed) Q target z offset := by
  trans ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
    (jointEvent slots rows upper lower W repeats cut visible Q target) positive).probability
      (fun x => decide (response slots rows upper lower W a labeling observed
          (hiddenOutput slots rows upper lower W repeats cut x) =
        offset + TensorBucketEvaluation.tensorOutputLinear W z
          (hiddenOutput slots rows upper lower W repeats cut x)))
  · apply probability_condition_congr
    intro x hx
    have hv : visible x.2 = true := (Bool.and_eq_true_iff.mp hx).2
    rw [fixes_input x.2 hv]
  · exact conditional_observed_response_probability slots rows upper lower W a repeats cut
      externalLaw visible Q target positive labeling observed z offset

end
end PerfectCompleteness.OwnInputAffineSlice


namespace PerfectCompleteness.OwnInputRawAssembly

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open OwnInputReference (RawSample ScalarSample UpperSpace UpperVector Cut)

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

theorem backgroundOf_assemble
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) :
    HierarchicalMatrixTable.backgroundOf slots upper
        (OwnInputCanonicalQuery.assemble slots rows upper lower upperRows external) =
      HierarchicalMatrixTable.backgroundOf slots upper
        (OwnInputCanonicalQuery.assemble slots rows upper lower 0 external) := by
  funext node
  simp only [HierarchicalMatrixTable.backgroundOf, OwnInputCanonicalQuery.assemble,
    dite_eq_right node.property]

def exteriorBackground (external : OwnInputReference.Exterior slots rows upper lower) :
    HierarchicalMatrixTable.Background (rows := rows) slots upper :=
  HierarchicalMatrixTable.backgroundOf slots upper
    (OwnInputCanonicalQuery.assemble slots rows upper lower 0 external)

variable (W : Submodule F2 (UpperVector rows upper))
  (repeats : Nat → Nat) (cut : Cut upper lower)

def scalarEval : ScalarSample slots upper lower repeats cut → UpperSpace slots upper :=
  RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))

def mergedTape (sample : RawSample slots rows upper lower W repeats cut) :
    BucketSampler.Tape (rows (Nodes.height upper)) (ScalarSample slots upper lower repeats cut) :=
  (HiddenBucketBias.splitTape W (ScalarSample slots upper lower repeats cut)).symm
    (sample.1, sample.2.1)

theorem split_mergedTape (sample : RawSample slots rows upper lower W repeats cut) :
    HiddenBucketBias.splitTape W (ScalarSample slots upper lower repeats cut)
      (mergedTape slots rows upper lower W repeats cut sample) = (sample.1, sample.2.1) :=
  (HiddenBucketBias.splitTape W (ScalarSample slots upper lower repeats cut)).apply_symm_apply _

def arrays (sample : RawSample slots rows upper lower W repeats cut) : Arrays slots rows :=
  OwnInputCanonicalQuery.assemble slots rows upper lower
    (BucketSampler.evaluate (rows (Nodes.height upper)) (scalarEval slots upper lower repeats cut)
      (mergedTape slots rows upper lower W repeats cut sample)) sample.2.2

def background (visible : OwnInputAffineSlice.VisibleSample slots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.Background (rows := rows) slots upper :=
  exteriorBackground slots rows upper lower visible.2

def knownVisible (visible : OwnInputAffineSlice.VisibleSample slots rows upper lower W repeats cut) :
    HiddenBucketBias.VisibleDirection W → UpperSpace slots upper :=
  fun v => scalarEval slots upper lower repeats cut (visible.1 v)

theorem readInput_knownBuckets (a : Block rows lower)
    (visible : OwnInputAffineSlice.VisibleSample slots rows upper lower W repeats cut) :
    (OwnInputReference.readInput slots rows upper lower W a
      (scalarEval slots upper lower repeats cut) visible).knownBuckets =
      knownVisible slots rows upper lower W repeats cut visible := rfl

theorem arrays_upper (sample : RawSample slots rows upper lower W repeats cut) :
    arrays slots rows upper lower W repeats cut sample upper =
      BucketSampler.evaluate (rows (Nodes.height upper)) (scalarEval slots upper lower repeats cut)
        (mergedTape slots rows upper lower W repeats cut sample) :=
  OwnInputCanonicalQuery.assemble_upper slots rows upper lower _ _

theorem background_arrays (sample : RawSample slots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.backgroundOf slots upper
      (arrays slots rows upper lower W repeats cut sample) =
      background slots rows upper lower W repeats cut sample.2 :=
  backgroundOf_assemble slots rows upper lower _ sample.2.2

theorem arrays_eq_matrix_assemble (sample : RawSample slots rows upper lower W repeats cut) :
    arrays slots rows upper lower W repeats cut sample =
      HierarchicalMatrixTable.assemble slots upper
        (background slots rows upper lower W repeats cut sample.2)
        (NodeEmbedding.matrix (arrays slots rows upper lower W repeats cut sample) upper) := by
  have h := HierarchicalMatrixTable.assemble_original slots upper
    (arrays slots rows upper lower W repeats cut sample)
  rw [background_arrays] at h
  exact h.symm

theorem matrix_arrays (sample : RawSample slots rows upper lower W repeats cut) :
    NodeEmbedding.matrix (arrays slots rows upper lower W repeats cut sample) upper =
      TensorProjectedSlice.totalMatrix (NodeEmbedding.embed slots upper) W
        (HierarchicalTensorMatrix.visibleMatrix slots upper W
          (knownVisible slots rows upper lower W repeats cut sample.2))
        (OwnInputAffineSlice.hiddenOutput slots rows upper lower W repeats cut sample) := by
  have h := HierarchicalTensorMatrix.matrix_eq_totalMatrix slots upper W
    (scalarEval slots upper lower repeats cut)
    (mergedTape slots rows upper lower W repeats cut sample)
    (arrays slots rows upper lower W repeats cut sample)
    (arrays_upper slots rows upper lower W repeats cut sample).symm
  rw [split_mergedTape] at h
  exact h

theorem response_eq_canonical (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : RawSample slots rows upper lower W repeats cut) :
    OwnInputReference.response slots rows upper lower W a labeling
        (OwnInputReference.readInput slots rows upper lower W a
          (scalarEval slots upper lower repeats cut) sample.2)
        (OwnInputAffineSlice.hiddenOutput slots rows upper lower W repeats cut sample) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (OwnInputCanonicalQuery.canonicalQuery slots rows lower a
          (arrays slots rows upper lower W repeats cut sample))).2.1
            ⟨upper, cut.upper_ne_lower⟩ := by
  have h := OwnInputCanonicalQuery.response_readInput_hidden_eq slots rows upper lower
    cut.upper_ne_lower W a labeling (scalarEval slots upper lower repeats cut)
    (mergedTape slots rows upper lower W repeats cut sample) sample.2.2
  rw [split_mergedTape] at h
  exact h

theorem response_eq_rightUpper (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : RawSample slots rows upper lower W repeats cut) :
    OwnInputReference.response slots rows upper lower W a labeling
        (OwnInputReference.readInput slots rows upper lower W a
          (scalarEval slots upper lower repeats cut) sample.2)
        (OwnInputAffineSlice.hiddenOutput slots rows upper lower W repeats cut sample) =
      HierarchicalPrediction.rightUpper slots upper
        (background slots rows upper lower W repeats cut sample.2)
        labeling lower cut.upper_ne_lower a
        (NodeEmbedding.matrix (arrays slots rows upper lower W repeats cut sample) upper) := by
  rw [← background_arrays slots rows upper lower W repeats cut sample,
    HierarchicalPrediction.rightUpper, HierarchicalMatrixTable.displayed_original]
  exact response_eq_canonical slots rows upper lower W repeats cut a labeling sample

theorem response_eq_rightUpper_totalMatrix (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : RawSample slots rows upper lower W repeats cut) :
    OwnInputReference.response slots rows upper lower W a labeling
        (OwnInputReference.readInput slots rows upper lower W a
          (scalarEval slots upper lower repeats cut) sample.2)
        (OwnInputAffineSlice.hiddenOutput slots rows upper lower W repeats cut sample) =
      HierarchicalPrediction.rightUpper slots upper
        (background slots rows upper lower W repeats cut sample.2)
        labeling lower cut.upper_ne_lower a
        (TensorProjectedSlice.totalMatrix (NodeEmbedding.embed slots upper) W
          (HierarchicalTensorMatrix.visibleMatrix slots upper W
            (knownVisible slots rows upper lower W repeats cut sample.2))
          (OwnInputAffineSlice.hiddenOutput slots rows upper lower W repeats cut sample)) := by
  rw [← matrix_arrays slots rows upper lower W repeats cut sample]
  exact response_eq_rightUpper slots rows upper lower W repeats cut a labeling sample

end
end PerfectCompleteness.OwnInputRawAssembly

end OAI
