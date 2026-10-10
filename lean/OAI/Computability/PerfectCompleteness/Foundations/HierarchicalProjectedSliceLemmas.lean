import OAI.Computability.PerfectCompleteness.Algebra.AffineDecoderMeeting
import OAI.Computability.PerfectCompleteness.Algebra.RightDecoderAffineSuccess
import OAI.Computability.PerfectCompleteness.Algebra.TensorBucketEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Algebra.TensorRowAdviceLemmas
import OAI.Computability.PerfectCompleteness.Algebra.TensorSliceDimension
import OAI.Computability.PerfectCompleteness.Construction.ProjectedNodeEmbedding
import OAI.Computability.PerfectCompleteness.Decoding.ChildBlockProjection
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalLeftDecoder
import OAI.Computability.PerfectCompleteness.Decoding.RightDecoderWitness
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas
import OAI.Computability.PerfectCompleteness.Machines.OwnInputAffineSliceLemmas
import OAI.Computability.PerfectCompleteness.Machines.OwnInputReferenceLemmas

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedSlice

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace originalSlots upper) :=
  Fintype.ofFinite _

local instance valueFintype : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projectedSlots upper)

abbrev HiddenTensor := LinearMap.ker A ⊗[F2] NodeEmbedding.NodeH projectedSlots upper

abbrev visibleMatrix := HierarchicalTensorMatrix.visibleMatrix originalSlots upper (LinearMap.ker A)
  (fun v => ProjectedNodeEmbedding.nativePullback projection upper (known v))

theorem visibleMatrix_apply
    (q : Module.Dual F2 (NodeEmbedding.RowSpace originalSlots upper)) :
    visibleMatrix originalSlots projectedSlots projection upper A known q =
      ∑ v : HiddenBucketBias.VisibleDirection (LinearMap.ker A),
        ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap q) (known v) • v.val.val :=
  HierarchicalTensorMatrix.visibleMatrix_apply originalSlots upper (LinearMap.ker A)
    (fun v => ProjectedNodeEmbedding.nativePullback projection upper (known v)) q

abbrev matrix (T : HiddenTensor projectedSlots upper A) :=
  TensorProjectedSlice.totalMatrix (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A)
    (visibleMatrix originalSlots projectedSlots projection upper A known) T

abbrev quotientMatrix (T : HiddenTensor projectedSlots upper A) :=
  MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (matrix originalSlots projectedSlots projection upper A known T)

abbrev table :=
  HierarchicalUsefulness.table originalSlots upper lowerLevel original arrays lowerEvent κ σ background

abbrev VisibleGood : Prop :=
  ManyGoodRows.GoodRow (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
      (visibleMatrix originalSlots projectedSlots projection upper A known)))

def witness
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :=
  TensorSelectedSlice.witness
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) hgood

def columnSpace
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Submodule F2 (Module.Dual F2 (NodeEmbedding.NodeH projectedSlots upper)) :=
  TensorSelectedSlice.columnSpace (ProjectedNodeEmbedding.intoOriginal projection upper)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) hgood

theorem columnSpace_eq_pulled
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    columnSpace originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      ((witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace.map
        (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background).mkQ.dualMap).map
        (ProjectedNodeEmbedding.intoOriginal projection upper).dualMap :=
  TensorSelectedSlice.columnSpace_eq_sequential_maps (ProjectedNodeEmbedding.intoOriginal projection upper)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) hgood

theorem finrank_columnSpace_le
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Module.finrank F2
      (columnSpace originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) ≤ r :=
  TensorSelectedSlice.finrank_columnSpace_le (ProjectedNodeEmbedding.intoOriginal projection upper)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) hgood

def J (T : HiddenTensor projectedSlots upper A) : Bool :=
  GoodAdviceEvents.J (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ (A, quotientMatrix originalSlots projectedSlots projection upper lowerLevel background A known T)

def target
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true) :
    columnSpace originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood →ₗ[F2]
      LinearMap.ker A :=
  TensorSelectedSlice.target (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) le_rfl hgood hne

theorem J_iff_restriction
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true)
    (T : HiddenTensor projectedSlots upper A) :
    J originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true ↔
      TensorRestriction.restrictionMap
        (columnSpace originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) T =
      target originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne :=
  TensorSelectedSlice.J_iff_restriction (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) le_rfl hgood hne T

theorem J_false_of_not_good
    (hbad : ¬ VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor projectedSlots upper A) :
    J originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = false :=
  TensorSelectedSlice.J_false_of_not_good (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) le_rfl hbad T

theorem selectedValue_eq_some
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor projectedSlots upper A) :
    HierarchicalPrediction.selectedValue
        (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ) r ρ A
        (quotientMatrix originalSlots projectedSlots projection upper lowerLevel background A known T) =
      some (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value := by
  change HierarchicalPrediction.selectedValue _ r ρ A
    (MatrixRowQuotient.projectMatrix _ (TensorProjectedSlice.totalMatrix _ _ _ T)) = _
  rw [TensorRowAdvice.selectedValue_projectMatrix_eq (ProjectedNodeEmbedding.intoOriginal projection upper)
    (LinearMap.ker A) A le_rfl
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ) ρ
    (visibleMatrix originalSlots projectedSlots projection upper A known) T]
  simp only [HierarchicalPrediction.selectedValue, dite_eq_left hgood, witness,
    TensorSelectedSlice.witness]

def correction
    (y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :
    Module.Dual F2 (NodeEmbedding.RowSpace originalSlots upper) :=
  RepresentativeMatrixTable.correctionFunctional (TreeCanonical.numberedSlots originalSlots)
    (NodeEmbedding.RowSpace originalSlots upper) (HierarchicalMatrixTable.other originalSlots upper background)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap originalSlots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec originalSlots upper lowerLevel background) y.2

def nativeCorrection
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Module.Dual F2 (NodeEmbedding.NodeH projectedSlots upper) :=
  (correction originalSlots upper lowerLevel background
    (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value).comp
      (ProjectedNodeEmbedding.intoOriginal projection upper)

theorem nativeCorrection_eq_upperTarget
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    nativeCorrection originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      DecoderSourcePullback.upperTarget projection upper
        (correction originalSlots upper lowerLevel background
          (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) :=
  ProjectedNodeEmbedding.dualMap_eq_upperTarget projection upper
    (correction originalSlots upper lowerLevel background
      (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value)

def visibleOffset
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Block rows upper :=
  visibleMatrix originalSlots projectedSlots projection upper A known
      (correction originalSlots upper lowerLevel background
        (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) +
    (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value.1

theorem selectedCorrection_eq_some
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor projectedSlots upper A) :
    (HierarchicalPrediction.selectedValue
      (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ) r ρ A
      (quotientMatrix originalSlots projectedSlots projection upper lowerLevel background A known T)).map
        (fun y => (correction originalSlots upper lowerLevel background y).comp
          (ProjectedNodeEmbedding.intoOriginal projection upper)) =
      some (nativeCorrection originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) := by
  simp only [selectedValue_eq_some originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood T,
    Option.map_some, nativeCorrection]

theorem affinePrediction_eq_tensor
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor projectedSlots upper A) :
    HierarchicalPrediction.affinePrediction originalSlots upper lowerLevel background
        (matrix originalSlots projectedSlots projection upper A known T)
        (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value =
      visibleOffset originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood +
        TensorBucketEvaluation.tensorOutput (LinearMap.ker A)
          (nativeCorrection originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) T :=
  TensorProjectedSlice.prediction_eq_visible_add_tensorOutput (ProjectedNodeEmbedding.intoOriginal projection upper)
    (LinearMap.ker A) (visibleMatrix originalSlots projectedSlots projection upper A known) T
    (correction originalSlots upper lowerLevel background
      (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value)
    (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value.1

end
end PerfectCompleteness.HierarchicalProjectedSlice


namespace PerfectCompleteness.HierarchicalProjectedMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays HierarchicalProjectedSlice
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

local instance upperDualFintype : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projected upper)

def useful (X : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background) : Prop :=
  HierarchicalUsefulness.mark slots upper lowerLevel original arrays lowerEvent κ
    ⟨background, X⟩ = true

def leftLaw : FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  HierarchicalLeftDecoder.adviceLaw slots upper lowerLevel background σ
    (useful slots upper lowerLevel background original arrays lowerEvent κ) r ρ A
    (A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (visibleMatrix slots projected projection upper A known)))

theorem leftLaw_congr
    (projected₂ : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (projection₂ : ∀ s j, MixedSupport.Projection (slots s j) (projected₂ s j))
    (known₂ : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      NodeEmbedding.NodeH projected₂ upper)
    (hU : A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (visibleMatrix slots projected projection upper A known)) =
      A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (visibleMatrix slots projected₂ projection₂ upper A known₂))) :
    leftLaw slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known =
      leftLaw slots projected₂ projection₂ upper lowerLevel background original arrays lowerEvent κ σ ρ A known₂ := by
  unfold leftLaw
  rw [hU]

theorem leftLaw_eq_affine
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    leftLaw slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known =
      LeftDecoder.affineLaw
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace
        (correction slots upper lowerLevel background
          (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) := by
  have h := LeftDecoder.adviceLaw_of_good (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background) σ
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
      (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background)
      (useful slots upper lowerLevel background original arrays lowerEvent κ) r ρ A
      (A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (visibleMatrix slots projected projection upper A known))) hgood
  dsimp only [leftLaw, HierarchicalLeftDecoder.adviceLaw, LeftDecoder.law, LeftDecoder.center,
    HierarchicalProjectedSlice.witness, TensorSelectedSlice.witness, HierarchicalProjectedSlice.correction,
    HierarchicalProjectedSlice.table, HierarchicalUsefulness.table, HierarchicalFrozenTables.table,
    useful] at h ⊢
  exact h

theorem columnSpace_eq_nativeQ
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      AffineDecoderMeeting.nativeQ (ProjectedNodeEmbedding.intoOriginal projection upper)
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace :=
  HierarchicalProjectedSlice.columnSpace_eq_pulled slots projected projection upper lowerLevel background
    original arrays lowerEvent κ σ ρ A known hgood

theorem nativeCorrection_eq_nativeCenter
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    nativeCorrection slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      AffineDecoderMeeting.nativeCenter (ProjectedNodeEmbedding.intoOriginal projection upper)
        (correction slots upper lowerLevel background
          (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) := rfl

variable (lower : Nodes branch n) (a : Block rows lower)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)
  (input : OwnInputReference.Input projected rows upper lower (LinearMap.ker A) a)

theorem meeting_probability_ge_coset
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (threshold : ℝ) :
    (1 / (2 : ℝ) ^ r) *
        (RightDecoder.law projected rows upper lower (LinearMap.ker A) a repeats cut σ input threshold).probability
          (fun decoded => decide (decoded -
            nativeCorrection slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood ∈
            columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)) ≤
      ((leftLaw slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known).product
        (RightDecoder.law projected rows upper lower (LinearMap.ker A) a repeats cut σ input threshold)).probability
          (fun pair => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap pair.1 = pair.2)) := by
  rw [leftLaw_eq_affine slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood]
  apply AffineDecoderMeeting.product_probability_lower
  intro decoded hdecoded
  have bound := AffineDecoderMeeting.native_point_probability_lower (ProjectedNodeEmbedding.intoOriginal projection upper)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace
    (correction slots upper lowerLevel background
      (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value)
    (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).column_count decoded (by
      have hd := of_decide_eq_true hdecoded
      simpa only [columnSpace_eq_nativeQ slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood,
        nativeCorrection_eq_nativeCenter slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood]
        using hd)
  convert bound using 1
  congr 1
  funext candidate
  exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl

theorem meeting_probability_lower
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true)
    (ρpred h₀ : ℝ) (hρpred : 0 < ρpred) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hslice : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hlist : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ (ρpred * h₀ / 4) ^ 2 / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 (LinearMap.ker A) < ρpred / 8)
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ (r * rows (Nodes.height upper)))
    (hmatch : ρpred ≤ RightDecoderWitness.conditionalMatch projected rows upper lower
      (LinearMap.ker A) a repeats cut σ input
      (columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (target slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne)
      (nativeCorrection slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (visibleOffset slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)) :
    (1 / (2 : ℝ) ^ r) *
        ((ρpred * h₀ / 4) ^ 2 / (2 * (2 : ℝ) ^ rows (Nodes.height upper))) ≤
      ((leftLaw slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known).product
        (RightDecoder.law projected rows upper lower (LinearMap.ker A) a repeats cut σ input
          (ρpred * h₀ / 4))).probability
          (fun pair => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap pair.1 = pair.2)) := by
  have hdimension := TensorSliceDimension.equation_finrank_le (LinearMap.ker A)
    (columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    (HierarchicalProjectedSlice.finrank_columnSpace_le slots projected projection upper lowerLevel background
      original arrays lowerEvent κ σ ρ A known hgood)
  have hsize' : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2
      ((columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) →ₗ[F2]
        LinearMap.ker A) :=
    hsize.trans (one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 2) hdimension)
  have hright := RightDecoderAffineSuccess.coset_probability_lower projected rows upper lower
    (LinearMap.ker A) a repeats cut σ input ρpred h₀ hρpred hh₀ hrep hslice hlist hexcluded
    (columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    hsize'
    (target slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne)
    (nativeCorrection slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    (visibleOffset slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) hmatch
  exact (mul_le_mul_of_nonneg_left hright
    (div_nonneg zero_le_one (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r))).trans
      (meeting_probability_ge_coset slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known
        lower a repeats cut input hgood (ρpred * h₀ / 4))

end
end PerfectCompleteness.HierarchicalProjectedMeeting


namespace PerfectCompleteness.ProjectedRawAssembly

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s k, MixedSupport.Projection (originalSlots s k) (projectedSlots s k))
  (rows : Nat → Nat) (upper lower : Nodes branch n)

def exteriorBackground
    (external : OwnInputReference.Exterior projectedSlots rows upper lower) :
    HierarchicalMatrixTable.Background (rows := rows) originalSlots upper :=
  fun node row => ProjectedNodeEmbedding.nativePullback projection node.val
    (OwnInputRawAssembly.exteriorBackground projectedSlots rows upper lower external node row)

variable (W : Submodule F2 (Block rows upper))
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

def arrays
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    Arrays originalSlots rows :=
  ChildBlockProjection.arraysPullback rows projection
    (OwnInputRawAssembly.arrays projectedSlots rows upper lower W repeats cut sample)

def background
    (visible : OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.Background (rows := rows) originalSlots upper :=
  exteriorBackground originalSlots projectedSlots projection rows upper lower visible.2

def visibleMatrix
    (visible : OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower W repeats cut) :
    Module.Dual F2 (NodeEmbedding.RowSpace originalSlots upper) →ₗ[F2] Block rows upper :=
  HierarchicalTensorMatrix.visibleMatrix originalSlots upper W
    (fun v => ProjectedNodeEmbedding.nativePullback projection upper
      (OwnInputRawAssembly.knownVisible projectedSlots rows upper lower W repeats cut visible v))

theorem visibleMatrix_apply
    (visible : OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower W repeats cut)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace originalSlots upper)) :
    visibleMatrix originalSlots projectedSlots projection rows upper lower W repeats cut visible q =
      ∑ v : HiddenBucketBias.VisibleDirection W,
        (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.knownVisible projectedSlots rows upper lower W repeats cut visible v) •
            v.val.val :=
  HierarchicalTensorMatrix.visibleMatrix_apply originalSlots upper W
    (fun v => ProjectedNodeEmbedding.nativePullback projection upper
      (OwnInputRawAssembly.knownVisible projectedSlots rows upper lower W repeats cut visible v)) q

theorem arrays_upper
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut)
    (row : Fin (rows (Nodes.height upper))) :
    arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample upper row =
      ProjectedNodeEmbedding.nativePullback projection upper
        (BucketSampler.evaluate (rows (Nodes.height upper))
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
          (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower W repeats cut sample) row) := by
  change ProjectedNodeEmbedding.nativePullback projection upper
    (OwnInputRawAssembly.arrays projectedSlots rows upper lower W repeats cut sample upper row) = _
  rw [OwnInputRawAssembly.arrays_upper]

theorem background_arrays
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.backgroundOf originalSlots upper
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) =
      background originalSlots projectedSlots projection rows upper lower W repeats cut sample.2 := by
  funext node row
  exact congrArg
    (fun bg : HierarchicalMatrixTable.Background (rows := rows) projectedSlots upper =>
      ProjectedNodeEmbedding.nativePullback projection node.val (bg node row))
    (OwnInputRawAssembly.background_arrays projectedSlots rows upper lower W repeats cut sample)

theorem arrays_eq_matrix_assemble
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample =
      HierarchicalMatrixTable.assemble originalSlots upper
        (background originalSlots projectedSlots projection rows upper lower W repeats cut sample.2)
        (NodeEmbedding.matrix
          (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) upper) := by
  have h := HierarchicalMatrixTable.assemble_original originalSlots upper
    (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample)
  rw [background_arrays] at h
  exact h.symm

theorem matrix_arrays
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    NodeEmbedding.matrix
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) upper =
      TensorProjectedSlice.totalMatrix (ProjectedNodeEmbedding.intoOriginal projection upper) W
        (visibleMatrix originalSlots projectedSlots projection rows upper lower W repeats cut sample.2)
        (OwnInputAffineSlice.hiddenOutput projectedSlots rows upper lower W repeats cut sample) := by
  apply LinearMap.ext
  intro q
  have hsplit := TensorBucketEvaluation.evaluate_splitTape W
    (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
    (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
    (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower W repeats cut sample)
  rw [OwnInputRawAssembly.split_mergedTape] at hsplit
  calc
    NodeEmbedding.matrix
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) upper q =
        (fun row => (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.arrays projectedSlots rows upper lower W repeats cut sample upper row)) := rfl
    _ = (fun row => (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
        (BucketSampler.evaluate (rows (Nodes.height upper))
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
          (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower W repeats cut sample) row)) := by
      rw [OwnInputRawAssembly.arrays_upper]
    _ = TensorBucketEvaluation.visibleOutput W
          (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2.1 +
        TensorBucketEvaluation.tensorOutput W
          (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputAffineSlice.hiddenOutput projectedSlots rows upper lower W repeats cut sample) := hsplit
    _ = _ := by
      rw [TensorProjectedSlice.totalMatrix_apply,
        TensorProjectedSlice.includedEvaluation_eq_tensorOutput, visibleMatrix_apply]
      rfl

end
end PerfectCompleteness.ProjectedRawAssembly


namespace PerfectCompleteness.SourceProjectedCanonicalQuery

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
  (rows : Nat → Nat)
  (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))

def query {Y : Type*} (arrays : Arrays slots rows) (post : Output branch n rows → Y) :
    MixedSupport.Assignment (TreeCanonical.numberedSlots slots) → Y :=
  post ∘ TreeCanonical.numberedFunction slots (fullJoint arrays)

theorem query_pullback {Y : Type*} (arrays : Arrays projected rows)
    (post : Output branch n rows → Y) :
    query rows (ChildBlockProjection.arraysPullback rows p arrays) post =
      query rows arrays post ∘ MixedSupport.projectionMap (TreeCanonical.numberedProjection p) := by
  funext x
  change post (fullJoint (ChildBlockProjection.arraysPullback rows p arrays)
      ((TreeCanonical.assignmentEquiv slots).symm x)) =
    post (fullJoint arrays ((TreeCanonical.assignmentEquiv projected).symm
      (MixedSupport.projectionMap (TreeCanonical.numberedProjection p) x)))
  rw [ChildBlockProjection.fullJoint_pullback, TreeCanonical.assignmentEquiv_symm_projection]

theorem key_pullback {Y : Type*} (arrays : Arrays projected rows)
    (post : Output branch n rows → Y) (side : CanonicalKeys.Side) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots slots)
        (query rows (ChildBlockProjection.arraysPullback rows p arrays) post) =
      CanonicalKeys.key side (TreeCanonical.numberedSlots projected) (query rows arrays post) := by
  rw [query_pullback]
  exact CanonicalKeys.key_projection side (TreeCanonical.numberedProjection p) (query rows arrays post)

theorem label_val_pullback {Y : Type*} (arrays : Arrays projected rows)
    (post : Output branch n rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    (KeyStrategy.label labeling side (TreeCanonical.numberedSlots slots)
        (query rows (ChildBlockProjection.arraysPullback rows p arrays) post)).val =
      (KeyStrategy.label labeling side (TreeCanonical.numberedSlots projected)
        (query rows arrays post)).val :=
  KeyStrategy.label_val_eq_of_key_eq labeling side side _ _ _ _
    (key_pullback rows p arrays post side)

theorem response_pullback {Y : Type*} (arrays : Arrays projected rows)
    (post : Output branch n rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
        (query rows (ChildBlockProjection.arraysPullback rows p arrays) post) =
      KeyStrategy.response labeling side (TreeCanonical.numberedSlots projected)
        (query rows arrays post) := by
  rw [query_pullback]
  exact KeyStrategy.response_projection labeling side (TreeCanonical.numberedProjection p)
    (query rows arrays post)

theorem canonicalQuery_pullback (lower : Nodes branch n) (a : Block rows lower)
    (arrays : Arrays projected rows) :
    OwnInputCanonicalQuery.canonicalQuery slots rows lower a
        (ChildBlockProjection.arraysPullback rows p arrays) =
      OwnInputCanonicalQuery.canonicalQuery projected rows lower a arrays ∘
        MixedSupport.projectionMap (TreeCanonical.numberedProjection p) :=
  query_pullback rows p arrays (BlockQuotient.projectBlock lower a)

theorem canonical_response_pullback (lower : Nodes branch n) (a : Block rows lower)
    (arrays : Arrays projected rows)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
        (OwnInputCanonicalQuery.canonicalQuery slots rows lower a
          (ChildBlockProjection.arraysPullback rows p arrays)) =
      KeyStrategy.response labeling side (TreeCanonical.numberedSlots projected)
        (OwnInputCanonicalQuery.canonicalQuery projected rows lower a arrays) :=
  response_pullback rows p arrays (BlockQuotient.projectBlock lower a) labeling side

theorem response_readInput_hidden (upper lower : Nodes branch n) (hne : upper ≠ lower)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper)) (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace projected upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior projected rows upper lower) :
    OwnInputReference.response projected rows upper lower W a labeling
        (OwnInputReference.readInput projected rows upper lower W a eval
          ((HiddenBucketBias.splitTape W Ω tape).2, external))
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (OwnInputCanonicalQuery.canonicalQuery slots rows lower a
          (ChildBlockProjection.arraysPullback rows p
            (OwnInputCanonicalQuery.assemble projected rows upper lower
              (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external)))).2.1
                ⟨upper, hne⟩ := by
  have h := OwnInputCanonicalQuery.response_readInput_hidden_eq projected rows upper lower
    hne W a labeling eval tape external
  rw [← canonical_response_pullback rows p lower a
    (OwnInputCanonicalQuery.assemble projected rows upper lower
      (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) labeling .right] at h
  exact h

theorem response_readInput_hidden_arrays (upper lower : Nodes branch n) (hne : upper ≠ lower)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper)) (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace projected upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (arrays : Arrays projected rows)
    (hupper : BucketSampler.evaluate (rows (Nodes.height upper)) eval tape = arrays upper) :
    OwnInputReference.response projected rows upper lower W a labeling
        (OwnInputReference.readInput projected rows upper lower W a eval
          ((HiddenBucketBias.splitTape W Ω tape).2,
            OwnInputCanonicalQuery.exteriorOf projected rows upper lower arrays))
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (OwnInputCanonicalQuery.canonicalQuery slots rows lower a
          (ChildBlockProjection.arraysPullback rows p arrays))).2.1 ⟨upper, hne⟩ :=
  (OwnInputCanonicalQuery.response_readInput_hidden_arrays projected rows upper lower
    hne W a labeling eval tape arrays hupper).trans
      (congrArg (fun value : OwnInputCanonicalQuery.CanonicalOutput rows lower a =>
        value.2.1 ⟨upper, hne⟩)
          (canonical_response_pullback rows p lower a arrays labeling .right).symm)

end
end PerfectCompleteness.SourceProjectedCanonicalQuery


namespace PerfectCompleteness.HierarchicalProjectedRawPrediction

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (rows : Nat → Nat) (upper lower : Nodes branch n) (lowerLevel : Nat)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace originalSlots upper) :=
  Fintype.ofFinite _

local instance valueFintype : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

abbrev Raw := OwnInputReference.RawSample projectedSlots rows upper lower (LinearMap.ker A) repeats cut
abbrev Visible := OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower (LinearMap.ker A) repeats cut

abbrev rawArrays (sample : Raw projectedSlots rows upper lower A repeats cut) :=
  ProjectedRawAssembly.arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut sample

abbrev rawBackground (sample : Raw projectedSlots rows upper lower A repeats cut) :=
  HierarchicalMatrixTable.backgroundOf originalSlots upper
    (rawArrays originalSlots projectedSlots projection rows upper lower A repeats cut sample)

abbrev rawMatrix (sample : Raw projectedSlots rows upper lower A repeats cut) :=
  NodeEmbedding.matrix (rawArrays originalSlots projectedSlots projection rows upper lower A repeats cut sample) upper

abbrev visibleBackground (v : Visible projectedSlots rows upper lower A repeats cut) :=
  ProjectedRawAssembly.background originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut v

abbrev known (v : Visible projectedSlots rows upper lower A repeats cut) :=
  OwnInputRawAssembly.knownVisible projectedSlots rows upper lower (LinearMap.ker A) repeats cut v

abbrev hidden (sample : Raw projectedSlots rows upper lower A repeats cut) :=
  OwnInputAffineSlice.hiddenOutput projectedSlots rows upper lower (LinearMap.ker A) repeats cut sample

theorem response_eq_canonical (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : Raw projectedSlots rows upper lower A repeats cut) :
    OwnInputReference.response projectedSlots rows upper lower (LinearMap.ker A) a labeling
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2)
        (hidden projectedSlots rows upper lower A repeats cut sample) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots originalSlots)
        (OwnInputCanonicalQuery.canonicalQuery originalSlots rows lower a
          (rawArrays originalSlots projectedSlots projection rows upper lower A repeats cut sample))).2.1
            ⟨upper, cut.upper_ne_lower⟩ := by
  have h := SourceProjectedCanonicalQuery.response_readInput_hidden rows projection upper lower
    cut.upper_ne_lower (LinearMap.ker A) a labeling
    (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
    (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower (LinearMap.ker A) repeats cut sample)
    sample.2.2
  rw [OwnInputRawAssembly.split_mergedTape] at h
  exact h

theorem response_eq_rightUpper (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : Raw projectedSlots rows upper lower A repeats cut) :
    OwnInputReference.response projectedSlots rows upper lower (LinearMap.ker A) a labeling
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2)
        (hidden projectedSlots rows upper lower A repeats cut sample) =
      HierarchicalPrediction.rightUpper originalSlots upper
        (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample.2)
        labeling lower cut.upper_ne_lower a
        (rawMatrix originalSlots projectedSlots projection rows upper lower A repeats cut sample) := by
  dsimp only [visibleBackground, rawMatrix, rawArrays]
  rw [← ProjectedRawAssembly.background_arrays originalSlots projectedSlots projection rows upper lower
    (LinearMap.ker A) repeats cut sample,
    HierarchicalPrediction.rightUpper, HierarchicalMatrixTable.displayed_original]
  exact response_eq_canonical originalSlots projectedSlots projection rows upper lower A repeats cut
    a labeling sample

theorem response_eq_rightUpper_totalMatrix (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : Raw projectedSlots rows upper lower A repeats cut) :
    OwnInputReference.response projectedSlots rows upper lower (LinearMap.ker A) a labeling
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2)
        (hidden projectedSlots rows upper lower A repeats cut sample) =
      HierarchicalPrediction.rightUpper originalSlots upper
        (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample.2)
        labeling lower cut.upper_ne_lower a
        (HierarchicalProjectedSlice.matrix originalSlots projectedSlots projection upper A
          (known projectedSlots rows upper lower A repeats cut sample.2)
          (hidden projectedSlots rows upper lower A repeats cut sample)) := by
  exact (response_eq_rightUpper originalSlots projectedSlots projection rows upper lower A repeats cut
    a labeling sample).trans (congrArg
      (fun X : HierarchicalMatrixTable.Matrix (rows := rows) originalSlots upper =>
        HierarchicalPrediction.rightUpper originalSlots upper
          (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample.2)
          labeling lower cut.upper_ne_lower a X)
      (ProjectedRawAssembly.matrix_arrays originalSlots projectedSlots projection rows upper lower
        (LinearMap.ker A) repeats cut sample))

def rawJ (sample : Raw projectedSlots rows upper lower A repeats cut) : Bool :=
  GoodAdviceEvents.J
    (HierarchicalUsefulness.table originalSlots upper lowerLevel original originalArrays lowerEvent κ σ
      (rawBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample)) r ρ
    (A, HierarchicalPrediction.quotientMatrix originalSlots upper lowerLevel
      (rawBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample)
      (rawMatrix originalSlots projectedSlots projection rows upper lower A repeats cut sample))

def rawPrediction (a : Block rows lower)
    (sample : Raw projectedSlots rows upper lower A repeats cut) : Bool :=
  HierarchicalPrediction.prediction originalSlots upper lowerLevel
    (rawBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample) σ lower cut.upper_ne_lower a
    original originalArrays lowerEvent κ r ρ A (rawMatrix originalSlots projectedSlots projection rows upper lower A repeats cut sample)

abbrev VisibleGood (v : Visible projectedSlots rows upper lower A repeats cut) : Prop :=
  HierarchicalProjectedSlice.VisibleGood originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)

abbrev tensorJ (v : Visible projectedSlots rows upper lower A repeats cut)
    (T : HierarchicalProjectedSlice.HiddenTensor projectedSlots upper A) : Bool :=
  HierarchicalProjectedSlice.J originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) T

abbrev columnSpace (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalProjectedSlice.columnSpace originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) hgood

abbrev target (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true) :=
  HierarchicalProjectedSlice.target originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) hgood hne

abbrev nativeCorrection (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalProjectedSlice.nativeCorrection originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) hgood

abbrev visibleOffset (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) :=
  HierarchicalProjectedSlice.visibleOffset originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v) hgood

theorem rawJ_eq_tensorJ (sample : Raw projectedSlots rows upper lower A repeats cut) :
    rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut sample =
      tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut
        sample.2 (hidden projectedSlots rows upper lower A repeats cut sample) := by
  exact congrArg₂
    (fun (b : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)
        (X : HierarchicalMatrixTable.Matrix (rows := rows) originalSlots upper) =>
      GoodAdviceEvents.J
        (HierarchicalUsefulness.table originalSlots upper lowerLevel original originalArrays lowerEvent κ σ b)
        r ρ (A, HierarchicalPrediction.quotientMatrix originalSlots upper lowerLevel b X))
    (ProjectedRawAssembly.background_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut sample)
    (ProjectedRawAssembly.matrix_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut sample)

theorem rawJ_iff_restriction (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true)
    (sample : Raw projectedSlots rows upper lower A repeats cut) (hv : sample.2 = v) :
    rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut sample =
        true ↔
      TensorRestriction.restrictionMap
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) (hidden projectedSlots rows upper lower A repeats cut sample) =
        target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne := by
  rw [rawJ_eq_tensorJ, hv]
  exact HierarchicalProjectedSlice.J_iff_restriction originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)
    hgood hne _

def responseMatch (a : Block rows lower) (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) (sample : Raw projectedSlots rows upper lower A repeats cut) : Bool :=
  decide (OwnInputReference.response projectedSlots rows upper lower (LinearMap.ker A) a σ
      (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2)
      (hidden projectedSlots rows upper lower A repeats cut sample) =
    visibleOffset originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v hgood +
      TensorBucketEvaluation.tensorOutputLinear (LinearMap.ker A)
        (nativeCorrection originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) (hidden projectedSlots rows upper lower A repeats cut sample))

theorem rawPrediction_eq (a : Block rows lower) (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) (sample : Raw projectedSlots rows upper lower A repeats cut) (hv : sample.2 = v) :
    rawPrediction originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a sample =
      (rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut sample &&
      responseMatch originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a v hgood sample) := by
  have hbg := ProjectedRawAssembly.background_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A)
    repeats cut sample
  have hmat := ProjectedRawAssembly.matrix_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A)
    repeats cut sample
  have hresponse := response_eq_rightUpper_totalMatrix originalSlots projectedSlots projection rows upper lower A repeats cut a σ sample
  rw [hv] at hbg hmat hresponse
  change rawBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample =
    visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v at hbg
  change rawMatrix originalSlots projectedSlots projection rows upper lower A repeats cut sample =
    HierarchicalProjectedSlice.matrix originalSlots projectedSlots projection upper A
      (known projectedSlots rows upper lower A repeats cut v)
      (hidden projectedSlots rows upper lower A repeats cut sample) at hmat
  have hprediction := congrArg₂
    (fun (b : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)
        (X : HierarchicalMatrixTable.Matrix (rows := rows) originalSlots upper) =>
      HierarchicalPrediction.prediction originalSlots upper lowerLevel b σ lower cut.upper_ne_lower a
        original originalArrays lowerEvent κ r ρ A X) hbg hmat
  unfold rawPrediction
  rw [hprediction, rawJ_eq_tensorJ]
  simp only [hv]
  dsimp only [HierarchicalPrediction.prediction]
  rw [HierarchicalProjectedSlice.selectedValue_eq_some originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)
    hgood (hidden projectedSlots rows upper lower A repeats cut sample)]
  dsimp only
  rw [HierarchicalProjectedSlice.affinePrediction_eq_tensor originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)
    hgood (hidden projectedSlots rows upper lower A repeats cut sample), ← hresponse]
  simp only [tensorJ, HierarchicalProjectedSlice.J, responseMatch, hv,
    TensorBucketEvaluation.tensorOutput]
  all_goals
    apply congrArg₂ (fun first second : Bool => first && second)
    · rfl
    · exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl

def given (v : Visible projectedSlots rows upper lower A repeats cut)
    (sample : Raw projectedSlots rows upper lower A repeats cut) : Bool :=
  rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
    A repeats cut sample && decide (sample.2 = v)

theorem given_eq_jointEvent (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true) :
    given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v =
      OwnInputAffineSlice.jointEvent projectedSlots rows upper lower (LinearMap.ker A) repeats cut
        (fun data => decide (data = v))
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne) := by
  funext sample
  by_cases hv : sample.2 = v
  · have hJ : rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut sample =
      OwnInputAffineSlice.tensorSlice (LinearMap.ker A)
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne) (hidden projectedSlots rows upper lower A repeats cut sample) := by
      apply Bool.eq_iff_iff.mpr
      simp only [OwnInputAffineSlice.tensorSlice, decide_eq_true_eq]
      exact rawJ_iff_restriction originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood hne sample hv
    unfold given OwnInputAffineSlice.jointEvent
    rw [hJ]
  · simp only [given, OwnInputAffineSlice.jointEvent, hv, decide_false, Bool.and_false]

theorem selection_of_positive
    (externalLaw : FiniteDistribution (OwnInputReference.Exterior projectedSlots rows upper lower))
    (v : Visible projectedSlots rows upper lower A repeats cut)
    (positive : 0 <
      (OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).probability
        (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)) :
    VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v ∧
      ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v T = true := by
  have hex : ∃ sample, given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v sample = true := by
    by_contra hnone
    have hfalse : given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v = fun _ => false := by
      funext sample
      exact Bool.eq_false_iff.mpr (fun hs => hnone ⟨sample, hs⟩)
    rw [hfalse, FiniteDistribution.probability_false] at positive
    exact (lt_irrefl 0) positive
  obtain ⟨sample, hs⟩ := hex
  have hp := Bool.and_eq_true_iff.mp hs
  have hv : sample.2 = v := @of_decide_eq_true _ _ hp.2
  have ht := hp.1
  rw [rawJ_eq_tensorJ, hv] at ht
  refine ⟨?_, hidden projectedSlots rows upper lower A repeats cut sample, ht⟩
  by_contra hbad
  have hfalse := HierarchicalProjectedSlice.J_false_of_not_good originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)
    hbad (hidden projectedSlots rows upper lower A repeats cut sample)
  exact Bool.noConfusion (hfalse.symm.trans ht)

theorem conditional_prediction_eq (a : Block rows lower)
    (externalLaw : FiniteDistribution (OwnInputReference.Exterior projectedSlots rows upper lower))
    (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true)
    (positive : 0 <
      (OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).probability
        (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)) :
    ((OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).condition
      (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)
      positive).probability
        (rawPrediction originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut a) =
      RightDecoderWitness.conditionalMatch projectedSlots rows upper lower (LinearMap.ker A) a repeats cut σ
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) v)
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne)
        (nativeCorrection originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (visibleOffset originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) := by
  let μ := OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw
  let joint := OwnInputAffineSlice.jointEvent projectedSlots rows upper lower (LinearMap.ker A) repeats cut
    (fun data => decide (data = v))
    (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v hgood)
    (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v hgood hne)
  have hgiven : given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v = joint :=
    given_eq_jointEvent originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v hgood hne
  have hpositive : 0 < μ.probability joint := by
    rw [← hgiven]
    exact positive
  trans (μ.condition
    (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)
    positive).probability
      (responseMatch originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a v hgood)
  · apply OwnInputAffineSlice.probability_condition_congr
    intro sample hs
    have hp := Bool.and_eq_true_iff.mp hs
    have hv : sample.2 = v := @of_decide_eq_true _ _ hp.2
    rw [rawPrediction_eq originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut a v hgood sample hv, hp.1, Bool.true_and]
  trans (μ.condition joint hpositive).probability
    (responseMatch originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut a v hgood)
  · simp only [FiniteDistribution.probability_condition, hgiven]
  · exact OwnInputAffineSlice.conditional_response_probability projectedSlots rows upper lower (LinearMap.ker A)
      a repeats cut externalLaw (fun data => decide (data = v))
      (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)
      (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood hne) hpositive σ
      (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) v)
      (by
        intro data hdata
        have hv : data = v := @of_decide_eq_true _ _ hdata
        subst data
        rfl)
      (nativeCorrection originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)
      (visibleOffset originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
