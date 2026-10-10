import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.Computability.PerfectCompleteness.Algebra.AffineDecoderMeeting
import OAI.Computability.PerfectCompleteness.Algebra.RightDecoderAffineSuccess
import OAI.Computability.PerfectCompleteness.Algebra.TensorRowAdviceLemmas
import OAI.Computability.PerfectCompleteness.Algebra.TensorSliceDimension
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalLeftDecoder
import OAI.Computability.PerfectCompleteness.Reduction.FixedRows

namespace OAI


namespace PerfectCompleteness.HierarchicalDecoderMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays HierarchicalTensorSlice
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

private theorem affine_meeting_probability_lower
    {source native : Type*} [AddCommGroup source] [Module F2 source]
    [AddCommGroup native] [Module F2 native]
    [FiniteDimensional F2 source] [FiniteDimensional F2 native]
    (embedding : native →ₗ[F2] source) (knownRows : Submodule F2 source)
    (columns : Submodule F2 (Module.Dual F2 (source ⧸ knownRows)))
    (center : Module.Dual F2 source) {dimension : Nat}
    (hcolumns : Module.finrank F2 columns ≤ dimension)
    [nativeFintype : Fintype (Module.Dual F2 native)]
    (right : FiniteDistribution (Module.Dual F2 native)) :
    letI : Fintype (Module.Dual F2 source) := LeftDecoder.dualFintype (V := source)
    ∀ (left : FiniteDistribution (Module.Dual F2 source))
      (nativeColumns : Submodule F2 (Module.Dual F2 native)) (offset : Module.Dual F2 native),
      left = LeftDecoder.affineLaw knownRows columns center →
      nativeColumns = AffineDecoderMeeting.nativeQ embedding knownRows columns →
      offset = AffineDecoderMeeting.nativeCenter embedding center →
      (1 / (2 : ℝ) ^ dimension) * right.probability
        (fun decoded => decide (decoded - offset ∈ nativeColumns)) ≤
        (left.product right).probability
          (fun pair => decide (embedding.dualMap pair.1 = pair.2)) := by
  intro left nativeColumns offset hleft hcolumns' hoffset
  rw [hleft, hcolumns', hoffset]
  cases Subsingleton.elim nativeFintype (LeftDecoder.dualFintype (V := native))
  exact AffineDecoderMeeting.meeting_probability_lower embedding knownRows columns center hcolumns right

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
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
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH slots upper)

def useful (X : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background) : Prop :=
  HierarchicalUsefulness.mark slots upper lowerLevel original arrays lowerEvent κ
    ⟨background, X⟩ = true

def leftLaw : FiniteDistribution (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  HierarchicalLeftDecoder.adviceLaw slots upper lowerLevel background σ
    (useful slots upper lowerLevel background original arrays lowerEvent κ) r ρ A
    (A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (visibleMatrix slots upper A known)))

theorem leftLaw_eq_affine
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    leftLaw slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known =
      LeftDecoder.affineLaw
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace
        (correction slots upper lowerLevel background
          (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) := by
  have h := LeftDecoder.adviceLaw_of_good (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background) σ
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
      (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background)
      (useful slots upper lowerLevel background original arrays lowerEvent κ) r ρ A
      (A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (visibleMatrix slots upper A known))) hgood
  dsimp only [leftLaw, HierarchicalLeftDecoder.adviceLaw, LeftDecoder.law, LeftDecoder.center,
    HierarchicalTensorSlice.witness, TensorSelectedSlice.witness, HierarchicalTensorSlice.correction,
    HierarchicalTensorSlice.table, HierarchicalUsefulness.table, HierarchicalFrozenTables.table,
    useful] at h ⊢
  exact h

theorem columnSpace_eq_nativeQ
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      AffineDecoderMeeting.nativeQ (NodeEmbedding.embed slots upper)
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace :=
  HierarchicalTensorSlice.columnSpace_eq_pulled slots upper lowerLevel background
    original arrays lowerEvent κ σ ρ A known hgood

theorem nativeCorrection_eq_nativeCenter
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    nativeCorrection slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      AffineDecoderMeeting.nativeCenter (NodeEmbedding.embed slots upper)
        (correction slots upper lowerLevel background
          (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) := rfl

variable (lower : Nodes branch n) (a : Block rows lower)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)
  (input : OwnInputReference.Input slots rows upper lower (LinearMap.ker A) a)

theorem meeting_probability_ge_coset
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (threshold : ℝ) :
    (1 / (2 : ℝ) ^ r) *
        (RightDecoder.law slots rows upper lower (LinearMap.ker A) a repeats cut σ input threshold).probability
          (fun decoded => decide (decoded -
            nativeCorrection slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood ∈
            columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)) ≤
      ((leftLaw slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known).product
        (RightDecoder.law slots rows upper lower (LinearMap.ker A) a repeats cut σ input threshold)).probability
          (fun pair => decide ((NodeEmbedding.embed slots upper).dualMap pair.1 = pair.2)) := by
  convert affine_meeting_probability_lower
      (source := NodeEmbedding.RowSpace slots upper)
      (native := OwnInputReference.UpperSpace slots upper)
      (NodeEmbedding.embed slots upper)
      (nativeFintype := RightDecoder.scalarFintype slots upper)
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace
      (correction slots upper lowerLevel background
        (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value)
      (witness slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).column_count
      (RightDecoder.law slots rows upper lower (LinearMap.ker A) a repeats cut σ input threshold)
      (leftLaw slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
      (columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (nativeCorrection slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (leftLaw_eq_affine slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (columnSpace_eq_nativeQ slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (nativeCorrection_eq_nativeCenter slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)

theorem meeting_probability_lower
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true)
    (ρpred h₀ : ℝ) (hρpred : 0 < ρpred) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hslice : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hlist : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ (ρpred * h₀ / 4) ^ 2 / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 (LinearMap.ker A) < ρpred / 8)
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ (r * rows (Nodes.height upper)))
    (hmatch : ρpred ≤ RightDecoderWitness.conditionalMatch slots rows upper lower
      (LinearMap.ker A) a repeats cut σ input
      (columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (target slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne)
      (nativeCorrection slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (visibleOffset slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)) :
    (1 / (2 : ℝ) ^ r) *
        ((ρpred * h₀ / 4) ^ 2 / (2 * (2 : ℝ) ^ rows (Nodes.height upper))) ≤
      ((leftLaw slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known).product
        (RightDecoder.law slots rows upper lower (LinearMap.ker A) a repeats cut σ input
          (ρpred * h₀ / 4))).probability
          (fun pair => decide ((NodeEmbedding.embed slots upper).dualMap pair.1 = pair.2)) := by
  have hdimension := TensorSliceDimension.equation_finrank_le (LinearMap.ker A)
    (columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    (HierarchicalTensorSlice.finrank_columnSpace_le slots upper lowerLevel background
      original arrays lowerEvent κ σ ρ A known hgood)
  have hsize' : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2
      ((columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) →ₗ[F2]
        LinearMap.ker A) :=
    hsize.trans (one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 2) hdimension)
  have hright := RightDecoderAffineSuccess.coset_probability_lower slots rows upper lower
    (LinearMap.ker A) a repeats cut σ input ρpred h₀ hρpred hh₀ hrep hslice hlist hexcluded
    (columnSpace slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    hsize'
    (target slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne)
    (nativeCorrection slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    (visibleOffset slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) hmatch
  exact (mul_le_mul_of_nonneg_left hright
    (div_nonneg zero_le_one (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r))).trans
      (meeting_probability_ge_coset slots upper lowerLevel background original arrays lowerEvent κ σ ρ A known
        lower a repeats cut input hgood (ρpred * h₀ / 4))

end
end PerfectCompleteness.HierarchicalDecoderMeeting


namespace PerfectCompleteness.HierarchicalFixedDecoderMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays HierarchicalTensorSlice
open UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

theorem kernel_finrank_ge {ℓ r : Nat} (A : ManyGoodRows.RowMap (Fin ℓ → F2) r) :
    ℓ - r ≤ Module.finrank F2 (LinearMap.ker A) := by
  have hrange : Module.finrank F2 (LinearMap.range A) ≤ r := by
    simpa only [Module.finrank_fin_fun] using (Submodule.finrank_le (LinearMap.range A))
  have hdim := LinearMap.finrank_range_add_finrank_ker A
  simp only [Module.finrank_fin_fun] at hdim
  change Module.finrank F2 (LinearMap.range A) + Module.finrank F2 (LinearMap.ker A) = ℓ at hdim
  omega

variable {δ : ℚ} (plan : FixedRows.Plan δ)

theorem repetitionsBalanced : RecursiveSamplerBias.RepetitionsBalanced (FixedRows.repeats plan) :=
  RecursiveSamplerBias.repetitionsBalanced_of_six_le (FixedRows.repeats plan)
    (fun k => plan.repeats_min (FixedRows.rows plan (k + 1)))

theorem slice_error (height : Nat) :
    (7 / 8 : ℝ) ^ FixedRows.repeats plan height ≤
      h plan.order (FixedRows.rows plan height) / 2 :=
  (plan.repeats_error (FixedRows.rows plan height)).trans (min_le_left _ _)

theorem list_error (height : Nat) :
    (7 / 8 : ℝ) ^ FixedRows.repeats plan height ≤
      tau (InitialParameters.useful δ) plan.density plan.order (FixedRows.rows plan height) ^ 2 / 2 :=
  (plan.repeats_error (FixedRows.rows plan height)).trans (min_le_right _ _)

theorem kernel_excluded (height : Nat)
    (A : ManyGoodRows.RowMap (Fin (FixedRows.rows plan height) → F2) plan.order) :
    1 / (2 : ℝ) ^ Module.finrank F2 (LinearMap.ker A) <
      rhoPred (InitialParameters.useful δ) plan.density / 8 := by
  have hker := kernel_finrank_ge A
  apply (one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 2) hker).trans_lt
  simpa only [FixedRows.rows, DescendingRows.treeRows] using
    plan.rows_correction (plan.depth - height)

variable (hδ : 0 < δ) {branch : Nat → Nat} {t : Nat}
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background
    (rows := FixedRows.rows plan) slots upper)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype : Fintype
    (Block (FixedRows.rows plan) upper ×
      HierarchicalMatrixTable.SideOutput (rows := FixedRows.rows plan) upper) :=
  Fintype.ofFinite _

local instance upperDualFintype : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH slots upper)
  (lower : Nodes branch plan.depth) (a : Block (FixedRows.rows plan) lower)
  (cut : OwnInputReference.Cut upper lower)
  (input : OwnInputReference.Input slots (FixedRows.rows plan) upper lower (LinearMap.ker A) a)

include hδ

theorem meeting_probability_lower
    (hgood : VisibleGood slots upper lowerLevel background original arrays lowerEvent
      (InitialParameters.useful δ) σ plan.density A known)
    (hne : ∃ T, J slots upper lowerLevel background original arrays lowerEvent
      (InitialParameters.useful δ) σ plan.density A known T = true)
    (hmatch : rhoPred (InitialParameters.useful δ) plan.density ≤
      RightDecoderWitness.conditionalMatch slots (FixedRows.rows plan) upper lower
        (LinearMap.ker A) a (FixedRows.repeats plan) cut σ input
        (columnSpace slots upper lowerLevel background original arrays lowerEvent
          (InitialParameters.useful δ) σ plan.density A known hgood)
        (target slots upper lowerLevel background original arrays lowerEvent
          (InitialParameters.useful δ) σ plan.density A known hgood hne)
        (nativeCorrection slots upper lowerLevel background original arrays lowerEvent
          (InitialParameters.useful δ) σ plan.density A known hgood)
        (visibleOffset slots upper lowerLevel background original arrays lowerEvent
          (InitialParameters.useful δ) σ plan.density A known hgood)) :
    (1 / (2 : ℝ) ^ plan.order) *
        (tau (InitialParameters.useful δ) plan.density plan.order
          (FixedRows.rows plan (Nodes.height upper)) ^ 2 /
            (2 * (2 : ℝ) ^ FixedRows.rows plan (Nodes.height upper))) ≤
      ((HierarchicalDecoderMeeting.leftLaw slots upper lowerLevel background original arrays lowerEvent
        (InitialParameters.useful δ) σ plan.density A known).product
        (RightDecoder.law slots (FixedRows.rows plan) upper lower (LinearMap.ker A) a
          (FixedRows.repeats plan) cut σ input
          (tau (InitialParameters.useful δ) plan.density plan.order
            (FixedRows.rows plan (Nodes.height upper))))).probability
          (fun pair => decide ((NodeEmbedding.embed slots upper).dualMap pair.1 = pair.2)) := by
  simpa only [UpperParameterScalars.tau] using
    (HierarchicalDecoderMeeting.meeting_probability_lower slots upper lowerLevel background
      original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known
      lower a (FixedRows.repeats plan) cut input hgood hne
      (rhoPred (InitialParameters.useful δ) plan.density)
      (h plan.order (FixedRows.rows plan (Nodes.height upper)))
      (rhoPred_pos (InitialParameters.useful_pos hδ) plan.density_pos)
      (h_pos plan.order (FixedRows.rows plan (Nodes.height upper)))
      (repetitionsBalanced plan) (slice_error plan (Nodes.height upper))
      (list_error plan (Nodes.height upper)) (kernel_excluded plan (Nodes.height upper) A)
      le_rfl hmatch)

end
end PerfectCompleteness.HierarchicalFixedDecoderMeeting

end OAI
