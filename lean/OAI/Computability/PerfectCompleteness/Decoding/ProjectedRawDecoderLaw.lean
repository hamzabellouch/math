import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedSliceLemmas

namespace OAI

section

namespace PerfectCompleteness.ProjectedRawDecoderLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (rows : Nat → Nat) (upper lower : Nodes branch n) (level : Nat)

local instance upperDualFintype : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

theorem advice_eq_visible
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
    (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)
    (raw : OwnInputReference.RawSample projected rows upper lower (LinearMap.ker A) repeats cut) :
    A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper level background)
        (NodeEmbedding.matrix
          (ProjectedRawAssembly.arrays slots projected projection rows upper lower
            (LinearMap.ker A) repeats cut raw) upper)) =
      A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper level background)
        (HierarchicalProjectedSlice.visibleMatrix slots projected projection upper A
          (HierarchicalProjectedRawPrediction.known projected rows upper lower A repeats cut raw.2))) := by
  rw [ProjectedRawAssembly.matrix_arrays]
  exact TensorRowAdvice.rowAdvice_projectMatrix
    (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A) A le_rfl
    (HierarchicalFrozenTables.knownRows slots upper level background)
    (ProjectedRawAssembly.visibleMatrix slots projected projection rows upper lower
      (LinearMap.ker A) repeats cut raw.2)
    (OwnInputAffineSlice.hiddenOutput projected rows upper lower (LinearMap.ker A) repeats cut raw)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays slots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

theorem adviceLaw_eq_leftLaw
    (raw : OwnInputReference.RawSample projected rows upper lower (LinearMap.ker A) repeats cut) :
    let actual := ProjectedRawAssembly.arrays slots projected projection rows upper lower
      (LinearMap.ker A) repeats cut raw
    let background := HierarchicalMatrixTable.backgroundOf slots upper actual
    HierarchicalLeftDecoder.adviceLaw slots upper level background σ
        (HierarchicalProjectedMeeting.useful slots upper level background
          original originalArrays lowerEvent κ) r ρ A
        (A.comp (MatrixRowQuotient.projectMatrix
          (HierarchicalFrozenTables.knownRows slots upper level background)
          (NodeEmbedding.matrix actual upper))) =
      HierarchicalProjectedMeeting.leftLaw slots projected projection upper level
        (HierarchicalProjectedRawPrediction.visibleBackground
          slots projected projection rows upper lower A repeats cut raw.2)
        original originalArrays lowerEvent κ σ ρ A
        (HierarchicalProjectedRawPrediction.known projected rows upper lower A repeats cut raw.2) := by
  dsimp only
  rw [ProjectedRawAssembly.background_arrays]
  unfold HierarchicalProjectedMeeting.leftLaw
  rw [advice_eq_visible slots projected projection rows upper lower level
    (ProjectedRawAssembly.background slots projected projection rows upper lower
      (LinearMap.ker A) repeats cut raw.2) A repeats cut raw]

end
end PerfectCompleteness.ProjectedRawDecoderLaw

end

end OAI
