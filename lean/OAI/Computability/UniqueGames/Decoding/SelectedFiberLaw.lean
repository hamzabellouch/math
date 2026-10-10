import OAI.Computability.UniqueGames.Decoding.ActualAdviceUpperLemmas
import OAI.Computability.UniqueGames.Decoding.VisiblePoliciesLemmas

namespace OAI

/-!
# Actual conditional selected-fiber agreement

The selected event is the full-table event used by the total-variation
comparison. On a positive complete-data fiber it becomes the uniform actual
affine row/column slice. The selector is fixed by the left observation; the
extra complete data and a supporting matrix occur only in this analysis.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedFiberLaw

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse UniqueGamesTheorem.Foundations.Games
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The universe finset is independent of the chosen finite enumeration.
The instances are explicit so elaboration need not unfold either enumeration. -/
private theorem univ_congr {X : Type*} (i j : Fintype X) :
    @Finset.univ X i = @Finset.univ X j := by
  cases Subsingleton.elim i j
  rfl

variable {k s d r : ℕ}

def datumLeft (S : Source) (data : Datum S k s d r) : LeftInput S k s d (Vector r) :=
  AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

def datumMatrix (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :=
  (AdviceLaw.completeDraw data N).hiddenMatrix

def datumProjection (S : Source) (data : Datum S k s d r) :=
  AdviceExperiment.projection (ActualGame.rhs S) (AdviceLaw.completeDraw data 0)

theorem datumLeft_eq (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N) =
      datumLeft S data := by
  unfold datumLeft
  rw [AdviceLaw.completeDraw_left, AdviceLaw.completeDraw_left]

theorem datumMatrix_rows (S : Source) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data) :
    data.1.2.comp (datumMatrix S data N) = data.2.2.2.val :=
  AdviceLaw.completeDraw_rows data N

theorem datumMatrix_rowAdvice (S : Source) (data : Datum S k s d r)
    (N : AdviceLaw.PrivateMap data) :
    RowErasureMatrix.rowAdvice (LinearMap.toMatrix' data.1.2)
        (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      mapEquiv k r (datumLeft S data).rows := by
  rw [← mapEquiv_rowAdvice]
  change mapEquiv k r ((data.1.2.comp (datumMatrix S data N)).comp (datumProjection S data)) =
    mapEquiv k r ((data.1.2.comp (datumMatrix S data 0)).comp (datumProjection S data))
  rw [datumMatrix_rows, datumMatrix_rows]
  rfl

/-- Every event membership uses the same selected normalized witness on the
entire complete-data fiber. -/
theorem slice_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data) :
    slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).toSlice.points := by
  rw [slice_eq_selectedEvent]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  exact SelectedDecoding.selectedEvent_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)

/-- On the selected event, the actual full-table target-hit predicate equals
projected affine equality with the very same normalized coefficient/intercept. -/
theorem target_assemble_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (N : AdviceLaw.PrivateMap data)
    (hN : slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true) :
    targetHit S k s d r labeling α (AdviceLaw.completeAssemble data N) = true ↔
      TableKeysRestoration.projectedAnswer S k s d labeling (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) ((datumMatrix S data N).prod data.2.2.1) =
        datumMatrix S data N (datumProjection S data
          (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).coefficient) +
          (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept := by
  have hp := (slice_assemble_iff S labeling α hα hsmall data hgood N).mp hN
  rw [targetHit_eq_selectedMatch]
  change decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
      (fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S)
        (AdviceLaw.completeDraw data N))) α (LinearMap.toMatrix' data.1.2)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)))) = true ↔ _
  rw [datumLeft_eq, decide_eq_true_eq]
  refine (SelectedDecoding.selectedMatch_iff_normalized S labeling α hα hsmall
    (datumLeft S data) hgood _ (datumMatrix_rowAdvice S data N)).trans ?_
  have hp' : mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data)) ∈
      (RowErasureMatrix.family s (1 + 2 * k) r).points
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood) := hp
  simp only [hp', true_and, LinearEquiv.symm_apply_apply]
  rw [show fullTable S labeling (datumLeft S data)
      (mapEquiv k s ((datumMatrix S data N).comp (datumProjection S data))) =
      TableKeysRestoration.projectedAnswer S k s d labeling (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) ((datumMatrix S data N).prod data.2.2.1) from
    ProjectedColumnSlice.fullTable_padded S labeling (AdviceLaw.completeDraw data 0) (datumMatrix S data N)]
  rfl

/-- Positive mass supplies a supporting private coordinate in the selected
fiber; neither a hidden matrix nor good advice is an additional premise. -/
theorem exists_selected_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (data : Datum S k s d r)
    (positive : 0 < (law S k s d r β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))) :
    ∃ N : AdviceLaw.PrivateMap data,
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true := by
  have hex : ∃ x : Seed S k s d r,
      VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α) x = true := by
    by_contra hn
    have he : VisibleTransfer.fiberEvent AdviceLaw.completeObserve data
        (slice S k s d r labeling α) = fun _ => false := by
      funext x
      apply Bool.eq_false_iff.mpr
      intro hx
      exact hn ⟨x, hx⟩
    rw [he, FiniteDistribution.probability_false] at positive
    exact (lt_irrefl 0) positive
  obtain ⟨x, hx⟩ := hex
  have hx' : AdviceLaw.completeObserve x = data ∧ slice S k s d r labeling α x = true := by
    simpa only [VisibleTransfer.fiberEvent, Bool.and_eq_true, decide_eq_true_eq] using hx
  let N := (AdviceLaw.completeFiberEquiv data).symm ⟨x, hx'.1⟩
  have he : AdviceLaw.completeAssemble data N = x :=
    congrArg Subtype.val ((AdviceLaw.completeFiberEquiv data).apply_symm_apply ⟨x, hx'.1⟩)
  exact ⟨N, he.symm ▸ hx'.2⟩

theorem good_of_selected_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (data : Datum S k s d r) (N : AdviceLaw.PrivateMap data)
    (hN : slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true) :
    GoodAdvice S labeling α (datumLeft S data) := by
  have hg := slice_good S k s d r labeling α (AdviceLaw.completeAssemble data N) hN
  change GoodAdvice S labeling α
    (AdviceExperiment.leftObservation (ActualGame.rhs S) (AdviceLaw.completeDraw data N)) at hg
  rw [datumLeft_eq] at hg
  exact hg

/-- The actual selected private coordinates are in bijection with the complete
projected affine slice. The supporting point is used only to state its column
equations; the canonical visible base still defines the private coordinates. -/
def selectedPrivateEquiv (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true) :
    {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} ≃
      RowErasureSliceQuotient.AffineSlice data.1.2
        ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
          (datumProjection S data)) (datumMatrix S data Nstar) := by
  let D := normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood
  let e := AdviceFibers.rowFiberEquiv data.1.2 data.2.2.2.val
    (AdviceFibers.observedBase data.1.2 data.2.2.2)
    (AdviceFibers.observedBase_property data.1.2 data.2.2.2)
  have hs : mapEquiv k s ((datumMatrix S data Nstar).comp (datumProjection S data)) ∈ D.toSlice.points :=
    (slice_assemble_iff S labeling α hα hsmall data hgood Nstar).mp hstar
  have hrow (N : AdviceLaw.PrivateMap data) :
      data.1.2.comp (datumMatrix S data N) = data.1.2.comp (datumMatrix S data Nstar) := by
    rw [datumMatrix_rows, datumMatrix_rows]
  let lift := fun M : RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar) =>
    e.symm ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩
  have hlift (M) : datumMatrix S data (lift M) = M.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨M.val, M.property.1.trans (datumMatrix_rows S data Nstar)⟩)
  refine {
    toFun := fun N => ⟨datumMatrix S data N.val, hrow N.val, ?_⟩
    invFun := fun M => ⟨lift M, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs
      (datumMatrix S data N.val) (hrow N.val)).mp
        ((slice_assemble_iff S labeling α hα hsmall data hgood N.val).mp N.property)
  · apply (slice_assemble_iff S labeling α hα hsmall data hgood (lift M)).mpr
    rw [hlift]
    exact (ProjectedColumnSlice.contains_padded_iff D data.1.2
      (normalizedDescription_spec S labeling α hα hsmall (datumLeft S data) hgood).1
      (datumProjection S data) (datumMatrix S data Nstar) hs M.val M.property.1).mpr M.property.2
  · intro N
    apply Subtype.ext
    exact e.symm_apply_apply N.val
  · intro M
    apply Subtype.ext
    exact hlift M

@[simp] theorem selectedPrivateEquiv_val (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (N : {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true}) :
    (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar N).val =
      datumMatrix S data N.val := rfl
/-- Exact conditional target probability, with no assumed uniformity premise. -/
theorem conditional_eq_transferred (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (data : Datum S k s d r) (hgood : GoodAdvice S labeling α (datumLeft S data))
    (Nstar : AdviceLaw.PrivateMap data)
    (hstar : slice S k s d r labeling α (AdviceLaw.completeAssemble data Nstar) = true)
    (positive : 0 < (law S k s d r β hβ hβ').probability
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))) :
    ((law S k s d r β hβ hβ').condition
      (VisibleTransfer.fiberEvent AdviceLaw.completeObserve data (slice S k s d r labeling α))
        positive).probability (targetHit S k s d r labeling α) =
      SelectedDecoding.transferredAgreement S labeling (AdviceLaw.completeDraw data 0)
        (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood)
        (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept
        (datumMatrix S data Nstar) := by
  have enumeration : ActualAdviceUpper.publicMapFintype s r =
      (ActualConditionalLaw.homFintype : Fintype (Alphabet s →ₗ[F2] Vector r)) :=
    Subsingleton.elim _ _
  unfold law at positive ⊢
  revert positive
  rw [enumeration]
  intro positive
  refine (ActualConditionalLaw.probability_condition_complete
    (k := k) (Id := Fin S.occurrences) (K := Alphabet s) (W := Vector d) (R := Vector r)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (@FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)
      ActualConditionalLaw.homFintype inferInstance) β hβ hβ' data
    (slice S k s d r labeling α) (targetHit S k s d r labeling α) positive).trans ?_
  let : Fintype (RawPartnerTarget.RawPoint (PaddedLaw.choiceMask data.2.1) →ₗ[F2] Alphabet s) :=
    homFintype
  let : Fintype (RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar)) :=
    SelectedDecoding.affineSliceFintype _ _ _
  let f : {N : AdviceLaw.PrivateMap data //
      slice S k s d r labeling α (AdviceLaw.completeAssemble data N) = true} → ℝ :=
    fun N => if targetHit S k s d r labeling α (AdviceLaw.completeAssemble data N.val) = true
      then 1 else 0
  let g : RowErasureSliceQuotient.AffineSlice data.1.2
      ((normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).columns.map
        (datumProjection S data)) (datumMatrix S data Nstar) → ℝ :=
    fun M => if TableKeysRestoration.projectedAnswer S k s d labeling
        (PaddedLaw.choiceMask data.2.1)
        (RawPrivateTable.supported (PaddedLaw.choiceMask data.2.1) (ActualGame.names S)
          data.1.1 (PaddedLaw.choiceSlots data.2.1)) (M.val.prod data.2.2.1) =
        M.val (datumProjection S data
          (normalizedResponse S labeling α hα hsmall (datumLeft S data) hgood).coefficient) +
          (normalizedDescription S labeling α hα hsmall (datumLeft S data) hgood).intercept
      then 1 else 0
  have he : (𝔼 N, f N) = 𝔼 M, g M := by
    refine Fintype.expect_equiv
      (selectedPrivateEquiv S labeling α hα hsmall data hgood Nstar hstar) f g ?_
    intro N
    dsimp only [f, g]
    simp only [selectedPrivateEquiv_val]
    exact TransferredDecoding.indicator_congr _ _ _ _
      (target_assemble_iff S labeling α hα hsmall data hgood N.val N.property)
  calc
    _ = 𝔼 N, f N := by
      apply Finset.expect_congr (by ext N; simp only [Finset.mem_univ])
      intro N _
      exact TransferredDecoding.indicator_congr _ _ _ _ Iff.rfl
    _ = 𝔼 M, g M := he
    _ = _ := by
      unfold SelectedDecoding.transferredAgreement
      apply Finset.expect_congr (univ_congr _ _)
      intro M _
      exact TransferredDecoding.indicator_congr _ _ _ _ Iff.rfl

/-- Every complete visible datum selected by the actual witness event pays the
private-decoding success constant. Good advice and a nonempty transferred
slice follow from positivity and are not additional hypotheses. -/
theorem visibleWitness_decoding (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (data : Datum S k s d r)
    (hvisible : VisibleTransfer.visibleWitness (law S k s d r β hβ hβ')
      AdviceLaw.completeObserve (slice S k s d r labeling α)
      (targetHit S k s d r labeling α) (α / 4) data = true) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (s * r) / (2 : ℝ) ^ r ≤
      ActualConditionalLaw.datumAgreement S labeling (goodPredicate S labeling α hα hsmall) data := by
  obtain ⟨positive, hagree⟩ := VisibleTransfer.visibleWitness_conditional
    (law S k s d r β hβ hβ') AdviceLaw.completeObserve
    (slice S k s d r labeling α) (targetHit S k s d r labeling α) (α / 4) data hvisible
  obtain ⟨Nstar, hstar⟩ := exists_selected_private S labeling α β hβ hβ' data positive
  have hgood := good_of_selected_private S labeling α data Nstar hstar
  rw [conditional_eq_transferred S labeling α hα hsmall β hβ hβ' data hgood Nstar hstar positive] at hagree
  apply SelectedDecoding.observedAgreement_lower S labeling α hα hsmall
    (AdviceLaw.completeDraw data 0) hgood (datumMatrix S data Nstar) ?_ hagree
  exact (datumMatrix_rows S data Nstar).trans (datumMatrix_rows S data 0).symm

end UniqueGamesTheorem.Decoder.SelectedFiberLaw

end

end OAI
