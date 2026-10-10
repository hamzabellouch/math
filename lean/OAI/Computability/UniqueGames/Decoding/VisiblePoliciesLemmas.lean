import OAI.Computability.UniqueGames.Decoding.MatrixCoordinates
import OAI.Computability.UniqueGames.Decoding.TableKeysLemmas
import OAI.Computability.UniqueGames.Inverse.AffineWitnessLemmas
import OAI.Computability.UniqueGames.Inverse.RowErasureMatrixLemmas
import OAI.Computability.UniqueGames.Inverse.ShortcodeInterfaceLemmas

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Decoder.VisiblePolicies

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Foundations.Games
open ActualSource PrivateStrategy
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The part of a normalized affine witness needed by the left sampler. -/
structure ResponseWitness (k : ℕ) where
  columns : Submodule F2 (ActualHomogeneous.E k)
  coefficient : ActualHomogeneous.E k
  firstBit : ActualHomogeneous.tau coefficient = 1

def defaultWitness (k : ℕ) : ResponseWitness k :=
  ⟨⊥, ActualHomogeneous.hBasis k, ActualHomogeneous.tau_hBasis⟩

variable {k s d : ℕ} {R : Type} [AddCommGroup R] [Module F2 R]

abbrev LeftInput (S : Source) (k s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.FullAdvice k (Fin S.occurrences) (Alphabet s) (Vector d) R

abbrev RightInput (S : Source) (J : Finset (Fin k)) (s d : ℕ) (R : Type)
    [AddCommGroup R] [Module F2 R] :=
  AdviceExperiment.ProjectedAdvice (K := Alphabet s) (W := Vector d) (R := R)
    (ActualGame.names S) J

/-- The witness choice has only the left observation as its variable input. -/
def chosenWitness {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) : ResponseWitness k :=
  if h : ∃ w, good q w then Classical.choose h else defaultWitness k

theorem chosenWitness_spec {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) (h : ∃ w, good q w) :
    good q (chosenWitness good q) := by
  rw [chosenWitness, dite_eq_left h]
  exact Classical.choose_spec h

def leftPolicy {S : Source}
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (q : LeftInput S k s d R) :
    FiniteDistribution (ActualAnswer (ActualHomogeneous.tau (dimension := k))) :=
  let w := chosenWitness good q
  candidateLaw w.columns w.coefficient ActualHomogeneous.tau w.firstBit

/-- A fixed valid fallback gives a total policy even on impossible row inputs. -/
def pointLaw {X : Type*} [Fintype X] (x : X) : FiniteDistribution X where
  weight y := if y = x then 1 else 0
  nonnegative y := by split <;> norm_num
  normalized := by simp

/-- The right kernel consumes its own complete visible observation only. -/
def rightPolicy (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R) :
    FiniteDistribution (ActualAnswer (TableKeys.visibleTau J)) :=
  if h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows then
    privateLaw
      (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
      q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J)
  else pointLaw (TransferredDecoding.visibleFallback J)

theorem rightPolicy_on_attainable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (J : Finset (Fin k)) (q : RightInput S J s d R)
    (h : ∃ M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s,
      q.rowMap.comp M = q.rows) :
    rightPolicy S labeling J q =
      privateLaw
        (TableKeysPrivateRow.rowAnswer S labeling J q.question q.rowMap ⟨q.rows, h⟩ q.complement)
        q.rowMap.ker.subtype (TableKeys.visibleTau J) (TransferredDecoding.visibleFallback J) := by
  rw [rightPolicy, dite_eq_left h]

theorem leftPolicy_changeHidden (S : Source)
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R)
    (N : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] draw.rowMap.ker) :
    leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S)
      (AdviceExperiment.changeHidden draw N)) =
      leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) := by
  rw [AdviceExperiment.leftObservation_changeHidden]

theorem rightPolicy_on_draw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) :
    rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2 =
      privateLaw
        (TableKeysPrivateRow.rowAnswer S labeling draw.singletons
          (RawPrivateTable.supported draw.singletons (ActualGame.names S)
            draw.occurrences draw.positions)
          draw.rowMap (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement)
        draw.rowMap.ker.subtype (TableKeys.visibleTau draw.singletons)
        (TransferredDecoding.visibleFallback draw.singletons) := by
  rw [rightPolicy_on_attainable S labeling draw.singletons
    (AdviceExperiment.rightObservation (ActualGame.names S) draw).2
    (AdviceExperiment.right_rows_attainable (ActualGame.names S) draw)]
  rfl

/-- The literal product of the two observation-local stochastic responses. -/
def observedAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) : ℝ :=
  ((leftPolicy good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)).product
    (rightPolicy S labeling draw.singletons
      (AdviceExperiment.rightObservation (ActualGame.names S) draw).2)).probability
    (fun answers => decide
      (AdviceExperiment.projection (ActualGame.rhs S) draw answers.1.1 = answers.2.1))

/-- The private-decoding expression is exactly the actual local-kernel product
probability.  In particular there is no shared decoder random tape. -/
theorem observedAgreement_eq_private (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : LeftInput S k s d R → ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) R) :
    observedAgreement S labeling good draw =
      let w := chosenWitness good (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)
      PrivateStrategy.conditionalAgreement w.columns w.coefficient
        ActualHomogeneous.tau w.firstBit (AdviceExperiment.projection (ActualGame.rhs S) draw)
        (TableKeysPrivateRow.rowAnswer S labeling draw.singletons
          (RawPrivateTable.supported draw.singletons (ActualGame.names S)
            draw.occurrences draw.positions)
          draw.rowMap (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement)
        draw.rowMap.ker.subtype (TableKeys.visibleTau draw.singletons)
        (TransferredDecoding.visibleFallback draw.singletons) := by
  rw [observedAgreement, rightPolicy_on_draw S labeling draw]
  dsimp only [PrivateStrategy.conditionalAgreement, leftPolicy]
  congr 1
  funext answers
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

end UniqueGamesTheorem.Decoder.VisiblePolicies

end

end

section

/-!
# The actual visible selector used by the stochastic decoder

At fixed labeling, the matrix table depends only on the occurrence question and
complement map. Its normalized row/column witness is selected from the observed
row map and row value. Transporting this witness through the actual homogeneous
coordinates supplies `VisiblePolicies.ResponseWitness`; the selected target's
affine intercept is retained separately, including exact equality on the slice.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedPolicies

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

/-- The table at a fixed actual occurrence question and complement map. -/
def matrixTable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (occ : ActualGame.Question S k)
    (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (M : Shortcode.Mat s (1 + 2 * k)) : Alphabet s :=
  TableKeysGame.unfolded S k s d labeling
    (occ, ((mapEquiv k s).symm M).prod T)

/-- No hidden matrix is an input to this fixed table function. -/
def fullTable (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (q : LeftInput S k s d (Vector r)) : Shortcode.Mat s (1 + 2 * k) → Alphabet s :=
  matrixTable S labeling q.occurrences q.complement

theorem matrixTable_fold (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (occ : ActualGame.Question S k)
    (T : ActualHomogeneous.E k →ₗ[F2] Vector d)
    (h : Alphabet s) (M : Shortcode.Mat s (1 + 2 * k)) :
    matrixTable S labeling occ T
        (M + Shortcode.rankOne h (Shortcode.functionalRow (coordinateTau k))) =
      matrixTable S labeling occ T M + h := by
  unfold matrixTable
  rw [mapEquiv_symm_firstBit_shift]
  have hprod : (((mapEquiv k s).symm M + ActualHomogeneous.tau.smulRight h).prod T) =
      ((mapEquiv k s).symm M).prod T +
        ActualHomogeneous.tau.smulRight (h, (0 : Vector d)) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · rfl
    · simp
  rw [hprod]
  exact TableKeysGame.unfolded_equivariant S k s d labeling
    (occ, ((mapEquiv k s).symm M).prod T) h

def GoodAdvice (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (q : LeftInput S k s d (Vector r)) : Prop :=
  (RowErasureMatrix.family s (1 + 2 * k) r).GoodAdvice (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows)

/-- The actual normalized description, chosen using only the left observation. -/
def normalizedDescription (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    RowErasureDescriptions.Description s (1 + 2 * k) r :=
  RowErasureMatrix.normalizedChosenDescription (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood (coordinateTau k)
    (matrixTable_fold S labeling q.occurrences q.complement) hα hsmall

theorem normalizedDescription_spec (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    let F := RowErasureMatrix.family s (1 + 2 * k) r
    let D := normalizedDescription S labeling α hα hsmall q hgood
    let D₀ := F.chosenDescription (fullTable S labeling q) α
      (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood
    F.rowMap D = LinearMap.toMatrix' q.rowMap ∧
      F.rowValue D = mapEquiv k r q.rows ∧
      (F.points D).Nonempty ∧
      α / 2 ≤ F.agreement (fullTable S labeling q) D ∧
      coordinateTau k D.coefficient = 1 ∧
      D.toSlice = D₀.toSlice ∧
      F.agreement (fullTable S labeling q) D = F.agreement (fullTable S labeling q) D₀ ∧
      ∀ M, M ∈ F.points D₀ → F.target D M = F.target D₀ M :=
  RowErasureMatrix.normalizedChosenDescription_spec (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood (coordinateTau k)
    (matrixTable_fold S labeling q.occurrences q.complement) hα hsmall

/-- The response coefficient and columns in the actual homogeneous space. -/
def normalizedResponse (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    ResponseWitness k where
  columns := (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan.map
    (domainCoordinates k).symm.toLinearMap
  coefficient := (domainCoordinates k).symm
    (normalizedDescription S labeling α hα hsmall q hgood).coefficient
  firstBit := (normalizedDescription_spec S labeling α hα hsmall q hgood).2.2.2.2.1

theorem normalizedResponse_dimension (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    Module.finrank F2 (normalizedResponse S labeling α hα hsmall q hgood).columns ≤ r := by
  exact (Submodule.finrank_map_le (domainCoordinates k).symm.toLinearMap
    (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan).trans
    (normalizedDescription S labeling α hα hsmall q hgood).toSlice.columnSpan_finrank_le

/-- The generic selector predicate is now the graph of the actual normalized
row-advice selector, rather than an unspecified class of candidate witnesses. -/
def goodPredicate (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (w : ResponseWitness k) : Prop :=
  ∃ hgood : GoodAdvice S labeling α q,
    w = normalizedResponse S labeling α hα hsmall q hgood

theorem chosenWitness_eq_normalizedResponse (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    chosenWitness (goodPredicate S labeling α hα hsmall) q =
      normalizedResponse S labeling α hα hsmall q hgood := by
  obtain ⟨hgood', hw⟩ := chosenWitness_spec (goodPredicate S labeling α hα hsmall) q
    ⟨normalizedResponse S labeling α hα hsmall q hgood, hgood, rfl⟩
  exact hw

/-- The actual left kernel is uniform on the selected normalized affine coset
intersected with the first-bit-one answer space. -/
theorem leftPolicy_eq_candidateLaw (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q) :
    leftPolicy (goodPredicate S labeling α hα hsmall) q =
      let w := normalizedResponse S labeling α hα hsmall q hgood
      PrivateStrategy.candidateLaw w.columns w.coefficient ActualHomogeneous.tau w.firstBit := by
  unfold leftPolicy
  rw [chosenWitness_eq_normalizedResponse S labeling α hα hsmall q hgood]

/-- Every point of the selected matrix slice has exactly the observed row value
when transported to the actual homogeneous domain. -/
theorem normalized_point_row (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k))
    (hM : M ∈ (RowErasureMatrix.family s (1 + 2 * k) r).points
      (normalizedDescription S labeling α hα hsmall q hgood)) :
    q.rowMap.comp ((mapEquiv k s).symm M) = q.rows := by
  have hs := normalizedDescription_spec S labeling α hα hsmall q hgood
  have hm := (RowErasureMatrix.family s (1 + 2 * k) r).points_row
    (normalizedDescription S labeling α hα hsmall q hgood) M hM
  rw [hs.1, hs.2.1] at hm
  apply (mapEquiv k r).injective
  rw [mapEquiv_rowAdvice, LinearEquiv.apply_symm_apply]
  exact hm

/-- Coordinate transport keeps the actual affine target, including its selected
intercept; first-bit normalization never replaces it by a homogeneous target. -/
theorem normalized_target (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k)) :
    (RowErasureMatrix.family s (1 + 2 * k) r).target
        (normalizedDescription S labeling α hα hsmall q hgood) M =
      (mapEquiv k s).symm M (normalizedResponse S labeling α hα hsmall q hgood).coefficient +
        (normalizedDescription S labeling α hα hsmall q hgood).intercept :=
  affine_evaluation k s M _ _

end UniqueGamesTheorem.Decoder.SelectedPolicies

end

end

section

/-!
# Conditional success of the actual selected policies

This endpoint uses the normalized witness chosen from the left observation and
the private Fourier kernel chosen from the right observation. The hypothesis is
literal uniform agreement on a transferred affine column slice. Deriving that
hypothesis from the actual visible conditional law is the separate transfer
step; it is not assumed as an inverse theorem or as extra prover information.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.SelectedDecoding

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The affine slice is a subtype of a finite linear-map space. -/
instance affineSliceFintype {E K L : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    [AddCommGroup L] [Module F2 L] [Fintype (E →ₗ[F2] K)]
    (A : K →ₗ[F2] L) (Q : Submodule F2 E) (Mstar : E →ₗ[F2] K) :
    Fintype (RowErasureSliceQuotient.AffineSlice A Q Mstar) := by
  unfold RowErasureSliceQuotient.AffineSlice
  infer_instance

variable {k s d r : ℕ}

/-- Normalizing the target preserves the actual selected event, point by point. -/
theorem selectedEvent_iff_normalized (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k))
    (hrow : RowErasureMatrix.rowAdvice (LinearMap.toMatrix' q.rowMap) M =
      mapEquiv k r q.rows) :
    (RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
        (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap) M ↔
      M ∈ (RowErasureMatrix.family s (1 + 2 * k) r).points
        (normalizedDescription S labeling α hα hsmall q hgood) := by
  have he := (RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent_iff_of_advice
    (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap)
    (mapEquiv k r q.rows) hgood M hrow
  obtain ⟨_, _, _, _, _, hslice, _, _⟩ :=
    normalizedDescription_spec S labeling α hα hsmall q hgood
  rw [show (RowErasureMatrix.family s (1 + 2 * k) r).points
      (normalizedDescription S labeling α hα hsmall q hgood) =
      (RowErasureMatrix.family s (1 + 2 * k) r).points
        ((RowErasureMatrix.family s (1 + 2 * k) r).chosenDescription
          (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap)
          (mapEquiv k r q.rows) hgood) from congrArg Shortcode.Slice.points hslice]
  exact he

/-- The selected target-hit event uses exactly the transported coefficient and
its adjusted intercept. This identifies the event used by the mass estimates. -/
theorem selectedMatch_iff_normalized (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (hgood : GoodAdvice S labeling α q)
    (M : Shortcode.Mat s (1 + 2 * k))
    (hrow : RowErasureMatrix.rowAdvice (LinearMap.toMatrix' q.rowMap) M =
      mapEquiv k r q.rows) :
    (RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
        (fullTable S labeling q) α (LinearMap.toMatrix' q.rowMap) M ↔
      M ∈ (RowErasureMatrix.family s (1 + 2 * k) r).points
          (normalizedDescription S labeling α hα hsmall q hgood) ∧
        fullTable S labeling q M =
          (mapEquiv k s).symm M
              (normalizedResponse S labeling α hα hsmall q hgood).coefficient +
            (normalizedDescription S labeling α hα hsmall q hgood).intercept := by
  let F := RowErasureMatrix.family s (1 + 2 * k) r
  let D := normalizedDescription S labeling α hα hsmall q hgood
  let D₀ := F.chosenDescription (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood
  have he := F.selectedMatch_iff_of_advice (fullTable S labeling q) α
    (LinearMap.toMatrix' q.rowMap) (mapEquiv k r q.rows) hgood M hrow
  obtain ⟨_, _, _, _, _, hslice, _, htarget⟩ :=
    normalizedDescription_spec S labeling α hα hsmall q hgood
  have hp : F.points D = F.points D₀ := congrArg Shortcode.Slice.points hslice
  rw [← normalized_target S labeling α hα hsmall q hgood M]
  constructor
  · intro h
    obtain ⟨hm, hf⟩ := he.mp h
    refine ⟨hp.symm ▸ hm, ?_⟩
    rw [htarget M hm]
    exact hf
  · rintro ⟨hm, hf⟩
    have hm₀ : M ∈ F.points D₀ := hp ▸ hm
    apply he.mpr
    refine ⟨hm₀, ?_⟩
    rw [← htarget M hm₀]
    exact hf

/-- Rank-nullity supplies the small trivial-character probability for every
row map, including those with dependent rows. -/
theorem rowKernel_reciprocal_le (A : Alphabet s →ₗ[F2] Vector r) :
    1 / (Fintype.card A.ker : ℝ) ≤ 1 / (2 : ℝ) ^ (s - r) := by
  have hk : 2 ^ (s - r) ≤ Fintype.card A.ker := by
    simpa only [Nat.card_eq_fintype_card] using binary_kernel_card_lower A
  have hk' : (2 : ℝ) ^ (s - r) ≤ (Fintype.card A.ker : ℝ) := by
    exact_mod_cast hk
  exact one_div_le_one_div_of_le (by positivity) hk'

/-- Literal uniform target agreement on the projected affine slice. The slice
origin is an analysis witness, independent of the canonical visible row base. -/
def transferredAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (w : ResponseWitness k) (u : Alphabet s)
    (Mstar : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s) : ℝ :=
  𝔼 M : RowErasureSliceQuotient.AffineSlice draw.rowMap
      (w.columns.map (AdviceExperiment.projection (ActualGame.rhs S) draw)) Mstar,
    if TableKeysRestoration.projectedAnswer S k s d labeling draw.singletons
        (RawPrivateTable.supported draw.singletons (ActualGame.names S)
          draw.occurrences draw.positions) (M.val.prod draw.complement) =
      M.val (AdviceExperiment.projection (ActualGame.rhs S) draw w.coefficient) + u
    then (1 : ℝ) else 0

/-- The actual independently sampled local policies obey the decoding lower
bound at every datum with a transferred good slice for its selected witness. -/
theorem observedAgreement_lower (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (hgood : GoodAdvice S labeling α (AdviceExperiment.leftObservation (ActualGame.rhs S) draw))
    (Mstar : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s)
    (hstar : draw.rowMap.comp Mstar = draw.rowMap.comp draw.hiddenMatrix)
    (hagreement : α / 4 ≤ transferredAgreement S labeling draw
      (normalizedResponse S labeling α hα hsmall
        (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood)
      (normalizedDescription S labeling α hα hsmall
        (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood).intercept Mstar) :
    (α / 8) ^ 2 / (2 : ℝ) ^ (s * r) / (2 : ℝ) ^ r ≤
      observedAgreement S labeling (goodPredicate S labeling α hα hsmall) draw := by
  let q := AdviceExperiment.leftObservation (ActualGame.rhs S) draw
  let w := normalizedResponse S labeling α hα hsmall q hgood
  let u := (normalizedDescription S labeling α hα hsmall q hgood).intercept
  have hH : Module.finrank F2 draw.rowMap.ker ≤ s := by
    simpa only [Module.finrank_fin_fun] using draw.rowMap.ker.finrank_le
  have hs : 1 / (Fintype.card draw.rowMap.ker : ℝ) ≤ α / 8 :=
    (rowKernel_reciprocal_le draw.rowMap).trans hsmall.le
  have h := TransferredDecoding.actual_transferred_decoding S labeling draw.singletons
    draw.occurrences draw.positions draw.rowMap
    (AdviceFibers.observe draw.rowMap draw.hiddenMatrix) draw.complement Mstar hstar
    w.columns w.coefficient w.firstBit u α hα.le s r hH
    (normalizedResponse_dimension S labeling α hα hsmall q hgood) hs hagreement
  rw [observedAgreement_eq_private,
    chosenWitness_eq_normalizedResponse S labeling α hα hsmall _ hgood]
  exact h

end UniqueGamesTheorem.Decoder.SelectedDecoding

end

end

section

/-!
# The selected padded slice is the actual projected affine slice

After fixing row advice, the selected full-domain column equations on `Mπ` are
exactly the equations fixing `M` on the image of the selected column span under
`π`. The equivalence keeps the same maps, so both uniform sampling and affine
target equality transport without changing the chosen intercept.
-/

noncomputable section

namespace UniqueGamesTheorem.Decoder.ProjectedColumnSlice

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction UniqueGamesTheorem.Soundness
open UniqueGamesTheorem.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

section Algebra

variable {V : Type*} [AddCommGroup V] [Module F2 V]

/-- Two successive images of a column subspace express the same pointwise
agreement as composition with the coordinate change and projection. -/
theorem column_agreement_iff (Q : Submodule F2 (Vector (1 + 2 * k)))
    (π : ActualHomogeneous.E k →ₗ[F2] V) (M Mstar : V →ₗ[F2] Alphabet s) :
    (∀ x ∈ Q, M (π ((domainCoordinates k).symm x)) =
      Mstar (π ((domainCoordinates k).symm x))) ↔
      ∀ v ∈ (Q.map (domainCoordinates k).symm.toLinearMap).map π, M v = Mstar v := by
  constructor
  · intro h v hv
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
    exact h x hx
  · intro h x hx
    apply h
    exact Submodule.mem_map.mpr ⟨(domainCoordinates k).symm x,
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩

/-- A simultaneous matrix slice pulls back to the projected column equations
once the actual row equation is fixed. -/
theorem contains_padded_iff
    (D : RowErasureDescriptions.Description s (1 + 2 * k) r)
    (A : Alphabet s →ₗ[F2] Vector r)
    (hDrow : (RowErasureMatrix.family s (1 + 2 * k) r).rowMap D = LinearMap.toMatrix' A)
    (π : ActualHomogeneous.E k →ₗ[F2] V) (Mstar : V →ₗ[F2] Alphabet s)
    (hstar : mapEquiv k s (Mstar.comp π) ∈ D.toSlice.points)
    (M : V →ₗ[F2] Alphabet s) (hrow : A.comp M = A.comp Mstar) :
    mapEquiv k s (M.comp π) ∈ D.toSlice.points ↔
      ∀ v ∈ (D.toSlice.columnSpan.map (domainCoordinates k).symm.toLinearMap).map π,
        M v = Mstar v := by
  have hr : D.toSlice.rowMap = A := by
    change Matrix.toLin' D.1 = A
    change D.1 = LinearMap.toMatrix' A at hDrow
    rw [hDrow, Matrix.toLin'_toMatrix']
  have hc (N : V →ₗ[F2] Alphabet s) :
      Matrix.toLin' (mapEquiv k s (N.comp π)) =
        (N.comp π).comp (domainCoordinates k).symm.toLinearMap := by
    rw [mapEquiv_apply, Matrix.toLin'_toMatrix']
  have hs : D.toSlice.Contains (mapEquiv k s (Mstar.comp π)) :=
    (Finset.mem_filter.mp hstar).2
  have he := D.toSlice.contains_iff_inSlice (mapEquiv k s (Mstar.comp π)) hs
    (mapEquiv k s (M.comp π))
  rw [AffineWitness.InSlice, hr, hc, hc] at he
  have hrows : A.comp ((M.comp π).comp (domainCoordinates k).symm.toLinearMap) =
      A.comp ((Mstar.comp π).comp (domainCoordinates k).symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hrow (π ((domainCoordinates k).symm x))
  constructor
  · intro h
    have hh := he.mp (Finset.mem_filter.mp h).2
    exact (column_agreement_iff D.toSlice.columnSpan π M Mstar).mp hh.2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, he.mpr ⟨hrows,
      (column_agreement_iff D.toSlice.columnSpan π M Mstar).mpr h⟩⟩

/-- The subtype equivalence leaves the actual matrix untouched. -/
def paddedSliceEquiv
    (D : RowErasureDescriptions.Description s (1 + 2 * k) r)
    (A : Alphabet s →ₗ[F2] Vector r)
    (hDrow : (RowErasureMatrix.family s (1 + 2 * k) r).rowMap D = LinearMap.toMatrix' A)
    (π : ActualHomogeneous.E k →ₗ[F2] V) (Mstar : V →ₗ[F2] Alphabet s)
    (hstar : mapEquiv k s (Mstar.comp π) ∈ D.toSlice.points) :
    {M : V →ₗ[F2] Alphabet s // A.comp M = A.comp Mstar ∧
      mapEquiv k s (M.comp π) ∈ D.toSlice.points} ≃
      RowErasureSliceQuotient.AffineSlice A
        ((D.toSlice.columnSpan.map (domainCoordinates k).symm.toLinearMap).map π) Mstar where
  toFun M := ⟨M.val, M.property.1,
    (contains_padded_iff D A hDrow π Mstar hstar M.val M.property.1).mp M.property.2⟩
  invFun M := ⟨M.val, M.property.1,
    (contains_padded_iff D A hDrow π Mstar hstar M.val M.property.1).mpr M.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform expectations agree exactly, because the subtype equivalence
preserves the underlying matrix. -/
theorem paddedSlice_expect
    (D : RowErasureDescriptions.Description s (1 + 2 * k) r)
    (A : Alphabet s →ₗ[F2] Vector r)
    (hDrow : (RowErasureMatrix.family s (1 + 2 * k) r).rowMap D = LinearMap.toMatrix' A)
    (π : ActualHomogeneous.E k →ₗ[F2] V) (Mstar : V →ₗ[F2] Alphabet s)
    (hstar : mapEquiv k s (Mstar.comp π) ∈ D.toSlice.points)
    [Fintype {M : V →ₗ[F2] Alphabet s // A.comp M = A.comp Mstar ∧
      mapEquiv k s (M.comp π) ∈ D.toSlice.points}]
    [Fintype (RowErasureSliceQuotient.AffineSlice A
      ((D.toSlice.columnSpan.map (domainCoordinates k).symm.toLinearMap).map π) Mstar)]
    (f : (V →ₗ[F2] Alphabet s) → ℝ) :
    (𝔼 M : {M : V →ₗ[F2] Alphabet s // A.comp M = A.comp Mstar ∧
      mapEquiv k s (M.comp π) ∈ D.toSlice.points}, f M.val) =
      𝔼 M : RowErasureSliceQuotient.AffineSlice A
        ((D.toSlice.columnSpan.map (domainCoordinates k).symm.toLinearMap).map π) Mstar,
        f M.val := by
  exact Fintype.expect_equiv (paddedSliceEquiv D A hDrow π Mstar hstar) _ _ (fun _ => rfl)

end Algebra

/-- Exact key sharing identifies the selected full table with the projected
answer table at every possible hidden matrix in this visible fiber. -/
theorem fullTable_padded (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (M : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s) :
    fullTable S labeling (AdviceExperiment.leftObservation (ActualGame.rhs S) draw)
        (mapEquiv k s (M.comp (AdviceExperiment.projection (ActualGame.rhs S) draw))) =
      TableKeysRestoration.projectedAnswer S k s d labeling draw.singletons
        (RawPrivateTable.supported draw.singletons (ActualGame.names S)
          draw.occurrences draw.positions) (M.prod draw.complement) := by
  unfold fullTable matrixTable
  rw [LinearEquiv.symm_apply_apply, TableKeysRestoration.projectedAnswer_pullback]
  rfl

/-- The concrete normalized witness induces exactly the projected column span
used by the private Fourier conditional bound. -/
theorem normalized_contains_iff (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (hgood : GoodAdvice S labeling α (AdviceExperiment.leftObservation (ActualGame.rhs S) draw))
    (Mstar : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s)
    (hstar : mapEquiv k s (Mstar.comp (AdviceExperiment.projection (ActualGame.rhs S) draw)) ∈
      (normalizedDescription S labeling α hα hsmall
        (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood).toSlice.points)
    (M : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s)
    (hrow : draw.rowMap.comp M = draw.rowMap.comp Mstar) :
    mapEquiv k s (M.comp (AdviceExperiment.projection (ActualGame.rhs S) draw)) ∈
        (normalizedDescription S labeling α hα hsmall
          (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood).toSlice.points ↔
      ∀ v ∈ (normalizedResponse S labeling α hα hsmall
          (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood).columns.map
            (AdviceExperiment.projection (ActualGame.rhs S) draw), M v = Mstar v := by
  exact contains_padded_iff _ draw.rowMap
    (normalizedDescription_spec S labeling α hα hsmall _ hgood).1
    (AdviceExperiment.projection (ActualGame.rhs S) draw) Mstar hstar M hrow

/-- The actual selected target retains its intercept after projection. -/
theorem normalized_target_padded (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (hgood : GoodAdvice S labeling α (AdviceExperiment.leftObservation (ActualGame.rhs S) draw))
    (M : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s) :
    (RowErasureMatrix.family s (1 + 2 * k) r).target
        (normalizedDescription S labeling α hα hsmall
          (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood)
        (mapEquiv k s (M.comp (AdviceExperiment.projection (ActualGame.rhs S) draw))) =
      M (AdviceExperiment.projection (ActualGame.rhs S) draw
          (normalizedResponse S labeling α hα hsmall
            (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood).coefficient) +
        (normalizedDescription S labeling α hα hsmall
          (AdviceExperiment.leftObservation (ActualGame.rhs S) draw) hgood).intercept := by
  rw [normalized_target, LinearEquiv.symm_apply_apply]
  rfl

end UniqueGamesTheorem.Decoder.ProjectedColumnSlice

end

end

end OAI
