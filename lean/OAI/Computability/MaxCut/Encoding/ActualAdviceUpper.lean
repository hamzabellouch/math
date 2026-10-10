import Mathlib
import OAI.Computability.MaxCut.Encoding.AdviceLaw
import OAI.Computability.MaxCut.Encoding.TransferredDecoding
import OAI.Computability.MaxCut.Games.IncidenceGap

namespace OAI

/-!
The clean-coordinate upper bound for the actual private-decoding policies.
At every fixed public map `A`, the visible coefficient space is
`Vector d × A.range`.  Its cardinality is at most `2^(d+rs)`, including when
`A` is rank deficient.  The true independent uniform maps `T,M`, the
Bernoulli mask, and all iid occurrence/position draws are retained by the
proved sampling equality, before averaging over the uniform public map.
-/

namespace MaxCutGames.Decoder.ActualAdviceUpper

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open MaxCutGames.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

instance publicMapFintype (s rs : Nat) : Fintype (Alphabet s →ₗ[F2] Vector rs) :=
  Fintype.ofInjective (fun A : Alphabet s →ₗ[F2] Vector rs => (A : Alphabet s → Vector rs))
    DFunLike.coe_injective

/-- The ordinary game uses actual occurrence IDs and actual variable names. -/
def sourceIncidence (S : Source) :
    IncidenceExtraction.Incidence (Fin S.occurrences) (Fin S.«variables») where
  name := ActualGame.names S
  rhs e := (S.equation e).rhs

abbrev Visible (d : Nat) (A : Alphabet s →ₗ[F2] Vector rs) := Vector d × A.range

def complementMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector d :=
  (LinearMap.fst F2 (Vector d) A.range).comp Y

def rowMap {E : Type} [AddCommGroup E] [Module F2 E]
    (A : Alphabet s →ₗ[F2] Vector rs) (Y : E →ₗ[F2] Visible d A) :
    E →ₗ[F2] Vector rs :=
  A.range.subtype.comp ((LinearMap.snd F2 (Vector d) A.range).comp Y)

/-- Decode only the data visible to the first player. -/
def fullInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (occ : Fin k → Fin S.occurrences)
    (Y : ActualHomogeneous.E k →ₗ[F2] Visible d A) :
    VisiblePolicies.LeftInput S k s d (Vector rs) where
  occurrences := occ
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

/-- Decode only the displayed question and the visible row/complement maps. -/
def projectedInput (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Visible d A) :
    VisiblePolicies.RightInput S J s d (Vector rs) where
  question := O
  rowMap := A
  complement := complementMap A Y
  rows := rowMap A Y

/-- Actual observation-local stochastic policies, in the exact advice space
used by the clean-coordinate experiment.  Public `A` is fixed before questions. -/
def policies (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) :
    Clean.ActualAdviceStochasticBridge.Policies k (sourceIncidence S) (Visible d A) where
  first _ occ Y := VisiblePolicies.leftPolicy good (fullInput S A occ Y)
  second J O Y := VisiblePolicies.rightPolicy S labeling J (projectedInput S A J O Y)

/-- The real draw corresponding to a fixed mask and the independently sampled
complement and hidden matrices. -/
def actualDraw (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector rs) where
  singletons := J
  occurrences := occ
  positions := slot
  rowMap := A
  hiddenMatrix := M
  complement := T

theorem fullInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    fullInput S A occ ((AdviceLaw.visibleMap A T M).comp
      (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) =
      AdviceExperiment.leftObservation (ActualGame.rhs S) (actualDraw S A J occ slot T M) :=
  rfl

theorem projectedInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    projectedInput S A J (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M) =
      (AdviceExperiment.rightObservation (ActualGame.names S)
        (actualDraw S A J occ slot T M)).2 :=
  rfl

/-- The product of the two local policy kernels is literally the private
decoder's observed agreement probability, before any expectations are taken. -/
theorem policyAgreement_actual (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (occ : Fin k → Fin S.occurrences) (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    (((policies S labeling good A).first J occ
        ((AdviceLaw.visibleMap A T M).comp
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))).product
      ((policies S labeling good A).second J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M))).probability
        (fun answers => decide
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot answers.1.val =
            answers.2.val)) =
      VisiblePolicies.observedAgreement S labeling good (actualDraw S A J occ slot T M) := by
  dsimp only [policies, sourceIncidence]
  rw [fullInput_actual S A J occ slot T M, projectedInput_actual S A J occ slot T M]
  rfl

/-- The clean experiment's indexed slot is exactly the actual bit projection;
this includes the third-position parity intercept. -/
theorem source_projection_eq (S : Source) (J : Finset (Fin k))
    (draw : Fin k → Fin S.occurrences × Fin 3) :
    Clean.ActualAdviceBridge.projection (sourceIncidence S) J draw =
      RawPrivateTable.projection J (ActualGame.rhs S) (fun j => (draw j).1)
        (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) := by
  simp only [Clean.ActualAdviceBridge.projection, sourceIncidence,
    RawPrivateTable.projection, ActualGame.rhs, toBit_ofBit]

theorem fixed_public_map_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (A : Alphabet s →ₗ[F2] Vector rs)
    (policy : Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  rw [AdviceLaw.actualSuccess_eq_cleanSuccess]
  exact Clean.ActualAdviceBound.stochastic_success_le_dimension_finite g ω policy
    β hβ₀ hβ₁ distinct hopt d rs (Clean.AdviceImageLaw.visible_card_binary_le d rs A)

/-- Rank deficiency is allowed separately at every public-map outcome. -/
theorem public_map_average_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : (A : Alphabet s →ₗ[F2] Vector rs) →
      Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A
          (policy A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  calc
    _ ≤ (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun _ => (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k) :=
      Clean.ActualAdviceBridge.expectation_mono _
        (fun A => fixed_public_map_bound g ω A (policy A) β hβ₀ hβ₁ distinct hopt)
    _ = _ := by
      rw [FiniteDistribution.expectation, ← Finset.sum_mul,
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).normalized, one_mul]

/-- The actual policies selected from the two separate observations obey the
bound under uniform occurrence IDs and every independent private response. -/
theorem actual_source_average_bound (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess
          (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
          (sourceIncidence S) A (policies S labeling good A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k :=
  public_map_average_bound (sourceIncidence S) (FiniteDistribution.uniform (Fin S.occurrences))
    (policies S labeling good) β hβ₀ hβ₁ distinct hopt

end

end MaxCutGames.Decoder.ActualAdviceUpper

end OAI
