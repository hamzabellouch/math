import OAI.Computability.UniqueGames.Soundness.ActualCanonicalPullbackLemmas
import OAI.Computability.UniqueGames.Soundness.ActualPointAnswers

namespace OAI

section

namespace UniqueGamesTheorem.Clean.AnswerBridge

open Integration.BinaryLinear
open Reduction
open Soundness
open Soundness.RepeatedGameBounds
open Soundness.RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {Q Id Name : Type}

abbrev FirstInput := ZeroInformation.FirstInput (Fin k) Q Id
abbrev SecondInput := ZeroInformation.SecondInput (Fin k) Q Id Name

abbrev SourceAnswer (k : ℕ) := {x : ActualHomogeneous.E k // ActualHomogeneous.tau x = 1}
abbrev TargetAnswer (J : Finset (Fin k)) := {v : RawPoint J // v none = 1}

abbrev PointStrategies (J : Finset (Fin k)) := IncidenceExtraction.Strategies
  (FirstInput (k := k) (Q := Q) (Id := Id))
  (SecondInput (k := k) (Q := Q) (Id := Id) (Name := Name))
  (SourceAnswer k) (TargetAnswer J)

theorem firstAnswer_eq_embed (rhs : Fin k → Bool) (x : ActualHomogeneous.E k) :
    ActualPointAnswers.firstAnswer rhs x =
      (toBit x.1, fun j i =>
        toBit ((ActualHomogeneous.embed (fun j => ofBit (rhs j)) x).2 j i)) := by
  apply Prod.ext
  · rfl
  · funext j i
    fin_cases i
    · rfl
    · rfl
    · change (((rhs j && toBit x.1) ^^ toBit (x.2 j).1) ^^ toBit (x.2 j).2) =
        toBit (ofBit (rhs j) * x.1 + (x.2 j).1 + (x.2 j).2)
      have h := congrArg toBit (ActualCanonicalPullback.ofBit_and (rhs j) (toBit x.1))
      rw [toBit_ofBit, ofBit_toBit] at h
      rw [toBit_add, toBit_add, ← h]

/-- Convert a pair of genuine local point strategies into the ordinary answer
type used by the clean-coordinate local simulation. -/
def toOuterStrategy (J : Finset (Fin k)) (g : IncidenceExtraction.Incidence Id Name)
    (strategy : PointStrategies (Q := Q) (Id := Id) (Name := Name) J) :
    IncidenceExtraction.Strategies
      (FirstInput (k := k) (Q := Q) (Id := Id))
      (SecondInput (k := k) (Q := Q) (Id := Id) (Name := Name))
      (ActualProjection.FirstAnswer (Fin k)) (ActualProjection.SecondAnswer (Fin k)) where
  first qa := ActualPointAnswers.firstAnswer (fun j => g.rhs (qa.question j))
    (strategy.first qa).val
  second qb := ActualPointAnswers.secondAnswer
    (ActualPointAnswers.displayedRhs g.rhs qb.question) J (strategy.second qb).val

/-- Projection agreement of matrix answers implies the named verifier accepts.
No question-law or value assumption occurs in this pointwise bridge. -/
theorem toOuterStrategy_wins (J : Finset (Fin k))
    (g : IncidenceExtraction.Incidence Id Name)
    (strategy : PointStrategies (Q := Q) (Id := Id) (Name := Name) J)
    (qa : FirstInput (k := k) (Q := Q) (Id := Id))
    (qb : SecondInput (k := k) (Q := Q) (Id := Id) (Name := Name))
    (slot : Fin k → PartnerProjection.Slot)
    (hquestion : qb.question = RawPrivateTable.displayed J g.name qa.question slot)
    (hagreement : rawProjection (fun j => g.rhs (qa.question j)) J slot
      (strategy.first qa).val = (strategy.second qb).val) :
    (toOuterStrategy J g strategy).wins
      (ActualProjection.predicateGame g (PartnerMapCoordinates.activeOf J)) qa qb := by
  exact ActualPointAnswers.actual_accepts J g qa qb slot hquestion
    (strategy.first qa).val (strategy.second qb).val (strategy.first qa).property hagreement

section RowEncoding

open Soundness.ConditionalIncidences Soundness.BinaryRowTransport
open scoped BigOperators

variable {D : Type} [AddCommGroup D] [Module F2 D]

/-- A basis supplies the required coordinates for every finite-dimensional
combined advice space; this choice is independent of the equation questions. -/
def finiteCoordinates [FiniteDimensional F2 D] :
    D ≃ₗ[F2] (Fin (Module.finrank F2 D) → F2) :=
  (Module.finBasis F2 D).equivFun

/-- The coordinate map is a bijection all the way to the actual bit-row type. -/
def bitsCoordinatesEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) :
    D ≃ ZeroInformation.Bits Q :=
  coordinates.toEquiv.trans rowBitsEquiv

def encodeCoefficients (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (gamma : RawCoefficients J D) :
    RawCoefficients J (ZeroInformation.Bits Q) :=
  fun s => rowBits (coordinates (gamma s))

def coefficientsEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k)) :
    RawCoefficients J D ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  Equiv.piCongrRight (fun _ => bitsCoordinatesEquiv coordinates)

/-- The encoding sends the actual uniform coefficient law to the uniform bit
coefficient law, counting every intercept and slope exactly once. -/
theorem uniform_encoded_coefficients [Fintype D] [Fintype Q]
    (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k))
    (F : RawCoefficients J (ZeroInformation.Bits Q) → ℝ) :
    (𝔼 gamma : RawCoefficients J D, F (encodeCoefficients coordinates J gamma)) =
      𝔼 bits : RawCoefficients J (ZeroInformation.Bits Q), F bits :=
  Fintype.expect_equiv (coefficientsEquiv coordinates J) _ F (fun _ => rfl)

theorem encoded_map_coefficients (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y)) =
      encodeCoefficients coordinates J (gammaOfRawMap J Y) := rfl

/-- Encoding the advice preserves exactly the zero-slope clean set. -/
theorem zeroSet_encodeCoefficients [Fintype Q] [DecidableEq Q] [DecidableEq D]
    (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (gamma : RawCoefficients J D) :
    zeroSet J (encodeCoefficients coordinates J gamma) = zeroSet J gamma := by
  ext j
  simp only [mem_zeroSet, encodeCoefficients]
  apply exists_congr
  intro hj
  change (rowBits (coordinates (gamma (some (.inr ⟨j, hj⟩)))) = ZeroInformation.zero) ↔
    gamma (some (.inr ⟨j, hj⟩)) = 0
  rw [rowBits_eq_zero]
  rw [← coordinates.map_zero]
  exact coordinates.injective.eq_iff

/-- Transport a local strategy on genuine row maps to the complete bit-row
input type. The same fixed public data may be closed over in both policies.
All remaining inputs are private to the respective prover. -/
def rowPointStrategies (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (rhs : Id → Bool)
    (first : (Fin k → Id) → (ActualHomogeneous.E k →ₗ[F2] D) → SourceAnswer k)
    (second : (Fin k → Sum Id Name) → (RawPoint J →ₗ[F2] D) → TargetAnswer J) :
    PointStrategies (Q := Q) (Id := Id) (Name := Name) J where
  first qa := first qa.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap rhs qa))
  second qb := second qb.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J qb))

theorem rowPointStrategies_first_actual [Fintype Q] [DecidableEq Q]
    (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (rhs : Id → Bool)
    (first : (Fin k → Id) → (ActualHomogeneous.E k →ₗ[F2] D) → SourceAnswer k)
    (second : (Fin k → Sum Id Name) → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (occ : Fin k → Id) (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPoint J →ₗ[F2] D) :
    (rowPointStrategies coordinates J rhs first second).first
      (actualFirst J
        (rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y)))
        (fun j => (occ j, ConcreteExtraction.slotIndex (slot j)))) =
      first occ (Y.comp (rawProjection (fun j => rhs (occ j)) J slot)) := by
  change first occ (coordinates.symm.toLinearMap.comp
    (ActualInputRows.firstMap rhs _)) = _
  rw [ActualInputRows.firstMap_actual]
  congr 1
  apply LinearMap.ext
  intro x
  simp

/-- The target policy receives the original target map and displayed question,
without an occurrence or selected slot supplied at a singleton coordinate. -/
theorem rowPointStrategies_second_actual [Fintype Q] [DecidableEq Q]
    (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (rhs : Id → Bool) (names : Id → Fin 3 → Name)
    (first : (Fin k → Id) → (ActualHomogeneous.E k →ₗ[F2] D) → SourceAnswer k)
    (second : (Fin k → Sum Id Name) → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (draw : Draw (Fin k) Id) (Y : RawPoint J →ₗ[F2] D) :
    (rowPointStrategies coordinates J rhs first second).second
      (actualSecond J names
        (rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y))) draw) =
      second
        (actualSecond J names
          (rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y))) draw).question
        Y := by
  change second _ (coordinates.symm.toLinearMap.comp
    (ActualInputRows.secondMap J _)) = _
  rw [ActualInputRows.secondMap_actual]
  congr 1
  apply LinearMap.ext
  intro x
  simp

/-- A default actual target answer is used only for unsupported displayed
questions, which never occur in the experiment. -/
def defaultTargetAnswer (J : Finset (Fin k)) : TargetAnswer J :=
  ⟨Pi.single none 1, by simp⟩

/-- Extend a policy defined on supported private questions to a total local
answer function. The support decision uses only the displayed question. -/
def extendSupportedPolicy (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (policy : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (question : Fin k → Sum Id Name) (Y : RawPoint J →ₗ[F2] D) : TargetAnswer J :=
  if h : question ∈ Set.range
      (fun e : RawPrivateTable.Extension k Id => RawPrivateTable.displayed J names e.1 e.2)
  then policy ⟨question, h⟩ Y else defaultTargetAnswer J

theorem extendSupportedPolicy_apply (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (policy : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (V : RawPrivateTable.SupportedV J names) (Y : RawPoint J →ₗ[F2] D) :
    extendSupportedPolicy J names policy V.val Y = policy V Y := by
  unfold extendSupportedPolicy
  rw [dite_eq_left V.property]
  congr 1

end RowEncoding

end
end UniqueGamesTheorem.Clean.AnswerBridge

end

end OAI
