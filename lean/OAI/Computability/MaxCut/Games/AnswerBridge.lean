import Mathlib
import OAI.Computability.MaxCut.Games.LabelBound
import OAI.Computability.MaxCut.Games.AdviceImageLaw
import OAI.Computability.MaxCut.Encoding.ActualInputRows

namespace OAI

namespace MaxCutGames.Clean.AnswerBridge

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

end
end MaxCutGames.Clean.AnswerBridge

/-! Explicit hidden-coordinate enumeration in the actual conditional law. -/

namespace MaxCutGames.Soundness.ConditionalIncidences
open scoped BigOperators

def coordinateReindex {A B X : Type} (e : B ≃ A) : (A → X) ≃ (B → X) where
  toFun f := fun b => f (e b)
  invFun g := fun a => g (e.symm a)
  left_inv f := by
    funext a
    exact congrArg f (e.apply_symm_apply a)
  right_inv g := by
    funext b
    exact congrArg g (e.symm_apply_apply b)

theorem raw_conditional_incidence_reindex
    {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D]
    [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (r : ℕ) (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (f : (Fin r → O × N) → ℚ) :
    average (fun sample : RawObservationFibre J name gamma observed =>
      f (fun i => incidence name (sample.val.2 (e i).val))) =
    average (fun fresh : Fin r → O × Fin 3 => f (fun i => incidence name (fresh i))) := by
  calc
    _ = average (fun fresh : InsideDraw (zeroSet J gamma) O =>
        f (fun i => incidence name (fresh (e i)))) :=
      raw_conditional_inside_average J name gamma observed hpos
        (fun fresh => f (fun i => incidence name (fresh (e i))))
    _ = _ := average_equiv (coordinateReindex e)
      (fun fresh : Fin r → O × Fin 3 => f (fun i => incidence name (fresh i)))

theorem raw_conditional_event_reindex_real
    {P D O N : Type} [Fintype P] [DecidableEq P]
    [Fintype D] [Zero D] [DecidableEq D]
    [Fintype O] [DecidableEq O] [DecidableEq N]
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (hpos : 0 < Fintype.card (RawObservationFibre J name gamma observed))
    (r : ℕ) (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Prop) [DecidablePred event] :
    ((∑ sample : RawObservationFibre J name gamma observed,
      if event (fun i => incidence name (sample.val.2 (e i).val)) then (1:ℝ) else 0) /
        Fintype.card (RawObservationFibre J name gamma observed)) =
    ((∑ fresh : Fin r → O × Fin 3,
      if event (fun i => incidence name (fresh i)) then (1:ℝ) else 0) /
        Fintype.card (Fin r → O × Fin 3)) := by
  have hQ := raw_conditional_incidence_reindex J name gamma observed hpos r e
    (fun q => if event q then (1:ℚ) else 0)
  have hR := congrArg (fun q : ℚ => (q : ℝ)) hQ
  simpa only [average, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast,
    apply_ite, Rat.cast_one, Rat.cast_zero] using hR

end MaxCutGames.Soundness.ConditionalIncidences

/-!
# Weighted conditional product law for the clean coordinates

The equation distribution is arbitrary.  All identities below are identities
of finite sums of its actual weights, rather than a reduction to uniform
occurrence sampling.  The clean set is fixed by independently sampled advice;
the only subsequently exposed question data lie outside that set.  Conditioning
on such data preserves the entire joint law of the clean questions.
-/

namespace MaxCutGames.Clean.ProductLaw

open scoped BigOperators
open Foundations.Games
open Soundness.ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P Q S : Type} [Fintype P] [DecidableEq P] [Fintype Q] [Fintype S]

/-- Restriction to the clean and nonclean coordinates is a genuine bijection. -/
def splitCoordinates (K : Finset P) :
    (P → Q) ≃ (PositionInside K → Q) × (PositionOutside K → Q) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ K) (fun _ => Q)

/-- Independent weighted sampling splits into independent clean and nonclean
parts. This identity proves, rather than assumes, their independence. -/
theorem table_split (μ : P → FiniteDistribution Q) (K : Finset P) :
    (FiniteDistribution.table μ).transport (splitCoordinates K) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).product
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro pieces
  change (∏ i, (μ i).weight ((splitCoordinates K).symm pieces i)) =
    (∏ i : PositionInside K, (μ i.val).weight (pieces.1 i)) *
      ∏ i : PositionOutside K, (μ i.val).weight (pieces.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : P => i ∈ K)
    (fun i => (μ i).weight ((splitCoordinates K).symm pieces i))
  have hi : Subtype.fintype (fun i : P => i ∈ K) =
      Finset.Subtype.fintype K := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : PositionInside K,
        (μ i.val).weight ((splitCoordinates K).symm pieces i.val)) *
        ∏ i : PositionOutside K,
          (μ i.val).weight ((splitCoordinates K).symm pieces i.val) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [splitCoordinates, Equiv.piEquivPiSubtypeProd, i.property]

theorem probability_product_and (μ : FiniteDistribution Q) (ν : FiniteDistribution S)
    (event : Q → Bool) (given : S → Bool) :
    (μ.product ν).probability (fun x => event x.1 && given x.2) =
      μ.probability event * ν.probability given := by
  classical
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    Fintype.sum_prod_type]
  calc
    _ = ∑ q, ∑ s, (if event q then μ.weight q else 0) *
        (if given s then ν.weight s else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      cases event q <;> cases given s <;> simp
    _ = _ := by rw [Finset.sum_mul_sum]

theorem probability_product_right (μ : FiniteDistribution Q)
    (ν : FiniteDistribution S) (given : S → Bool) :
    (μ.product ν).probability (fun x => given x.2) = ν.probability given := by
  simpa using probability_product_and μ ν (fun _ => true) given

/-- Exact factorization for an arbitrary joint event of clean coordinates and
an arbitrary observation/event depending only on the nonclean coordinates. -/
theorem table_inside_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (event : (PositionInside K → Q) → Bool)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability
        (fun x => event (fun i => x i.val) && given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  rw [← probability_product_and, ← table_split]
  exact (FiniteDistribution.probability_transport (FiniteDistribution.table μ)
    (splitCoordinates K) (fun pieces => event pieces.1 && given pieces.2)).symm

theorem table_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability (fun x => given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  simpa using table_inside_outside μ K (fun _ => true) given

/-- The normalized conditional law is the ordinary independent product law.
The only hypothesis is that the observed outside event has positive mass. -/
theorem conditioned_inside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (FiniteDistribution.table μ).probability
      (fun x => given (fun i => x i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((FiniteDistribution.table μ).condition
      (fun x => given (fun i => x i.val)) positive).probability
        (fun x => event (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  rw [FiniteDistribution.probability_condition]
  simp_rw [Bool.and_comm (given _)]
  rw [table_inside_outside, table_outside]
  have hne : (FiniteDistribution.table
      (fun i : PositionOutside K => μ i.val)).probability given ≠ 0 := by
    rw [table_outside] at positive
    exact ne_of_gt positive
  exact mul_div_cancel_right₀ _ hne

/-- Fixing an independently sampled seed additionally exposes the intercept and
all slope data, without exposing any of the clean questions. The seed's mass
and the outside-observation mass factor off from every clean event. -/
theorem seeded_inside_outside (ν : FiniteDistribution S)
    (μ : P → FiniteDistribution Q) (seed : S) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (event : (PositionInside K → Q) → Bool) :
    (ν.product (FiniteDistribution.table μ)).probability
      (fun x => (decide (x.1 = seed) && given (fun i => x.2 i.val)) &&
        event (fun i => x.2 i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (ν.weight seed *
          (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given) := by
  simp_rw [Bool.and_assoc, Bool.and_comm (given _)]
  rw [probability_product_and ν (FiniteDistribution.table μ)
    (fun s => decide (s = seed))
    (fun x : P → Q => event (fun i => x i.val) && given (fun i => x i.val)),
    table_inside_outside]
  have hseed : ν.probability (fun s => decide (s = seed)) = ν.weight seed := by
    simp [FiniteDistribution.probability]
  rw [hseed]
  ring

/-- Public conditioning on the independently generated advice, including its
intercept, and on arbitrary nonclean question data leaves the weighted clean
product law unchanged. `K` may be any function of `seed`; it is fixed here after
the public seed has been exposed. -/
theorem conditioned_seed_inside (ν : FiniteDistribution S)
    (μ : P → FiniteDistribution Q) (seed : S) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (ν.product (FiniteDistribution.table μ)).probability
      (fun x => decide (x.1 = seed) && given (fun i => x.2 i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((ν.product (FiniteDistribution.table μ)).condition
      (fun x => decide (x.1 = seed) && given (fun i => x.2 i.val)) positive).probability
        (fun x => event (fun i => x.2 i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  have hgiven := seeded_inside_outside ν μ seed K given (fun _ => true)
  simp only [Bool.and_true, FiniteDistribution.probability_true, one_mul] at hgiven
  rw [FiniteDistribution.probability_condition, seeded_inside_outside, hgiven]
  exact mul_div_cancel_right₀ _ (ne_of_gt (hgiven ▸ positive))

/-- Reindexing a finite coordinate set gives the usual `iid` law on `Fin r`. -/
theorem table_reindex (μ : FiniteDistribution Q) {A : Type} [Fintype A] [DecidableEq A]
    {r : ℕ} (e : Fin r ≃ A) :
    (FiniteDistribution.table (fun _ : A => μ)).transport (coordinateReindex e) =
      μ.iid r := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ a, μ.weight (x (e.symm a))) = ∏ i, μ.weight (x i)
  exact e.symm.prod_comp (fun i => μ.weight (x i))

/-- Fixed advice, intercept and nonclean data preserve precisely the repeated
incidence law for arbitrary occurrence weights. Repeated IDs are permitted. -/
theorem conditioned_incidence_reindex
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Bool) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).probability
          (fun x => event (fun i => incidence name (x (e i).val))) =
      ((μ.pushforward (incidence name)).iid r).probability event := by
  classical
  let given : (PositionOutside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => decide ((fun i => incidence name (x i)) = observed)
  let insideEvent : (PositionInside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => event (fun i => incidence name (x (e i)))
  have h := conditioned_inside (fun _ : P => μ) (zeroSet J gamma)
    given positive insideEvent
  change _ = _ at h
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward]
  rw [← table_reindex μ e, FiniteDistribution.probability_transport]
  exact h

/-- Equality of the complete conditional question distribution, not only its
individual marginals. The target is the ordinary repeated incidence law. -/
theorem conditioned_incidence_distribution
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma)) :
    (((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).pushforward
          (fun x i => incidence name (x (e i).val))) =
      (μ.pushforward (incidence name)).iid r := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro questions
  have h := conditioned_incidence_reindex μ J name gamma observed positive e
    (fun x => decide (x = questions))
  calc
    _ = ((FiniteDistribution.table (fun _ : P => μ)).condition
        (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)) positive).probability
          (fun x => decide ((fun i => incidence name (x (e i).val)) = questions)) := by
      unfold FiniteDistribution.pushforward FiniteDistribution.probability
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : (fun i => incidence name (x (e i).val)) = questions <;> simp [hx]
    _ = _ := h
    _ = _ := by simp [FiniteDistribution.probability]

omit [Fintype P] in
/-- A clean-mask rule reads only the independent advice seed. Thus even after
fixing the entire question tuple, its distribution is unchanged. The seed may
include the projection mask, all slope columns, and the independent intercept. -/
theorem clean_mask_independent (ν : FiniteDistribution S)
    (μ : FiniteDistribution Q) (clean : S → Finset P) (K : Finset P)
    (questionEvent : Q → Bool) :
    (ν.product μ).probability (fun x => decide (clean x.1 = K) && questionEvent x.2) =
      ν.probability (fun s => decide (clean s = K)) * μ.probability questionEvent := by
  exact probability_product_and ν μ (fun s => decide (clean s = K)) questionEvent

end
end MaxCutGames.Clean.ProductLaw

/-!
Weighted total probability for the public clean-coordinate observation.
The observation may have zero-probability fibres. Only its positive fibres
require a conditional bound; the identity itself is proved from finite sums.
-/

namespace MaxCutGames.Clean.WeightedPartition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]

def fibre (observe : Ω → H) (h : H) : Ω → Bool :=
  fun x => decide (observe x = h)

theorem sum_fibre_inter (μ : FiniteDistribution Ω) (observe : Ω → H)
    (event : Ω → Bool) :
    (∑ h, μ.probability (fun x => fibre observe h x && event x)) =
      μ.probability event := by
  classical
  unfold FiniteDistribution.probability fibre
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : event x = true <;> simp [hx]

theorem sum_fibre_bound (μ : FiniteDistribution Ω) (observe : Ω → H)
    (bound : H → ℝ) :
    (∑ h, μ.probability (fibre observe h) * bound h) =
      μ.expectation (fun x => bound (observe x)) := by
  classical
  unfold FiniteDistribution.probability FiniteDistribution.expectation fibre
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq, ite_mul, zero_mul]
  simp

/-- The averaging step for a genuine weighted observation. No conditional
independence or law-of-total-probability equality is supplied as a premise. -/
theorem probability_le_conditional_bounds (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : H → ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound h) :
    μ.probability event ≤ μ.expectation (fun x => bound (observe x)) := by
  rw [← sum_fibre_inter μ observe event, ← sum_fibre_bound μ observe bound]
  apply Finset.sum_le_sum
  intro h _
  by_cases positive : 0 < μ.probability (fibre observe h)
  · rw [μ.probability_inter_eq_mul_conditional (fibre observe h) event positive]
    exact mul_le_mul_of_nonneg_left (conditional h positive) positive.le
  · have zero : μ.probability (fibre observe h) = 0 :=
      le_antisymm (le_of_not_gt positive) (μ.probability_nonnegative _)
    rw [μ.probability_and_eq_zero_of_probability_eq_zero (fibre observe h) event zero,
      zero, zero_mul]

/-- A constant bound survives arbitrary public outside observations. -/
theorem probability_le_of_conditional_le (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound) :
    μ.probability event ≤ bound := by
  have estimate := probability_le_conditional_bounds μ observe event
    (fun _ => bound) conditional
  have constant : μ.expectation (fun _ => bound) = bound := by
    rw [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]
  simpa only [constant] using estimate

end
end MaxCutGames.Clean.WeightedPartition

/-!
The actual local simulation in Lemma 6.8 after fixing H. These reconstruction
maps consume only the first player's occurrence tuple or the second player's
name tuple. Its winning-event containment is proved from the concrete equation
and named-projection predicates.
-/

namespace MaxCutGames.Soundness.ConditionalSimulation

open Foundations.Games ConditionalIncidences IncidenceExtraction
open RepeatedGameBounds

noncomputable section

instance firstInputFintype {P R O : Type} [Fintype P] [Fintype R] [Fintype O] :
    Fintype (ZeroInformation.FirstInput P R O) := by
  classical
  exact Fintype.ofEquiv ((P → O) × ZeroInformation.FirstRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

instance secondInputFintype {P R O N : Type}
    [Fintype P] [Fintype R] [Fintype O] [Fintype N] :
    Fintype (ZeroInformation.SecondInput P R O N) := by
  classical
  exact Fintype.ofEquiv ((P → Sum O N) × ZeroInformation.SecondRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

def incidenceGame {O N : Type} [Fintype O] [Fintype N]
    (g : Incidence O N) (mu : FiniteDistribution (O × N)) :
    Foundations.Games.Game O N Triple Bool :=
  Simulation.weightedGame ⟨g.namedAccepts⟩ mu

def actualLocalSimulation
    {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (mu : FiniteDistribution (O × N))
    (enumerate : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma)) :
    IncidenceExtraction.LocalSimulation
      (Simulation.predicateGame ((incidenceGame g mu).repetition (zeroSet J gamma).card))
      (ActualProjection.predicateGame (R := R) g (membershipBool J)) where
  questionA qa := localFirstFromH J g.name gamma observed reference
    (fun j => qa (enumerate.symm j))
  questionB qb := localSecondFromH J g.name gamma observed reference
    (fun j => qb (enumerate.symm j))
  answerA _ answer i := answer.2 (enumerate i).val
  answerB _ answer i := answer.2.2 (enumerate i).val
  sound := by
    classical
    intro qa qb answerA answerB haccept
    change ((incidenceGame g mu).repetition (zeroSet J gamma).card).accepts _ _ _ _ = true
    rw [Foundations.Games.Game.repetition_accepts_iff]
    intro i
    change decide (g.namedAccepts (qa i) (qb i)
      (answerA.2 (enumerate i).val) (answerB.2.2 (enumerate i).val)) = true
    rw [decide_eq_true_eq]
    have hj : (enumerate i).val ∈ J := zeroSet_subset J gamma (enumerate i).property
    have hsingle : membershipBool J (enumerate i).val = true := by
      simp [membershipBool, hj]
    have hname : (localSecondFromH J g.name gamma observed reference
        (fun j => qb (enumerate.symm j))).question (enumerate i).val = Sum.inr (qb i) := by
      simpa using localSecondFromH_question_inside J g.name gamma observed reference
        (fun j => qb (enumerate.symm j)) (enumerate i)
    have h := ActualProjection.accepts_implies_named_incidence g (membershipBool J)
      _ _ answerA answerB haccept (enumerate i).val hsingle (qb i) hname
    simpa only [localFirstFromH_question_inside, Equiv.symm_apply_apply] using h

theorem actual_conditioned_strategy_success_le_repeated_value
    {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (mu : FiniteDistribution (O × N))
    (enumerate : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : IncidenceExtraction.Strategies
      (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)) :
    (Simulation.reconstructedGame
      ((incidenceGame g mu).repetition (zeroSet J gamma).card)
      (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (actualLocalSimulation J g gamma observed reference mu enumerate)).success
        (Simulation.strategyPair strategy) ≤
      ((incidenceGame g mu).repetition (zeroSet J gamma).card).value := by
  exact (Simulation.reconstructedGame_success_le
    ((incidenceGame g mu).repetition (zeroSet J gamma).card)
    (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (actualLocalSimulation J g gamma observed reference mu enumerate) strategy).trans
      (((incidenceGame g mu).repetition (zeroSet J gamma).card).success_le_value _)

end
end MaxCutGames.Soundness.ConditionalSimulation

/-! The genuine conditional experiment is the reconstructed repeated-game law. -/

namespace MaxCutGames.Soundness.ConditionalGameLaw
open scoped BigOperators
open Foundations.Games
open ConditionalIncidences ConditionalSimulation IncidenceExtraction RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_probability_decide {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (event : Ω → Prop) [DecidablePred event] :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (event x)) =
      (∑ x, if event x then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := by
  classical
  calc
    _ = (FiniteDistribution.uniform Ω).expectation
        (fun x => if event x then (1 : ℝ) else 0) := by
      unfold FiniteDistribution.probability FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : event x <;> simp [hx]
    _ = _ := FiniteDistribution.expectation_uniform _

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

abbrev OuterStrategy := IncidenceExtraction.Strategies
  (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
  (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)

def actualWin (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) (draw : Draw P O) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (actualFirst J gamma draw) (actualSecond J g.name gamma draw)

def conditionedWinProbability (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) : ℝ := by
  classical
  letI : Nonempty (RawObservationFibre J g.name gamma observed) := ⟨reference⟩
  exact (FiniteDistribution.uniform (RawObservationFibre J g.name gamma observed)).probability
    (fun sample => decide (actualWin J g gamma strategy sample.val.2))

def reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (questions : Fin (zeroSet J gamma).card → O × N) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (localFirstFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).1))
    (localSecondFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).2))

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualWin_iff_reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (sample : RawObservationFibre J g.name gamma observed) :
    actualWin J g gamma strategy sample.val.2 ↔
      reconstructedEvent J g gamma observed reference e strategy
        (fun i => incidence g.name (sample.val.2 (e i).val)) := by
  unfold actualWin reconstructedEvent
  simp only [incidence, Equiv.apply_symm_apply]
  rw [localFirstFromH_correct J g.name gamma observed distinct reference sample,
    localSecondFromH_correct J g.name gamma observed reference sample]

omit [Fintype N] in
theorem conditionedWinProbability_eq_fresh (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    conditionedWinProbability J g gamma observed reference strategy =
      (∑ fresh : Fin (zeroSet J gamma).card → O × Fin 3,
        if reconstructedEvent J g gamma observed reference e strategy
          (fun i => incidence g.name (fresh i)) then (1:ℝ) else 0) /
          Fintype.card (Fin (zeroSet J gamma).card → O × Fin 3) := by
  classical
  let : Nonempty (RawObservationFibre J g.name gamma observed) := ⟨reference⟩
  have hpos : 0 < Fintype.card (RawObservationFibre J g.name gamma observed) := Fintype.card_pos
  unfold conditionedWinProbability
  rw [uniform_probability_decide]
  have hraw := raw_conditional_event_reindex_real J g.name gamma observed hpos
    (zeroSet J gamma).card e (reconstructedEvent J g gamma observed reference e strategy)
  simpa only [← actualWin_iff_reconstructedEvent J g gamma observed reference e strategy distinct]
    using hraw

def incidenceLaw [Nonempty O] (g : Incidence O N) : FiniteDistribution (O × N) :=
  (FiniteDistribution.uniform (O × Fin 3)).pushforward (incidence g.name)

theorem reconstructed_success_eq_fresh_average [Nonempty O]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) :
    (Simulation.reconstructedGame
      ((incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card)
      (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (actualLocalSimulation J g gamma observed reference (incidenceLaw g) e)).success
        (Simulation.strategyPair strategy) =
      (∑ fresh : Fin (zeroSet J gamma).card → O × Fin 3,
        if reconstructedEvent J g gamma observed reference e strategy
          (fun i => incidence g.name (fresh i)) then (1:ℝ) else 0) /
          Fintype.card (Fin (zeroSet J gamma).card → O × Fin 3) := by
  classical
  let G := (incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card
  let outer := ActualProjection.predicateGame (R := R) g (membershipBool J)
  let r := actualLocalSimulation J g gamma observed reference (incidenceLaw g) e
  change (G.questions.pushforward (fun q => (r.questionA q.1, r.questionB q.2))).probability
    (fun q => decide (strategy.wins outer q.1 q.2)) = _
  rw [FiniteDistribution.probability_pushforward]
  change (((incidenceLaw g).iid (zeroSet J gamma).card).transport
    (Foundations.Games.Game.tupleQuestionEquiv (zeroSet J gamma).card)).probability
      (fun q => decide (strategy.wins outer (r.questionA q.1) (r.questionB q.2))) = _
  rw [FiniteDistribution.probability_transport]
  unfold incidenceLaw
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.iid_uniform,
    FiniteDistribution.probability_pushforward]
  change (FiniteDistribution.uniform (Fin (zeroSet J gamma).card → O × Fin 3)).probability
    (fun fresh => decide (reconstructedEvent J g gamma observed reference e strategy
      (fun i => incidence g.name (fresh i)))) = _
  exact uniform_probability_decide _

/-- The actual finite observation-fibre probability is bounded by the genuine
    repeated incidence-game value. The sampling identity is proved internally. -/
theorem conditioned_probability_le_repeated_value [Nonempty O]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    conditionedWinProbability J g gamma observed reference strategy ≤
      ((incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card).value := by
  rw [conditionedWinProbability_eq_fresh J g gamma observed reference e strategy distinct,
    ← reconstructed_success_eq_fresh_average J g gamma observed reference e strategy]
  exact actual_conditioned_strategy_success_le_repeated_value
    J g gamma observed reference (incidenceLaw g) e strategy

end
end MaxCutGames.Soundness.ConditionalGameLaw

end OAI
