import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Foundations.FiniteTrialsLemmas
import OAI.Computability.UniqueGames.Soundness.ActualCanonicalPullbackLemmas
import OAI.Computability.UniqueGames.Soundness.ExpectationComparisonLemmas
import OAI.Computability.UniqueGames.Soundness.SubsetIntersectionLemmas
import OAI.Computability.UniqueGames.Soundness.ZeroInformationLemmas

namespace OAI

section

/-!
# Exact partner-map laws in shared raw target coordinates

Inactive positions do not use a retained slot. Replacing their slots leaves
both the concrete partner projection and the shared raw projection unchanged.

The row/column expectation identity below transports the two actual uniform
map samples through the target coordinate equivalence independently. It is an
exact identity for every observable of the pulled-back maps; it requires no
trace, character, or naturality hypotheses.
-/

namespace UniqueGamesTheorem.Soundness.RawTargetLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget

/-- The genuine partner projection reads retained slots only at active positions. -/
theorem partnerProjection_congr_slots {k : Nat} (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot slot' : Fin k → Slot)
    (agree : ∀ j ∈ J, slot j = slot' j) :
    PartnerLinear.projection rhs (activeOf J) slot =
      PartnerLinear.projection rhs (activeOf J) slot' := by
  apply PartnerFullSampling.projection_eq_of_slots_eq_on_active
  intro j hj
  exact agree j (by simpa [activeOf] using hj)

/-- The shared raw target also ignores every inactive retained-slot choice. -/
theorem rawProjection_congr_slots {k : Nat} (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot slot' : Fin k → Slot)
    (agree : ∀ j ∈ J, slot j = slot' j) :
    RawPartnerTarget.rawProjection rhs J slot =
      RawPartnerTarget.rawProjection rhs J slot' := by
  unfold RawPartnerTarget.rawProjection
  rw [partnerProjection_congr_slots rhs J slot slot' agree]

theorem precompose_rawProjection {k : Nat} (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot : Fin k → Slot)
    {R : Type} [AddCommGroup R] [Module F2 R]
    (M : RawPoint J →ₗ[F2] R) :
    (M.comp (pointEquiv rhs J).toLinearMap).comp
        ((PartnerLinear.projection rhs (activeOf J) slot).comp
          (PartnerLinear.sourceLinearEquiv rhs).symm.toLinearMap) =
      M.comp (RawPartnerTarget.rawProjection rhs J slot) := by
  simp only [RawPartnerTarget.rawProjection, LinearMap.comp_assoc]

/-- Exact nested uniform expectations in partner versus raw coordinates.
    Any finite enumerations of the four map spaces may be used. -/
theorem partner_row_column_expectation {k : Nat} (rhs : Fin k → Bool)
    (J : Finset (Fin k)) (slot : Fin k → Slot)
    {D C : Type} [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
    [Fintype (PartnerPoint rhs (activeOf J) →ₗ[F2] D)]
    [Fintype (PartnerPoint rhs (activeOf J) →ₗ[F2] C)]
    [Fintype (RawPoint J →ₗ[F2] D)] [Fintype (RawPoint J →ₗ[F2] C)]
    (H : (ActualHomogeneous.E k →ₗ[F2] D) →
      (ActualHomogeneous.E k →ₗ[F2] C) → ℝ) :
    (𝔼 Z : PartnerPoint rhs (activeOf J) →ₗ[F2] D,
      𝔼 X : PartnerPoint rhs (activeOf J) →ₗ[F2] C,
        let pi := (PartnerLinear.projection rhs (activeOf J) slot).comp
          (PartnerLinear.sourceLinearEquiv rhs).symm.toLinearMap
        H (Z.comp pi) (X.comp pi)) =
    (𝔼 Z : RawPoint J →ₗ[F2] D, 𝔼 X : RawPoint J →ₗ[F2] C,
      H (Z.comp (RawPartnerTarget.rawProjection rhs J slot))
        (X.comp (RawPartnerTarget.rawProjection rhs J slot))) := by
  symm
  apply Fintype.expect_equiv
    (ActualMapComparison.sourcePrecomposeEquiv (R := D) (pointEquiv rhs J))
  intro Z
  apply Fintype.expect_equiv
    (ActualMapComparison.sourcePrecomposeEquiv (R := C) (pointEquiv rhs J))
  intro X
  change H (Z.comp (RawPartnerTarget.rawProjection rhs J slot))
      (X.comp (RawPartnerTarget.rawProjection rhs J slot)) =
    H ((Z.comp (pointEquiv rhs J).toLinearMap).comp
        ((PartnerLinear.projection rhs (activeOf J) slot).comp
          (PartnerLinear.sourceLinearEquiv rhs).symm.toLinearMap))
      ((X.comp (pointEquiv rhs J).toLinearMap).comp
        ((PartnerLinear.projection rhs (activeOf J) slot).comp
          (PartnerLinear.sourceLinearEquiv rhs).symm.toLinearMap))
  simp only [precompose_rawProjection]

end UniqueGamesTheorem.Soundness.RawTargetLaw

end

section

/-!
# Concrete finite averaging for the projection upper bound

The coefficient samples here are actual functions `Fin t → (Fin m → ZMod 2)`.
Their law is the normalized finite uniform sum over all such functions. The
binomial moment formula is proved from this sum, without an independence or
binomial-distribution premise.
-/

namespace UniqueGamesTheorem.Soundness.RepeatedGameBounds

open scoped BigOperators

noncomputable section

/-- The normalized uniform sum on a concrete finite outcome space. -/
def uniformAverage {Ω K : Type*} [Fintype Ω] [Field K] (f : Ω → K) : K :=
  (∑ ω, f ω) / (Fintype.card Ω : K)

/-- Number of zero columns in an actual coefficient vector. -/
def zeroCount {I C : Type*} [Fintype I] [Zero C] [DecidableEq C]
    (omega : I → C) : Nat :=
  (Finset.univ.filter fun j => omega j = 0).card

theorem power_zeroCount_eq_prod {I C K : Type*} [Fintype I] [Zero C] [DecidableEq C]
    [CommMonoid K] (a : K) (omega : I → C) :
    a ^ zeroCount omega = ∏ j, if omega j = 0 then a else 1 := by
  rw [← Finset.prod_filter]
  simp [zeroCount]

theorem sum_one_zero_weight {C K : Type*} [Fintype C] [Zero C]
    [DecidableEq C] [Field K] (a : K) :
    (∑ c : C, if c = 0 then a else 1) = (Fintype.card C : K) + a - 1 := by
  classical
  have hpoint : (fun c : C => if c = 0 then a else (1 : K)) =
      fun c => 1 + if c = 0 then a - 1 else 0 := by
    funext c
    split_ifs <;> ring
  rw [hpoint, Finset.sum_add_distrib]
  simp
  ring

/-- The unnormalized count identity, on the actual full product space. -/
theorem sum_power_zeroCount {C K : Type*} [Fintype C] [Zero C]
    [DecidableEq C] [Field K] (a : K) (t : Nat) :
    (∑ omega : Fin t → C, a ^ zeroCount omega) =
      ((Fintype.card C : K) + a - 1) ^ t := by
  simp_rw [power_zeroCount_eq_prod]
  rw [← Fintype.sum_pow (fun c : C => if c = 0 then a else 1) t,
    sum_one_zero_weight]

/-- Exact moment identity for independent uniform coefficients in any finite
nonempty zero-pointed space, proved by enumeration and product expansion. -/
theorem uniformAverage_power_zeroCount {C K : Type*} [Fintype C] [Zero C]
    [DecidableEq C] [Field K] [CharZero K] (a : K) (t : Nat) :
    uniformAverage (fun omega : Fin t → C => a ^ zeroCount omega) =
      (1 - (1 / (Fintype.card C : K)) * (1 - a)) ^ t := by
  have hC : (Fintype.card C : K) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformAverage
  rw [sum_power_zeroCount]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← div_pow]
  congr 1
  field_simp
  ring

/-- Binary vectors of length `m`, the actual coefficient alphabet. -/
abbrev BinaryCoefficient (m : Nat) := Fin m → ZMod 2

theorem card_binaryCoefficient (m : Nat) : Fintype.card (BinaryCoefficient m) = 2 ^ m := by
  simp [BinaryCoefficient]

/-- The precise averaging identity from Lemma 6.8, including zero-dimensional
coefficient spaces and zero trials. -/
theorem uniform_binary_coefficient_moment {K : Type*} [Field K] [CharZero K]
    (a : K) (m t : Nat) :
    uniformAverage (fun omega : Fin t → BinaryCoefficient m => a ^ zeroCount omega) =
      (1 - (1 / 2 : K) ^ m * (1 - a)) ^ t := by
  rw [uniformAverage_power_zeroCount, card_binaryCoefficient]
  simp

theorem uniformAverage_mono {Ω K : Type*} [Fintype Ω]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {f g : Ω → K} (h : ∀ ω, f ω ≤ g ω) : uniformAverage f ≤ uniformAverage g := by
  unfold uniformAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

theorem uniformAverage_const {Ω K : Type*} [Fintype Ω] [Nonempty Ω]
    [Field K] [CharZero K] (c : K) : uniformAverage (fun _ : Ω => c) = c := by
  have hΩ : (Fintype.card Ω : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformAverage, mul_div_cancel_left₀, hΩ]

/-- Iterated averaging equals a single average on the actual product space. -/
theorem uniformAverage_prod {Ω Γ K : Type*} [Fintype Ω] [Fintype Γ]
    [Field K] (f : Ω × Γ → K) :
    uniformAverage f = uniformAverage (fun ω => uniformAverage fun γ => f (ω, γ)) := by
  simp only [uniformAverage, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem uniformAverage_equiv {Ω Γ K : Type*} [Fintype Ω] [Fintype Γ]
    [Field K] (e : Ω ≃ Γ) (f : Γ → K) :
    uniformAverage (fun omega => f (e omega)) = uniformAverage f := by
  unfold uniformAverage
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformAverage_product_left {Ω Γ K : Type*} [Fintype Ω] [Fintype Γ]
    [Nonempty Γ] [Field K] [CharZero K] (f : Ω → K) :
    uniformAverage (fun omega : Ω × Γ => f omega.1) = uniformAverage f := by
  rw [uniformAverage_prod]
  simp_rw [uniformAverage_const]

theorem uniformAverage_coordinate_product {I C K : Type*} [Fintype I] [DecidableEq I] [Fintype C]
    [Field K] (f : I → C → K) :
    uniformAverage (fun omega : I → C => ∏ i, f i (omega i)) =
      ∏ i, uniformAverage (f i) := by
  classical
  unfold uniformAverage
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod]
  rw [Finset.prod_div_distrib]

theorem uniformAverage_power_zeroCount_indexed {I C K : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [Zero C] [DecidableEq C] [Field K] [CharZero K] (a : K) :
    uniformAverage (fun omega : I → C => a ^ zeroCount omega) =
      (1 - (1 / (Fintype.card C : K)) * (1 - a)) ^ Fintype.card I := by
  simp_rw [power_zeroCount_eq_prod]
  rw [uniformAverage_coordinate_product (fun _ c => if c = 0 then a else 1)]
  simp only [uniformAverage, sum_one_zero_weight, Finset.prod_const, Finset.card_univ]
  congr 1
  have hC : (Fintype.card C : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

open ConditionalIncidences in
def splitRawCoefficients {P C : Type} (J : Finset P) :
    RawCoefficients J C ≃ (PositionInside J → C) ×
      (Option (PositionOutside J × Fin 2) → C) where
  toFun gamma := (fun j => gamma (some (.inr j)), fun slot =>
    match slot with
    | none => gamma none
    | some j => gamma (some (.inl j)))
  invFun pieces slot := match slot with
    | none => pieces.2 none
    | some (.inl j) => pieces.2 (some j)
    | some (.inr j) => pieces.1 j
  left_inv gamma := by
    funext slot
    cases slot with
    | none => rfl
    | some slot => cases slot <;> rfl
  right_inv pieces := by
    apply Prod.ext
    · rfl
    · funext slot; cases slot <;> rfl

theorem zeroSet_card_eq_zeroCount {P C : Type} [DecidableEq P] [Zero C]
    [DecidableEq C] (J : Finset P) (gamma : ConditionalIncidences.RawCoefficients J C) :
    (ConditionalIncidences.zeroSet J gamma).card =
      zeroCount ((splitRawCoefficients J) gamma).1 := by
  simp [ConditionalIncidences.zeroSet, zeroCount, splitRawCoefficients]
  rfl

/-- The full raw coefficient tuple includes ζ₀ and both coefficients at every
full position. Their uniform averaging cancels exactly; no ignored-coordinate
independence premise is needed. -/
theorem uniform_raw_coefficient_moment {P C K : Type} [Fintype P] [DecidableEq P]
    [Fintype C] [Zero C] [DecidableEq C] [Field K] [CharZero K]
    (J : Finset P) (a : K) :
    uniformAverage (fun gamma : ConditionalIncidences.RawCoefficients J C =>
      a ^ (ConditionalIncidences.zeroSet J gamma).card) =
      (1 - (1 / (Fintype.card C : K)) * (1 - a)) ^ J.card := by
  simp_rw [zeroSet_card_eq_zeroCount]
  rw [uniformAverage_equiv (splitRawCoefficients J)
    (fun pieces => a ^ zeroCount pieces.1)]
  rw [uniformAverage_product_left
    (fun omega : ConditionalIncidences.PositionInside J → C => a ^ zeroCount omega),
    uniformAverage_power_zeroCount_indexed]
  simp [ConditionalIncidences.PositionInside]

/-- Averages an actual pointwise coefficient-dependent upper bound over the
uniform product law. No binomial distribution is assumed. -/
theorem uniform_binary_coefficient_upper {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a : K) (m t : Nat) (success : (Fin t → BinaryCoefficient m) → K)
    (bound : ∀ omega, success omega ≤ a ^ zeroCount omega) :
    uniformAverage success ≤ (1 - (1 / 2 : K) ^ m * (1 - a)) ^ t := by
  calc
    uniformAverage success ≤ uniformAverage
        (fun omega : Fin t → BinaryCoefficient m => a ^ zeroCount omega) :=
      uniformAverage_mono bound
    _ = _ := uniform_binary_coefficient_moment a m t

/-! ## Actual weighted winning probabilities under a local simulation -/

open Foundations.Games

namespace Simulation

abbrev PredicateGame := IncidenceExtraction.Game
abbrev PredicateStrategies := IncidenceExtraction.Strategies

variable {QA QB A B OA OB X Y : Type}
  [Fintype QA] [Fintype QB] [Fintype A] [Fintype B]
  [Fintype OA] [Fintype OB] [Fintype X] [Fintype Y]

/-- Pass a Boolean verifier predicate to the already checked deterministic
local-reconstruction and incidence-extraction interface. -/
def predicateGame (G : Game QA QB A B) : PredicateGame QA QB A B :=
  ⟨fun qa qb a b => G.accepts qa qb a b = true⟩

def strategyPair (s : PredicateStrategies QA QB A B) : Strategy QA QB A B :=
  (s.first, s.second)

/-- Interpret a concrete predicate and a normalized finite question law as a
game with the common foundation interface. -/
def weightedGame (G : PredicateGame QA QB A B)
    (questions : FiniteDistribution (QA × QB)) : Game QA QB A B := by
  classical
  exact ⟨questions, fun qa qb a b => decide (G.accepts qa qb a b)⟩

/-- The reconstructed outer question law is the actual pushforward of the
inner question law under the separate local reconstruction functions. -/
def reconstructedGame (inner : Game QA QB A B) (outer : PredicateGame OA OB X Y)
    (r : IncidenceExtraction.LocalSimulation (predicateGame inner) outer) :
    Game OA OB X Y :=
  weightedGame outer (inner.questions.pushforward fun questions =>
    (r.questionA questions.1, r.questionB questions.2))

/-- Event containment from `IncidenceExtraction` becomes an inequality of the
actual normalized winning sums. The outer law is constructed, not assumed. -/
theorem reconstructedGame_success_le
    (inner : Game QA QB A B) (outer : PredicateGame OA OB X Y)
    (r : IncidenceExtraction.LocalSimulation (predicateGame inner) outer)
    (s : PredicateStrategies OA OB X Y) :
    (reconstructedGame inner outer r).success (strategyPair s) ≤
      inner.success (strategyPair (r.induced s)) := by
  classical
  unfold Game.success
  change (inner.questions.pushforward fun questions =>
      (r.questionA questions.1, r.questionB questions.2)).probability _ ≤ _
  rw [FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro questions hwin
  have houter : s.wins outer (r.questionA questions.1) (r.questionB questions.2) := by
    exact of_decide_eq_true hwin
  exact r.induced_wins s questions.1 questions.2 houter

/-- Specialization to the actual parallel game. Its strategy receives each
entire question tuple, preserving cross-coordinate local dependence. -/
theorem reconstructed_repetition_success_le
    (G : Game QA QB A B) (n : Nat) (outer : PredicateGame OA OB X Y)
    (r : IncidenceExtraction.LocalSimulation (predicateGame (G.repetition n)) outer)
    (s : PredicateStrategies OA OB X Y) :
    (reconstructedGame (G.repetition n) outer r).success (strategyPair s) ≤
      (G.repetition n).success (strategyPair (r.induced s)) :=
  reconstructedGame_success_le (G.repetition n) outer r s

end Simulation

/-! ## The actual named projection predicate -/

namespace ActualProjection

open IncidenceExtraction

abbrev FirstAnswer (P : Type) := Bool × (P → Triple)
abbrev SecondAnswer (P : Type) := Bool × (P → Triple) × (P → Bool)

/-- Ambient coordinate form of the actual retained-coordinate projection. -/
def project {P : Type} (single : P → Bool) (indices : P → Fin 3)
    (answer : FirstAnswer P) : SecondAnswer P :=
  (answer.1, ZeroInformation.projectFull single answer.2,
    ZeroInformation.projectSingles single indices answer.2)

/-- A verifier using only the two displayed questions. The retained indices are
verifier witnesses compatible with the displayed names, never player inputs.
The output equality is the actual projection on all ambient coordinates. -/
def accepts {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P) : Prop :=
  (∀ j, xorTriple (answerA.2 j) = (g.rhs (qa.question j) && answerA.1)) ∧
  answerA.1 = true ∧ ∃ indices : P → Fin 3,
    qb.question = ZeroInformation.partnerQuestion single qa.question
      (fun j => g.name (qa.question j) (indices j)) ∧
    answerB = project single indices answerA

def predicateGame {P R O N : Type} (g : Incidence O N) (single : P → Bool) :
    IncidenceExtraction.Game
      (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (FirstAnswer P) (SecondAnswer P) :=
  ⟨accepts g single⟩

/-- Points satisfying (6.17) satisfy this named verifier: validity comes from
the actual first-question equation subspace and agreement from the actual
`partnerProjection` map. -/
theorem actual_partnerProjection_accepts
    {P R O N : Type} (g : Incidence O N) (positions : List P)
    (single : P → Bool) (zeta0 : ZeroInformation.Bits R)
    (zeta1 zeta2 omega : P → ZeroInformation.Bits R)
    (occurrences : P → O) (indices : P → Fin 3)
    (point : ZeroInformation.FirstPoint g.rhs occurrences)
    (hone : point.val.1 = true) :
    accepts g single
      (ZeroInformation.firstInput positions single zeta0 zeta1 zeta2 omega
        occurrences indices)
      (ZeroInformation.secondInput positions single zeta0 zeta1 zeta2 omega
        occurrences (fun j => g.name (occurrences j) (indices j)))
      point.val
      (ZeroInformation.partnerProjection single g.rhs occurrences
        (fun j => g.name (occurrences j) (indices j)) indices point).val := by
  exact ⟨point.property, hone, indices, rfl, rfl⟩

/-- At a single coordinate, actual projection acceptance supplies an accepted
named-incidence answer with no access to the retained index. -/
theorem accepts_implies_named_incidence
    {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P)
    (h : accepts g single qa qb answerA answerB)
    (j : P) (hj : single j = true) (name : N)
    (hname : qb.question j = Sum.inr name) :
    g.namedAccepts (qa.question j) name (answerA.2 j) (answerB.2.2 j) := by
  obtain ⟨hvalid, hone, indices, hquestions, hproject⟩ := h
  refine ⟨indices j, ?_, ?_, ?_⟩
  · have hq := congrFun hquestions j
    simp [ZeroInformation.partnerQuestion, hj, hname] at hq
    exact hq.symm
  · simpa [hone] using hvalid j
  · subst answerB
    simp [project, ZeroInformation.projectSingles, hj]

end ActualProjection

end
end UniqueGamesTheorem.Soundness.RepeatedGameBounds

end

end OAI
