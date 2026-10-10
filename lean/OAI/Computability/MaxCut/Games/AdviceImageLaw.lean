import Mathlib
import OAI.Computability.MaxCut.Games.Basic
import OAI.Computability.MaxCut.Games.RawPrivateTable

namespace OAI

noncomputable section

/-!
# The exact visible-advice law for a fixed latent map

For every fixed binary-linear map `A`, including rank-deficient maps, a uniform
latent column has a uniform image in `range A`.  An explicit range/kernel
bijection proves the assertion simultaneously for every intercept and slope.
The final theorem starts with the actual pair of independently uniform linear
maps on the partner answer space and pushes it to independent uniform visible
coefficients in `W × range A`.  No full-rank or independence premise is assumed.
-/

namespace MaxCutGames.Clean.AdviceImageLaw

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Soundness.ConditionalIncidences
open MaxCutGames.Soundness.PartnerMapCoordinates
open MaxCutGames.Foundations.Games

attribute [local instance] Classical.propDecidable

variable {K S W : Type} [AddCommGroup K] [Module F2 K]
  [AddCommGroup S] [Module F2 S]

def rangePoint (A : K →ₗ[F2] S) (m : K) : A.range :=
  ⟨A m, ⟨m, rfl⟩⟩

def selectedLift (A : K →ₗ[F2] S) (z : A.range) : K :=
  Classical.choose z.property

theorem selectedLift_spec (A : K →ₗ[F2] S) (z : A.range) :
    A (selectedLift A z) = (z : S) :=
  Classical.choose_spec z.property

theorem rangePoint_lift_add_kernel (A : K →ₗ[F2] S) (z : A.range) (k : A.ker) :
    rangePoint A (selectedLift A z + (k : K)) = z := by
  apply Subtype.ext
  change A (selectedLift A z + (k : K)) = (z : S)
  rw [map_add, selectedLift_spec, k.property, add_zero]

/-- Every range fibre is one translate of the same kernel. -/
def imageKernelEquiv (A : K →ₗ[F2] S) : K ≃ A.range × A.ker where
  toFun m := (rangePoint A m,
    ⟨m - selectedLift A (rangePoint A m), by
      change A (m - selectedLift A (rangePoint A m)) = 0
      rw [map_sub, selectedLift_spec]
      exact sub_self _⟩)
  invFun p := selectedLift A p.1 + (p.2 : K)
  left_inv m := by
    change selectedLift A (rangePoint A m) + (m - selectedLift A (rangePoint A m)) = m
    rw [add_comm, sub_add_cancel]
  right_inv p := by
    apply Prod.ext
    · exact rangePoint_lift_add_kernel A p.1 p.2
    · apply Subtype.ext
      change selectedLift A p.1 + (p.2 : K) -
        selectedLift A (rangePoint A (selectedLift A p.1 + (p.2 : K))) = (p.2 : K)
      rw [rangePoint_lift_add_kernel]
      exact add_sub_cancel_left _ _

def columnImage (A : K →ₗ[F2] S) (column : W × K) : W × A.range :=
  (column.1, rangePoint A column.2)

def columnSplitEquiv (A : K →ₗ[F2] S) : (W × K) ≃ (W × A.range) × A.ker :=
  (Equiv.prodCongr (Equiv.refl W) (imageKernelEquiv A)).trans
    (Equiv.prodAssoc W A.range A.ker).symm

def visibleCoefficients {I : Type} (A : K →ₗ[F2] S)
    (columns : I → W × K) : I → W × A.range :=
  fun i => columnImage A (columns i)

def coefficientsSplitEquiv (I : Type) (A : K →ₗ[F2] S) :
    (I → W × K) ≃ (I → W × A.range) × (I → A.ker) :=
  (Equiv.piCongrRight fun _ : I => columnSplitEquiv (W := W) A).trans
    (Equiv.arrowProdEquivProdArrow I (fun _ => W × A.range) (fun _ => A.ker))

instance rangeFintype [Fintype S] (A : K →ₗ[F2] S) : Fintype A.range :=
  Fintype.ofFinite _

instance kernelFintype [Fintype K] (A : K →ₗ[F2] S) : Fintype A.ker :=
  Fintype.ofFinite _

/-- Exact pushforward law for all columns jointly, including the original
intercept. This implies every event identity, not just individual marginals. -/
theorem uniform_visible_coefficients {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (F : (I → W × A.range) → ℝ) :
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
      𝔼 visible : I → W × A.range, F visible := by
  calc
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
        𝔼 pieces : (I → W × A.range) × (I → A.ker), F pieces.1 :=
      Fintype.expect_equiv (coefficientsSplitEquiv I A) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (I → W × A.range))
          (Finset.univ : Finset (I → A.ker)) (fun pieces => F pieces.1))

/-- The full product law exposes mutual independence of every raw coefficient. -/
theorem uniform_coordinate_product {I E : Type} [Fintype I] [DecidableEq I] [Fintype E]
    (f : I → E → ℝ) :
    (𝔼 columns : I → E, ∏ i, f i (columns i)) = ∏ i, 𝔼 e : E, f i e := by
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_pi, Nat.cast_prod]
  exact (Finset.prod_div_distrib _ _).symm

theorem visible_coefficient_product {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (f : I → W × A.range → ℝ) :
    (𝔼 columns : I → W × K, ∏ i, f i (columnImage A (columns i))) =
      ∏ i, 𝔼 e : W × A.range, f i e := by
  exact (uniform_visible_coefficients A (fun visible => ∏ i, f i (visible i))).trans
    (uniform_coordinate_product f)

theorem uniform_pushforward_of_expect {Ω Γ : Type} [Fintype Ω] [Fintype Γ]
    [Nonempty Ω] [Nonempty Γ] (f : Ω → Γ)
    (h : ∀ F : Γ → ℝ, (𝔼 x : Ω, F (f x)) = 𝔼 y : Γ, F y) :
    (FiniteDistribution.uniform Ω).pushforward f = FiniteDistribution.uniform Γ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  have he : (FiniteDistribution.uniform Ω).expectation
        (fun x => if f x = y then 1 else 0) =
      (FiniteDistribution.uniform Γ).expectation (fun z => if z = y then 1 else 0) := by
    simpa only [FiniteDistribution.expectation_uniform,
      ← Fintype.expect_eq_sum_div_card] using h (fun z => if z = y then 1 else 0)
  calc
    _ = (FiniteDistribution.uniform Ω).expectation
        (fun x => if f x = y then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
    _ = _ := he
    _ = _ := by simp [FiniteDistribution.expectation, mul_ite]

theorem visible_coefficients_pushforward {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Nonempty W] [Fintype K] [Fintype S] (A : K →ₗ[F2] S) :
    (FiniteDistribution.uniform (I → W × K)).pushforward (visibleCoefficients A) =
      FiniteDistribution.uniform (I → W × A.range) :=
  uniform_pushforward_of_expect (visibleCoefficients A) (uniform_visible_coefficients A)

/-- The worst-case codomain cardinality suffices; no rank estimate is needed. -/
theorem visible_card_le [Fintype W] [Fintype K] [Fintype S] (A : K →ₗ[F2] S) :
    Fintype.card (W × A.range) ≤ Fintype.card W * Fintype.card S := by
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul_left _
    (Fintype.card_le_of_injective (fun z : A.range => (z : S)) Subtype.val_injective)

theorem visible_card_binary_le [Fintype K] (w r : Nat)
    (A : K →ₗ[F2] (Fin r → F2)) :
    Fintype.card ((Fin w → F2) × A.range) ≤ 2 ^ (w + r) := by
  calc
    Fintype.card ((Fin w → F2) × A.range) ≤
        Fintype.card (Fin w → F2) * Fintype.card (Fin r → F2) :=
      visible_card_le A
    _ = 2 ^ (w + r) := by simp [F2, pow_add]

variable {P : Type} [Fintype P] [DecidableEq P]
  [AddCommGroup W] [Module F2 W]
  (rhs : P → Bool) (J : Finset P)

abbrev PartnerSpace := MaxCutGames.Soundness.PartnerProjection.PartnerPoint rhs (activeOf J)

/-- Raw coefficients commute with actual linear-map composition. -/
theorem coefficients_comp (A : K →ₗ[F2] S) (M : PartnerSpace rhs J →ₗ[F2] K) :
    coefficients rhs J S (A.comp M) = fun i => A (coefficients rhs J K M i) := by
  funext i
  simp [coefficients, mapEquiv, LinearMap.comp_apply]

def actualVisibleCoefficients (A : K →ₗ[F2] S)
    (maps : (PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K)) :
    RawSlot J → W × A.range :=
  fun i => (coefficients rhs J W maps.1 i, rangePoint A (coefficients rhs J K maps.2 i))

/-- The displayed second component is precisely the coefficient of `S = A M`. -/
theorem actualVisibleCoefficients_second (A : K →ₗ[F2] S)
    (T : PartnerSpace rhs J →ₗ[F2] W) (M : PartnerSpace rhs J →ₗ[F2] K)
    (i : RawSlot J) :
    ((actualVisibleCoefficients rhs J A (T, M) i).2 : S) =
      coefficients rhs J S (A.comp M) i := by
  rw [coefficients_comp]
  rfl

def actualMapPairEquiv :
    ((PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K)) ≃
      (RawSlot J → W × K) :=
  (Equiv.prodCongr (mapEquiv rhs J W).symm.toEquiv (mapEquiv rhs J K).symm.toEquiv).trans
    (Equiv.arrowProdEquivProdArrow (RawSlot J) (fun _ => W) (fun _ => K)).symm

/-- Sampling the actual independent maps `T` and `M` yields the claimed joint
uniform coefficient law of `(T,A M)`, for every fixed equation tuple and mask. -/
theorem actual_maps_visible_uniform [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (F : (RawSlot J → W × A.range) → ℝ) :
    (𝔼 maps : (PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K),
        F (actualVisibleCoefficients rhs J A maps)) =
      𝔼 gamma : RawSlot J → W × A.range, F gamma := by
  calc
    (𝔼 maps : (PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K),
        F (actualVisibleCoefficients rhs J A maps)) =
        𝔼 columns : RawSlot J → W × K, F (visibleCoefficients A columns) :=
      Fintype.expect_equiv (actualMapPairEquiv rhs J) _ _ (fun _ => rfl)
    _ = _ := uniform_visible_coefficients A F

theorem actual_maps_visible_product [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (f : RawSlot J → W × A.range → ℝ) :
    (𝔼 maps : (PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K),
        ∏ i, f i (actualVisibleCoefficients rhs J A maps i)) =
      ∏ i, 𝔼 e : W × A.range, f i e := by
  exact (actual_maps_visible_uniform rhs J A (fun gamma => ∏ i, f i (gamma i))).trans
    (uniform_coordinate_product f)

theorem actual_maps_visible_pushforward [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) :
    (FiniteDistribution.uniform
        ((PartnerSpace rhs J →ₗ[F2] W) × (PartnerSpace rhs J →ₗ[F2] K))).pushforward
        (actualVisibleCoefficients rhs J A) =
      FiniteDistribution.uniform (RawSlot J → W × A.range) :=
  uniform_pushforward_of_expect (actualVisibleCoefficients rhs J A)
    (actual_maps_visible_uniform rhs J A)

end MaxCutGames.Clean.AdviceImageLaw

/-!
# Concrete finite averaging for the projection upper bound

The coefficient samples here are actual functions `Fin t → (Fin m → ZMod 2)`.
Their law is the normalized finite uniform sum over all such functions. The
binomial moment formula is proved from this sum, without an independence or
binomial-distribution premise.
-/

namespace MaxCutGames.Soundness.RepeatedGameBounds

open scoped BigOperators

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

end MaxCutGames.Soundness.RepeatedGameBounds

/-! Conversion of actual binary linear points to the named projection answers. -/

namespace MaxCutGames.Soundness.ActualPointAnswers
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

attribute [local instance] Classical.propDecidable

variable {k : Nat}

def sourceTau : ActualHomogeneous.E k →ₗ[F2] F2 := LinearMap.fst F2 F2 _
def partnerTau (J : Finset (Fin k)) : RawPoint J →ₗ[F2] F2 := LinearMap.proj none

theorem tau_projection (rhs : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) : (partnerTau J).comp (rawProjection rhs J slot) = sourceTau := by
  apply LinearMap.ext
  intro x
  change ofBit (toBit x.1) = x.1
  exact ofBit_toBit _

def firstAnswer (rhs : Fin k → Bool) (x : ActualHomogeneous.E k) :
    ActualProjection.FirstAnswer (Fin k) :=
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  (p.homogeneous, fun j => ConcreteExtraction.tripleCoordinates (p.coordinates j))

def secondAnswer (rhs : Fin k → Bool) (J : Finset (Fin k)) (v : RawPoint J) :
    ActualProjection.SecondAnswer (Fin k) :=
  let y := (pointEquiv rhs J).symm v
  (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single)

private theorem triple_eq_of_first_second_parity_inline_ActualPointAnswers (a b : PartnerProjection.Triple)
    (h₁ : a.first = b.first) (h₂ : a.second = b.second) (hp : parity a = parity b) : a = b := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  dsimp only at h₁ h₂
  subst b₁
  subst b₂
  simp only [parity] at hp
  have h₃ := congrArg (fun z => (a₁ ^^ a₂) ^^ z) hp
  have cancel (c d : Bool) : (c ^^ (c ^^ d)) = d := by
    cases c <;> cases d <;> rfl
  simp only [cancel] at h₃
  cases h₃
  rfl

/-- Inactive occurrences determine every full triple. The active right-hand
sides never enter the partner answer. -/
theorem secondAnswer_projection (rhs rhs' : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (x : ActualHomogeneous.E k)
    (hout : ∀ j, j ∉ J → rhs' j = rhs j) :
    secondAnswer rhs' J (rawProjection rhs J slot x) =
      ActualProjection.project (activeOf J) (fun j => ConcreteExtraction.slotIndex (slot j))
        (firstAnswer rhs x) := by
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  let y := (pointEquiv rhs' J).symm (rawProjection rhs J slot x)
  let z := PartnerLinear.projection rhs (activeOf J) slot p
  have hr : pointEquiv rhs' J y = pointEquiv rhs J z :=
    (pointEquiv rhs' J).apply_symm_apply _
  have hh : y.homogeneous = z.homogeneous := by
    have h := congrArg toBit (congrFun hr none)
    simpa only [pointEquiv_none, toBit_ofBit] using h
  have hfull : y.full = z.full := by
    funext j
    by_cases hj : j ∈ J
    · rw [y.full_zero j (by simp [activeOf, hj]), z.full_zero j (by simp [activeOf, hj])]
    · have h₁ : (y.full j).first = (z.full j).first := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(0:Fin 2)))))
        simpa only [pointEquiv_full_first, toBit_ofBit] using h
      have h₂ : (y.full j).second = (z.full j).second := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(1:Fin 2)))))
        simpa only [pointEquiv_full_second, toBit_ofBit] using h
      have hp : parity (y.full j) = parity (z.full j) := by
        rw [y.full_valid j (by simp [activeOf, hj]),
          z.full_valid j (by simp [activeOf, hj]), hout j hj, hh]
      exact triple_eq_of_first_second_parity_inline_ActualPointAnswers _ _ h₁ h₂ hp
  have hsingle : y.single = z.single := by
    funext j
    by_cases hj : j ∈ J
    · have h := congrArg toBit (congrFun hr (some (.inr ⟨j,hj⟩)))
      simpa only [pointEquiv_single, toBit_ofBit] using h
    · rw [y.single_zero j (by simp [activeOf, hj]), z.single_zero j (by simp [activeOf, hj])]
  change (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single) = _
  rw [hh, hfull, hsingle]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j i
      change ConcreteExtraction.tripleCoordinates
          (if decide (j ∈ J) then zeroTriple else p.coordinates j) i =
        (if decide (j ∈ J) then false else ConcreteExtraction.tripleCoordinates (p.coordinates j) i)
      cases h : decide (j ∈ J) <;> simp [ConcreteExtraction.tripleCoordinates, zeroTriple]
    · funext j
      change (if decide (j ∈ J) then retained (slot j) (p.coordinates j) else false) =
        (if decide (j ∈ J) then ConcreteExtraction.tripleCoordinates (p.coordinates j)
          (ConcreteExtraction.slotIndex (slot j)) else false)
      rw [ConcreteExtraction.retained_coordinates]

def displayedRhs {Id Name : Type} (rhs : Id → Bool) (question : Fin k → Sum Id Name) :
    Fin k → Bool := fun j => match question j with
  | .inl o => rhs o
  | .inr _ => false

theorem displayedRhs_full {Id Name : Type} (rhs : Id → Bool)
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    displayedRhs rhs (RawPrivateTable.displayed J names occ slot) j = rhs (occ j) := by
  simp [displayedRhs, RawPrivateTable.displayed, hj]

/-- Actual point equality gives acceptance in the named verifier on complete
private inputs, with local answer conversions. -/
theorem actual_accepts {Q Id Name : Type} (J : Finset (Fin k))
    (g : IncidenceExtraction.Incidence Id Name)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name)
    (slot : Fin k → Slot)
    (hquestion : qb.question = RawPrivateTable.displayed J g.name qa.question slot)
    (x : ActualHomogeneous.E k) (v : RawPoint J)
    (hone : sourceTau x = 1)
    (hprojection : rawProjection (fun j => g.rhs (qa.question j)) J slot x = v) :
    ActualProjection.accepts g (activeOf J) qa qb
      (firstAnswer (fun j => g.rhs (qa.question j)) x)
      (secondAnswer (displayedRhs g.rhs qb.question) J v) := by
  let p := (PartnerLinear.sourceLinearEquiv (fun j => g.rhs (qa.question j))).symm x
  have hp : p.homogeneous = true := by
    change toBit x.1 = true
    change x.1 = 1 at hone
    rw [hone]
    decide
  refine ⟨?_, hp, (fun j => ConcreteExtraction.slotIndex (slot j)), ?_, ?_⟩
  · intro j
    exact (ConcreteExtraction.parity_coordinates _).trans (p.valid j)
  · rw [hquestion]
    funext j
    by_cases hj : j ∈ J <;>
      simp [RawPrivateTable.displayed, ZeroInformation.partnerQuestion, activeOf, hj]
  · rw [← hprojection]
    exact secondAnswer_projection _ _ J slot x (fun j hj => by
      rw [hquestion]
      exact displayedRhs_full g.rhs J g.name qa.question slot j hj)

end MaxCutGames.Soundness.ActualPointAnswers

end

end OAI
