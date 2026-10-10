import Mathlib
import OAI.Computability.DirectedFeedback.Games.Explicit
import OAI.Computability.DirectedFeedback.Games.ActualAdviceStochasticBridge

namespace OAI

section
section
section
section
section
section
section

section

namespace DFVSGames.Decoder.AdviceLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Soundness
open ConditionalIncidences RawPartnerTarget RawMapLaw
open DFVSGames.Foundations.Games
open DFVSGames.Clean

noncomputable section
attribute [local instance] Classical.propDecidable

section VisibleMap

variable {k : ℕ} {K W R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup W] [Module F2 W] [Fintype W]
  [AddCommGroup R] [Module F2 R] [Fintype R]

def visibleMap (A : K →ₗ[F2] R) {J : Finset (Fin k)}
    (T : RawPoint J →ₗ[F2] W) (M : RawPoint J →ₗ[F2] K) :
    RawPoint J →ₗ[F2] (W × A.range) :=
  T.prod (A.rangeRestrict.comp M)

omit [Fintype K] [Fintype W] [Fintype R] in
theorem visibleMap_apply (A : K →ₗ[F2] R) {J : Finset (Fin k)}
    (T : RawPoint J →ₗ[F2] W) (M : RawPoint J →ₗ[F2] K) (x : RawPoint J) :
    visibleMap A T M x = (T x, AdviceImageLaw.rangePoint A (M x)) := rfl

def rawMapPairCoefficientsEquiv (J : Finset (Fin k)) :
    ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) ≃
      (RawSlot J → W × K) :=
  (Equiv.prodCongr (rawMapEquiv J W).symm (rawMapEquiv J K).symm).trans
    (Equiv.arrowProdEquivProdArrow (RawSlot J) (fun _ => W) (fun _ => K)).symm

omit [Fintype K] [Fintype W] [Fintype R] in
theorem visibleMap_raw (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (TM : (RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) :
    visibleMap A TM.1 TM.2 = rawMap J (W × A.range)
      (AdviceImageLaw.visibleCoefficients A (rawMapPairCoefficientsEquiv J TM)) := by
  exact (rawMap_coefficients J (W × A.range) (visibleMap A TM.1 TM.2)).symm

theorem uniform_visible_maps (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] (W × A.range)) → ℝ) :
    (𝔼 TM : (RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K),
      H (visibleMap A TM.1 TM.2)) =
      𝔼 Y : RawPoint J →ₗ[F2] (W × A.range), H Y := by
  calc
    _ = 𝔼 columns : RawSlot J → W × K,
        H (rawMap J (W × A.range) (AdviceImageLaw.visibleCoefficients A columns)) := by
      apply Fintype.expect_equiv (rawMapPairCoefficientsEquiv J)
      intro TM
      rw [visibleMap_raw]
    _ = 𝔼 gamma : RawSlot J → W × A.range, H (rawMap J (W × A.range) gamma) :=
      AdviceImageLaw.uniform_visible_coefficients (I := RawSlot J) (W := W) A
        (fun gamma : RawSlot J → W × A.range => H (rawMap J (W × A.range) gamma))
    _ = _ := PaddedLaw.uniform_rawMaps J H

theorem uniform_visible_maps_expectation (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] (W × A.range)) → ℝ) :
    (FiniteDistribution.uniform
      ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K))).expectation
        (fun TM => H (visibleMap A TM.1 TM.2)) =
      (FiniteDistribution.uniform (RawPoint J →ₗ[F2] (W × A.range))).expectation H := by
  simpa only [FiniteDistribution.expectation_uniform,
    ← Fintype.expect_eq_sum_div_card] using uniform_visible_maps A J H

variable {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def actualSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] W) ×
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] K))).expectation fun TM =>
      ActualAdviceStochasticBridge.fixedMapSuccess μ g policy
        (NativeExperiment.maskSet mask) (visibleMap A TM.1 TM.2)

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualSuccess_eq_cleanSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    actualSuccess μ g A policy β hβ₀ hβ₁ =
      ActualAdviceStochasticBridge.success μ g policy β hβ₀ hβ₁ := by
  unfold actualSuccess ActualAdviceStochasticBridge.success
  apply FiniteDistribution.expectation_congr
  intro mask
  exact uniform_visible_maps_expectation A (NativeExperiment.maskSet mask)
    (ActualAdviceStochasticBridge.fixedMapSuccess μ g policy (NativeExperiment.maskSet mask))

end VisibleMap

section WholeTable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
  [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def drawDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution ((Fin k → PaddedLaw.BlockDraw V) × V) where
  weight := PaddedLaw.drawWeights β k
  nonnegative dz := mul_nonneg
    ((SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).1 dz.1)
    (SparseLaw.uniformWeights_pos dz.2).le
  normalized := by
    rw [Fintype.sum_prod_type]
    simp only [PaddedLaw.drawWeights, ← Finset.mul_sum,
      (SparseLaw.uniformWeights_isProbability (α := V)).2, mul_one]
    exact (SparseLaw.independentWeights_isProbability _
      (PaddedLaw.blockWeights_isProbability β hβ hβ') k).2

def paddedDistribution (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ActualHomogeneous.E k →ₗ[F2] V) :=
  (drawDistribution β hβ hβ').pushforward (fun dz => PaddedLaw.paddedMap rhs dz.1 dz.2)

theorem paddedDistribution_totalVariation_eq_slope (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (paddedDistribution (V := V) rhs β hβ hβ').totalVariation
      (FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V)) =
        DFVSGames.Foundations.Information.totalVariation
          (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
          (SparseLaw.uniformWeights (Fin k → V × V)) := by
  exact PaddedLaw.paddedMapWeights_totalVariation_eq_slope rhs β

theorem paddedDistribution_totalVariation (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (paddedDistribution (V := V) rhs β hβ hβ').totalVariation
      (FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V)) ≤
        Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  exact PaddedLaw.paddedMapWeights_totalVariation rhs β hβ hβ'

end WholeTable

section CommonLaw

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

def withKernel (μ : FiniteDistribution Ω) (p : Ω → FiniteDistribution Y) :
    FiniteDistribution (Ω × Y) where
  weight xy := μ.weight xy.1 * (p xy.1).weight xy.2
  nonnegative xy := mul_nonneg (μ.nonnegative _) ((p _).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact μ.normalized

theorem withKernel_totalVariation (μ : FiniteDistribution Ω)
    (p q : Ω → FiniteDistribution Y) :
    (withKernel μ p).totalVariation (withKernel μ q) =
      ∑ x, μ.weight x * (p x).totalVariation (q x) := by
  unfold FiniteDistribution.totalVariation withKernel
  rw [Fintype.sum_prod_type]
  have inner (x : Ω) :
      (∑ y, |μ.weight x * (p x).weight y - μ.weight x * (q x).weight y|) =
        μ.weight x * ∑ y, |(p x).weight y - (q x).weight y| := by
    simp only [← mul_sub, abs_mul, abs_of_nonneg (μ.nonnegative x), ← Finset.mul_sum]
  simp_rw [inner]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem withKernel_totalVariation_le (μ : FiniteDistribution Ω)
    (p q : Ω → FiniteDistribution Y) (η : ℝ)
    (h : ∀ x, (p x).totalVariation (q x) ≤ η) :
    (withKernel μ p).totalVariation (withKernel μ q) ≤ η := by
  rw [withKernel_totalVariation]
  calc
    _ ≤ ∑ x, μ.weight x * η := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)
    _ = η := by rw [← Finset.sum_mul, μ.normalized, one_mul]

end CommonLaw

theorem wholeAdvice_totalVariation {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (withKernel (occurrences.product publicLaw)
      (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ')).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) ≤
      Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  apply withKernel_totalVariation_le
  intro ua
  exact paddedDistribution_totalVariation (fun j => rhs (ua.1 j)) β hβ hβ'

theorem wholeAdvice_totalVariation_eq_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (withKernel (occurrences.product publicLaw)
      (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ')).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) =
      DFVSGames.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) := by
  rw [withKernel_totalVariation]
  simp_rw [paddedDistribution_totalVariation_eq_slope]
  rw [← Finset.sum_mul, (occurrences.product publicLaw).normalized, one_mul]

theorem wholeAdvice_totalVariation_le_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (withKernel (occurrences.product publicLaw)
      (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ')).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) ≤
      DFVSGames.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) :=
  (wholeAdvice_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ').le

section HiddenRows

variable {k : ℕ} {K R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup R] [Module F2 R] [Fintype R]

instance observedRowsFintype (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    Fintype (AdviceFibers.ObservedRow (E := RawPoint J) A) := Fintype.ofFinite _

theorem observed_hidden_independent (J : Finset (Fin k)) (A : K →ₗ[F2] R)
    (f : AdviceFibers.ObservedRow (E := RawPoint J) A → ℝ)
    (g : (RawPoint J →ₗ[F2] A.ker) → ℝ) :
    (𝔼 M : RawPoint J →ₗ[F2] K,
      f (AdviceFibers.observe A M) * g (AdviceFibers.hiddenCoordinate A M)) =
      (𝔼 S : AdviceFibers.ObservedRow (E := RawPoint J) A, f S) *
        (𝔼 N : RawPoint J →ₗ[F2] A.ker, g N) :=
  AdviceFibers.observed_hidden_independent A f g

end HiddenRows

section ProjectionSeeds

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]

abbrev ProjectionSeed (k : ℕ) (V : Type) [AddCommGroup V] [Module F2 V] :=
  Σ c : Fin k → PaddedLaw.ProjectionChoice,
    RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V

def projectionSeedDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (ProjectionSeed k V) where
  weight s := PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2
  nonnegative s := mul_nonneg
    ((PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').1 s.1)
    (SparseLaw.uniformWeights_pos s.2).le
  normalized := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (SparseLaw.uniformWeights_isProbability).2, mul_one]
    exact (PaddedLaw.choiceTupleWeight_isProbability β hβ hβ').2

def projectSeedMap (rhs : Fin k → Bool) (s : ProjectionSeed k V) :
    ActualHomogeneous.E k →ₗ[F2] V :=
  s.2.comp (rawProjection rhs (PaddedLaw.choiceMask s.1) (PaddedLaw.choiceSlots s.1))

variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

theorem projectionSeed_expectation (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (H : (ActualHomogeneous.E k →ₗ[F2] V) → ℝ) :
    (projectionSeedDistribution β hβ hβ').expectation (fun s => H (projectSeedMap rhs s)) =
      (paddedDistribution rhs β hβ hβ').expectation H := by
  rw [paddedDistribution, FiniteDistribution.expectation_pushforward]
  change (∑ s : ProjectionSeed k V,
      PaddedLaw.choiceTupleWeight β s.1 * SparseLaw.uniformWeights _ s.2 *
        H (projectSeedMap rhs s)) =
    ∑ dz, PaddedLaw.drawWeights β k dz * H (PaddedLaw.paddedMap rhs dz.1 dz.2)
  rw [PaddedLaw.actual_projection_mixture_expectation, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  calc
    _ = PaddedLaw.choiceTupleWeight β c *
        ∑ Y : RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V,
          SparseLaw.uniformWeights _ Y *
            H (Y.comp (rawProjection rhs (PaddedLaw.choiceMask c) (PaddedLaw.choiceSlots c))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      exact mul_assoc _ _ _
    _ = _ := by rw [PaddedLaw.sum_uniformWeights_mul]

theorem projectionSeed_pushforward (rhs : Fin k → Bool) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (projectionSeedDistribution β hβ hβ').pushforward (projectSeedMap (V := V) rhs) =
      paddedDistribution rhs β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro Y
  have h := projectionSeed_expectation rhs β hβ hβ' (fun X => if X = Y then 1 else 0)
  simpa [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite,
    PaddedLaw.pushforwardWeight] using h

end ProjectionSeeds

section ActualDraw

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

def seedToActualDraw (occ : Fin k → Id) (A : K →ₗ[F2] R)
    (s : ProjectionSeed k (K × W)) : AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask s.1
  occurrences := occ
  positions := PaddedLaw.choiceSlots s.1
  rowMap := A
  hiddenMatrix := (LinearMap.fst F2 K W).comp s.2
  complement := (LinearMap.snd F2 K W).comp s.2

theorem seed_projection (rhs : Id → F2) (occ : Fin k → Id) (A : K →ₗ[F2] R)
    (s : ProjectionSeed k (K × W)) :
    AdviceExperiment.projection rhs (seedToActualDraw occ A s) =
      rawProjection (fun j => toBit (rhs (occ j)))
        (PaddedLaw.choiceMask s.1) (PaddedLaw.choiceSlots s.1) := rfl

theorem seed_padded_pair (rhs : Id → F2) (occ : Fin k → Id) (A : K →ₗ[F2] R)
    (s : ProjectionSeed k (K × W)) :
    (AdviceExperiment.paddedMatrix rhs (seedToActualDraw occ A s)).prod
      (AdviceExperiment.paddedComplement rhs (seedToActualDraw occ A s)) =
        projectSeedMap (fun j => toBit (rhs (occ j))) s := by
  ext x <;> rfl

theorem seed_left_observation (rhs : Id → F2) (occ : Fin k → Id) (A : K →ₗ[F2] R)
    (s : ProjectionSeed k (K × W)) :
    AdviceExperiment.leftObservation rhs (seedToActualDraw occ A s) = {
      occurrences := occ, rowMap := A,
      complement := (LinearMap.snd F2 K W).comp
        (projectSeedMap (fun j => toBit (rhs (occ j))) s),
      rows := A.comp ((LinearMap.fst F2 K W).comp
        (projectSeedMap (fun j => toBit (rhs (occ j))) s)) } := rfl

theorem seed_right_observation {Name : Type} (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (A : K →ₗ[F2] R) (s : ProjectionSeed k (K × W)) :
    AdviceExperiment.rightObservation names (seedToActualDraw occ A s) =
      ⟨PaddedLaw.choiceMask s.1, {
        question := RawPrivateTable.supported (PaddedLaw.choiceMask s.1) names occ
          (PaddedLaw.choiceSlots s.1), rowMap := A,
        complement := (LinearMap.snd F2 K W).comp s.2,
        rows := A.comp ((LinearMap.fst F2 K W).comp s.2) }⟩ := rfl

end ActualDraw

section MaskSlots

def choiceDistribution (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution PaddedLaw.ProjectionChoice where
  weight := PaddedLaw.choiceWeight β
  nonnegative := (PaddedLaw.choiceWeight_isProbability β hβ hβ').1
  normalized := (PaddedLaw.choiceWeight_isProbability β hβ hβ').2

def maskSlotChoice (p : Bool × Fin 3) : PaddedLaw.ProjectionChoice :=
  if p.1 then some p.2 else none

theorem maskSlotChoice_pushforward (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((Clean.bernoulli β hβ hβ').product (FiniteDistribution.uniform (Fin 3))).pushforward
      maskSlotChoice = choiceDistribution β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.uniform, Clean.bernoulli, choiceDistribution]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases c <;> simp [maskSlotChoice, PaddedLaw.choiceWeight, div_eq_mul_inv] ; ring

def choicesOfMaskSlots {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    Fin k → PaddedLaw.ProjectionChoice :=
  fun j => maskSlotChoice (mask j, slots j)

theorem choices_expectation {k : ℕ} (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (H : (Fin k → PaddedLaw.ProjectionChoice) → ℝ) :
    ((choiceDistribution β hβ hβ').iid k).expectation H =
      ((Clean.bernoulli β hβ hβ').iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
          H (choicesOfMaskSlots mask slots))) := by
  rw [← maskSlotChoice_pushforward, FiniteDistribution.iid_pushforward,
    FiniteDistribution.expectation_pushforward, NativeExperiment.expectation_iid_product,
    FiniteDistribution.iid_uniform]
  rfl

theorem choices_mask {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    PaddedLaw.choiceMask (choicesOfMaskSlots mask slots) =
      NativeExperiment.maskSet mask := by
  ext j
  cases h : mask j <;>
    simp [PaddedLaw.choiceMask, NativeExperiment.maskSet, choicesOfMaskSlots,
      maskSlotChoice, h]

theorem choices_active_slot {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3)
    (j : Fin k) (hj : mask j = true) :
    PaddedLaw.choiceSlots (choicesOfMaskSlots mask slots) j = PaddedLaw.decodeSlot (slots j) := by
  simp [PaddedLaw.choiceSlots, PaddedLaw.choiceSlot, choicesOfMaskSlots, maskSlotChoice, hj]

theorem projectionSeed_mask_slots_expectation {k : ℕ} {V : Type}
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (H : ProjectionSeed k V → ℝ) :
    (projectionSeedDistribution β hβ hβ').expectation H =
      ((Clean.bernoulli β hβ hβ').iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
          (FiniteDistribution.uniform
            (RawPoint (PaddedLaw.choiceMask (choicesOfMaskSlots mask slots)) →ₗ[F2] V)).expectation
              (fun Y => H ⟨choicesOfMaskSlots mask slots, Y⟩))) := by
  calc
    _ = ((choiceDistribution β hβ hβ').iid k).expectation (fun c =>
        (FiniteDistribution.uniform (RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V)).expectation
          (fun Y => H ⟨c, Y⟩)) := by
      unfold FiniteDistribution.expectation
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro c _
      change (∑ Y, PaddedLaw.choiceTupleWeight β c * SparseLaw.uniformWeights _ Y * H ⟨c, Y⟩) =
        PaddedLaw.choiceTupleWeight β c * ∑ Y, SparseLaw.uniformWeights _ Y * H ⟨c, Y⟩
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      exact mul_assoc _ _ _
    _ = _ := choices_expectation β hβ hβ' _

end MaskSlots

section FullSeedLaw

variable {Ω Z Y : Type*} [Fintype Ω] [Fintype Z] [Fintype Y]

theorem product_pushforward_withKernel (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution Z) (f : Ω → Z → Y) :
    (μ.product ν).pushforward (fun xz => (xz.1, f xz.1 xz.2)) =
      withKernel μ (fun x => ν.pushforward (f x)) := by
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product, withKernel]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : Ω, if x = a then μ.weight x *
        ∑ z, if f x z = b then ν.weight z else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a
      · subst x
        simp only [Prod.mk.injEq, true_and, ite_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp
      · simp [Prod.mk.injEq, hx]
    _ = _ := by simp

end FullSeedLaw

def fullSeedLaw {k : ℕ} {Id A V : Type} [Fintype Id] [Fintype A]
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :=
  (occurrences.product publicLaw).product (projectionSeedDistribution (k := k) (V := V) β hβ hβ')

def fullSeedPad {k : ℕ} {Id A V : Type} [AddCommGroup V] [Module F2 V]
    (rhs : Id → Bool) (s : ((Fin k → Id) × A) × ProjectionSeed k V) :
    ((Fin k → Id) × A) × (ActualHomogeneous.E k →ₗ[F2] V) :=
  (s.1, projectSeedMap (fun j => rhs (s.1.1 j)) s.2)

theorem fullSeed_pad_law {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward (fullSeedPad rhs) =
      withKernel (occurrences.product publicLaw)
        (fun ua => paddedDistribution (V := V) (fun j => rhs (ua.1 j)) β hβ hβ') := by
  unfold fullSeedLaw fullSeedPad
  rw [product_pushforward_withKernel (occurrences.product publicLaw)
    (projectionSeedDistribution (k := k) (V := V) β hβ hβ')
    (fun ua seed => projectSeedMap (fun j => rhs (ua.1 j)) seed)]
  congr 1
  funext ua
  exact projectionSeed_pushforward (fun j => rhs (ua.1 j)) β hβ hβ'

theorem fullSeed_totalVariation {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) ≤
      Real.sqrt ((1 + β ^ 2 * ((Fintype.card V : ℝ) - 1) / 3) ^ k - 1) / 2 := by
  rw [fullSeed_pad_law]
  exact wholeAdvice_totalVariation occurrences publicLaw rhs β hβ hβ'

theorem fullSeed_totalVariation_eq_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) =
      DFVSGames.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) := by
  rw [fullSeed_pad_law]
  exact wholeAdvice_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ'

theorem fullSeed_totalVariation_le_slope {k : ℕ} {Id A V : Type}
    [Fintype Id] [Fintype A] [AddCommGroup V] [Module F2 V] [Fintype V]
    [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]
    (occurrences : FiniteDistribution (Fin k → Id)) (publicLaw : FiniteDistribution A)
    (rhs : Id → Bool) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((fullSeedLaw (V := V) occurrences publicLaw β hβ hβ').pushforward
      (fullSeedPad rhs)).totalVariation
      (withKernel (occurrences.product publicLaw)
        (fun _ => FiniteDistribution.uniform (ActualHomogeneous.E k →ₗ[F2] V))) ≤
      DFVSGames.Foundations.Information.totalVariation
        (SparseLaw.independentWeights (SparseLaw.mixture β (SparseLaw.singletonPairWeights V)) k)
        (SparseLaw.uniformWeights (Fin k → V × V)) :=
  (fullSeed_totalVariation_eq_slope occurrences publicLaw rhs β hβ hβ').le

section CompleteData

variable {k : ℕ} {Id K W R : Type}
  [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
  [AddCommGroup R] [Module F2 R]

abbrev FullSeed (k : ℕ) (Id K W R : Type)
    [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
    [AddCommGroup R] [Module F2 R] :=
  ((Fin k → Id) × (K →ₗ[F2] R)) × ProjectionSeed k (K × W)

abbrev CompleteData (k : ℕ) (Id K W R : Type)
    [AddCommGroup K] [Module F2 K] [AddCommGroup W] [Module F2 W]
    [AddCommGroup R] [Module F2 R] :=
  Σ ua : (Fin k → Id) × (K →ₗ[F2] R),
    Σ c : Fin k → PaddedLaw.ProjectionChoice,
      (RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] W) ×
        AdviceFibers.ObservedRow (E := RawPoint (PaddedLaw.choiceMask c)) ua.2

abbrev PrivateMap (d : CompleteData k Id K W R) :=
  RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] d.1.2.ker

def targetObservationEquiv (J : Finset (Fin k)) (A : K →ₗ[F2] R) :
    (RawPoint J →ₗ[F2] (K × W)) ≃
      ((RawPoint J →ₗ[F2] W) × AdviceFibers.ObservedRow (E := RawPoint J) A) ×
        (RawPoint J →ₗ[F2] A.ker) :=
  (LinearMap.prodEquiv F2).toEquiv.symm |>.trans
    (Equiv.prodComm _ _) |>.trans
    (Equiv.prodCongr (Equiv.refl _) (AdviceFibers.observationEquiv A)) |>.trans
    (Equiv.prodAssoc _ _ _).symm

def fullSeedCoordinatesEquiv :
    FullSeed k Id K W R ≃ Σ d : CompleteData k Id K W R, PrivateMap d :=
  ((Equiv.sigmaEquivProd ((Fin k → Id) × (K →ₗ[F2] R))
      (ProjectionSeed k (K × W))).symm.trans
    (Equiv.sigmaCongrRight fun (ua : (Fin k → Id) × (K →ₗ[F2] R)) =>
      Equiv.sigmaCongrRight fun c => targetObservationEquiv (PaddedLaw.choiceMask c) ua.2)).trans
    { toFun := fun p => ⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩
      invFun := fun p => ⟨p.1.1, p.1.2.1, p.1.2.2, p.2⟩
      left_inv := fun p => by rcases p with ⟨ua, c, ⟨T, S⟩, N⟩; rfl
      right_inv := fun p => by rcases p with ⟨⟨ua, c, T, S⟩, N⟩; rfl }

def completeObserve (s : FullSeed k Id K W R) : CompleteData k Id K W R :=
  (fullSeedCoordinatesEquiv s).1

def completeAssemble (d : CompleteData k Id K W R) (N : PrivateMap d) :
    FullSeed k Id K W R :=
  fullSeedCoordinatesEquiv.symm ⟨d, N⟩

theorem completeObserve_eq (s : FullSeed k Id K W R) :
    completeObserve s = ⟨s.1, s.2.1,
      (LinearMap.snd F2 K W).comp s.2.2,
      AdviceFibers.observe s.1.2 ((LinearMap.fst F2 K W).comp s.2.2)⟩ := rfl

theorem completeAssemble_eq (d : CompleteData k Id K W R) (N : PrivateMap d) :
    completeAssemble d N = (d.1, ⟨d.2.1,
      (AdviceFibers.assemble d.1.2 (AdviceFibers.observedBase d.1.2 d.2.2.2) N).prod
        d.2.2.1⟩) := rfl

@[simp] theorem completeObserve_assemble (d : CompleteData k Id K W R)
    (N : PrivateMap d) : completeObserve (completeAssemble d N) = d :=
  congrArg Sigma.fst (fullSeedCoordinatesEquiv.apply_symm_apply ⟨d, N⟩)

def completeFiberEquiv (d : CompleteData k Id K W R) :
    PrivateMap d ≃ {s : FullSeed k Id K W R // completeObserve s = d} :=
  ((Equiv.subtypeEquiv fullSeedCoordinatesEquiv (fun _ => Iff.rfl)).trans
    (Equiv.sigmaSubtype d)).symm

@[simp] theorem completeFiberEquiv_val (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeFiberEquiv d N).val = completeAssemble d N := rfl

def completeDraw (d : CompleteData k Id K W R) (N : PrivateMap d) :
    AdviceExperiment.Draw k Id K W R where
  singletons := PaddedLaw.choiceMask d.2.1
  occurrences := d.1.1
  positions := PaddedLaw.choiceSlots d.2.1
  rowMap := d.1.2
  hiddenMatrix := AdviceFibers.assemble d.1.2 (AdviceFibers.observedBase d.1.2 d.2.2.2) N
  complement := d.2.2.1

theorem completeDraw_seed (d : CompleteData k Id K W R) (N : PrivateMap d) :
    seedToActualDraw (completeAssemble d N).1.1 (completeAssemble d N).1.2
      (completeAssemble d N).2 = completeDraw d N := rfl

theorem completeDraw_rows (d : CompleteData k Id K W R) (N : PrivateMap d) :
    (completeDraw d N).rowMap.comp (completeDraw d N).hiddenMatrix = d.2.2.2.val := by
  exact (AdviceFibers.observed_assemble _ _ N).trans
    (AdviceFibers.observedBase_property _ _)

theorem completeDraw_left (rhs : Id → F2) (d : CompleteData k Id K W R)
    (N : PrivateMap d) :
    AdviceExperiment.leftObservation rhs (completeDraw d N) = {
      occurrences := d.1.1, rowMap := d.1.2,
      complement := d.2.2.1.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)),
      rows := d.2.2.2.val.comp (rawProjection (fun j => toBit (rhs (d.1.1 j)))
        (PaddedLaw.choiceMask d.2.1) (PaddedLaw.choiceSlots d.2.1)) } := by
  simp only [AdviceExperiment.leftObservation, completeDraw_rows] ; rfl

theorem completeDraw_right {Name : Type} (names : Id → Fin 3 → Name)
    (d : CompleteData k Id K W R) (N : PrivateMap d) :
    AdviceExperiment.rightObservation names (completeDraw d N) =
      ⟨PaddedLaw.choiceMask d.2.1, {
        question := RawPrivateTable.supported (PaddedLaw.choiceMask d.2.1) names d.1.1
          (PaddedLaw.choiceSlots d.2.1), rowMap := d.1.2,
        complement := d.2.2.1, rows := d.2.2.2.val }⟩ := by
  simp only [AdviceExperiment.rightObservation, completeDraw_rows] ; rfl

variable [Fintype Id] [Fintype K] [Fintype W] [Fintype R] [Fintype (K →ₗ[F2] R)]

def completeWeight (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (d : CompleteData k Id K W R) : ℝ :=
  (occurrences.weight d.1.1 * publicLaw.weight d.1.2) *
    (PaddedLaw.choiceTupleWeight β d.2.1 *
      (1 / (Fintype.card (RawPoint (PaddedLaw.choiceMask d.2.1) →ₗ[F2] (K × W)) : ℝ)))

omit [Fintype R] in

theorem fullSeed_weight_observed (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (s : FullSeed k Id K W R) :
    (fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').weight s =
      completeWeight occurrences publicLaw β (completeObserve s) := rfl

omit [Fintype R] in
theorem fullSeed_weight_fiber (occurrences : FiniteDistribution (Fin k → Id))
    (publicLaw : FiniteDistribution (K →ₗ[F2] R)) (β : ℝ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1) (d : CompleteData k Id K W R)
    (s : FullSeed k Id K W R) (hs : completeObserve s = d) :
    (fullSeedLaw (V := K × W) occurrences publicLaw β hβ hβ').weight s =
      completeWeight occurrences publicLaw β d := by
  rw [fullSeed_weight_observed, hs]

end CompleteData

end
end DFVSGames.Decoder.AdviceLaw

end

section

namespace DFVSGames.Fourier.Parity

def finiteSum {ι : Type} (indices : List ι) (f : ι → Rat) : Rat :=
  match indices with
  | [] => 0
  | i :: rest => f i + finiteSum rest f

theorem finiteSum_le {ι : Type} (indices : List ι) (f : ι → Rat) (bound : Rat)
    (h : ∀ i ∈ indices, f i ≤ bound) :
    finiteSum indices f ≤ (indices.length : Rat) * bound := by
  induction indices with
  | nil => simp [finiteSum]
  | cons i rest ih =>
    have hi := h i (by simp)
    have hr := ih (by intro j hj; exact h j (by simp [hj]))
    simp only [finiteSum, List.length_cons, Rat.natCast_add, Rat.natCast_ofNat]
    grind

theorem finiteSum_split {ι : Type} (indices : List ι) (f : ι → Rat)
    (zeroParity : ι → Bool) :
    finiteSum indices f =
      finiteSum indices (fun i => if zeroParity i then f i else 0) +
      finiteSum indices (fun i => if zeroParity i then 0 else f i) := by
  induction indices with
  | nil => simp [finiteSum]
  | cons i rest ih =>
    simp only [finiteSum]
    cases zeroParity i <;> simp_all <;> grind

theorem nonzero_sum_gt_half {ι : Type} (indices : List ι) (f : ι → Rat)
    (zeroParity : ι → Bool) (ρ : Rat)
    (dense : ρ < finiteSum indices f)
    (zero_bound : finiteSum indices (fun i => if zeroParity i then f i else 0) ≤ ρ / 2) :
    ρ / 2 < finiteSum indices (fun i => if zeroParity i then 0 else f i) := by
  have := finiteSum_split indices f zeroParity
  grind

theorem signed_le_abs (coefficient character : Rat)
    (sign : character = 1 ∨ character = -1) :
    coefficient * character ≤ coefficient.abs := by
  simp only [Rat.abs]
  rcases sign with h | h <;> rw [h] <;> split <;> grind

theorem coefficient_of_bounds {ι : Type} (indices : List ι)
    (coefficient character : ι → Rat) (zeroParity : ι → Bool)
    (ρ bound : Rat) (N : Nat)
    (bound_nonneg : 0 ≤ bound)
    (length_bound : indices.length ≤ N)
    (budget : (N : Rat) * bound ≤ ρ / 2)
    (sign : ∀ i ∈ indices, character i = 1 ∨ character i = -1)
    (dense : ρ < finiteSum indices (fun i => coefficient i * character i))
    (zero_bound : finiteSum indices (fun i =>
      if zeroParity i then coefficient i * character i else 0) ≤ ρ / 2) :
    ∃ i ∈ indices, zeroParity i = false ∧ bound < (coefficient i).abs := by
  classical
  by_cases exists_large : ∃ i ∈ indices,
      zeroParity i = false ∧ bound < (coefficient i).abs
  · exact exists_large
  · have hsmall : ∀ i ∈ indices,
        (if zeroParity i then 0 else coefficient i * character i) ≤ bound := by
      intro i hi
      cases hp : zeroParity i with
      | true => simpa [hp] using bound_nonneg
      | false =>
        have habs : (coefficient i).abs ≤ bound := by
          apply Rat.not_lt.mp
          intro hlarge
          exact exists_large ⟨i, hi, hp, hlarge⟩
        simpa [hp] using Rat.le_trans (signed_le_abs _ _ (sign i hi)) habs
    have hsum := finiteSum_le indices
      (fun i => if zeroParity i then 0 else coefficient i * character i) bound hsmall
    have hlength : (indices.length : Rat) ≤ (N : Rat) :=
      Rat.natCast_le_natCast.mpr length_bound
    have hmul := Rat.mul_le_mul_of_nonneg_right hlength bound_nonneg
    have hlarge := nonzero_sum_gt_half indices
      (fun i => coefficient i * character i) zeroParity ρ dense zero_bound
    exact False.elim (by grind)

theorem coefficient_gt_half_div {ι : Type} (indices : List ι)
    (coefficient character : ι → Rat) (zeroParity : ι → Bool)
    (ρ : Rat) (N : Nat)
    (ρ_pos : 0 < ρ) (N_pos : 0 < N)
    (length_bound : indices.length ≤ N)
    (sign : ∀ i ∈ indices, character i = 1 ∨ character i = -1)
    (dense : ρ < finiteSum indices (fun i => coefficient i * character i))
    (zero_bound : finiteSum indices (fun i =>
      if zeroParity i then coefficient i * character i else 0) ≤ ρ / 2) :
    ∃ i ∈ indices, zeroParity i = false ∧
      (ρ / 2) / (N : Rat) < (coefficient i).abs := by
  have hN : (0 : Rat) < (N : Rat) := Rat.natCast_pos.mpr N_pos
  have threshold_pos : (0 : Rat) < (ρ / 2) / (N : Rat) := by
    apply (Rat.lt_div_iff hN).mpr
    grind
  have budget : (N : Rat) * ((ρ / 2) / (N : Rat)) = ρ / 2 := by
    rw [Rat.mul_comm, Rat.div_mul_cancel (Rat.ne_of_gt hN)]
  exact coefficient_of_bounds indices coefficient character zeroParity ρ
    ((ρ / 2) / (N : Rat)) N (Rat.le_of_lt threshold_pos) length_bound
    (by rw [budget]) sign dense zero_bound

theorem div_div_eq (a b c : Rat) : (a / b) / c = a / (b * c) := by
  simp only [Rat.div_def, Rat.inv_mul_rev]
  grind

theorem lemma53_arithmetic {ι : Type} (indices : List ι)
    (coefficient character : ι → Rat) (zeroParity : ι → Bool)
    (ρ : Rat) (r s : Nat)
    (ρ_pos : 0 < ρ)
    (length_bound : indices.length ≤ 2 ^ (r * s))
    (sign : ∀ i ∈ indices, character i = 1 ∨ character i = -1)
    (dense : ρ < finiteSum indices (fun i => coefficient i * character i))
    (zero_bound : finiteSum indices (fun i =>
      if zeroParity i then coefficient i * character i else 0) ≤ ρ / 2) :
    ∃ i ∈ indices, zeroParity i = false ∧
      ρ / (2 * ((2 ^ (r * s) : Nat) : Rat)) < (coefficient i).abs := by
  simpa only [div_div_eq] using
    coefficient_gt_half_div indices coefficient character zeroParity ρ
      (2 ^ (r * s)) ρ_pos (Nat.two_pow_pos _) length_bound sign dense zero_bound

end DFVSGames.Fourier.Parity
end

end
end
end
end
end
end
end

end OAI
