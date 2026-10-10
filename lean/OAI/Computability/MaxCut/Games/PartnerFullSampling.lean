import Mathlib
import OAI.Computability.MaxCut.Games.RawMapLaw
import OAI.Computability.MaxCut.Games.MaskMoment

namespace OAI

/-!
# Full slot indices and the actual partner law

Uniform indices at all positions restrict to uniform indices on an active set.
The explicit restriction/complement equivalence proves this sampling fact. The
dependent partner average then equals sampling the active set followed by all
slot indices, including unused indices outside the active set. Finally, the
coordinatewise occurrence/slot draw is related to that same law.
-/

namespace MaxCutGames.Soundness.PartnerFullSampling

open scoped BigOperators
open PartnerSampling

noncomputable section

def restrictIndices {P X : Type*} (J : Finset P) (indices : P → X) : ↥J → X :=
  fun j => indices j.val

/-- The values inside and outside a finite set reconstruct the full tuple. -/
def restrictionProductEquiv {P X : Type*} [DecidableEq P] (J : Finset P) :
    (P → X) ≃ ((↥J → X) × ({j : P // j ∉ J} → X)) where
  toFun indices := (restrictIndices J indices, fun j => indices j.val)
  invFun parts := fun j =>
    if hj : j ∈ J then parts.1 ⟨j, hj⟩ else parts.2 ⟨j, hj⟩
  left_inv indices := by
    funext j
    by_cases hj : j ∈ J <;> simp [restrictIndices, hj]
  right_inv parts := by
    apply Prod.ext
    · funext j
      simp [restrictIndices, j.property]
    · funext j
      simp [j.property]

/-- Marginalizing the nonempty complement tuple gives the exact uniform law
on the active coordinates. This includes an empty active set or complement. -/
theorem expect_restrictIndices {P X : Type*} [Fintype P] [DecidableEq P]
    [Fintype X] [Nonempty X] (J : Finset P) (h : (↥J → X) → ℝ) :
    (𝔼 indices : P → X, h (restrictIndices J indices)) =
      𝔼 activeIndices : ↥J → X, h activeIndices := by
  calc
    (𝔼 indices : P → X, h (restrictIndices J indices)) =
        𝔼 parts : (↥J → X) × ({j : P // j ∉ J} → X), h parts.1 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = 𝔼 activeIndices : ↥J → X, h activeIndices := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (↥J → X))
          (Finset.univ : Finset ({j : P // j ∉ J} → X))
          (fun parts => h parts.1))

def fromFullIndices {k t : ℕ} (a : ActiveSet k t) (indices : Fin k → Fin 3) :
    Partner k t := ⟨a, restrictIndices a.val indices⟩

/-- Fixed-active-set form of the actual three-way slot sampling identity. -/
theorem fixed_active_expect_fullIndices {k t : ℕ} (a : ActiveSet k t)
    (h : (↥a.val → Fin 3) → ℝ) :
    (𝔼 indices : Fin k → Fin 3, h (restrictIndices a.val indices)) =
      𝔼 activeIndices : ↥a.val → Fin 3, h activeIndices :=
  expect_restrictIndices a.val h

/-- All active-set fibers have `3^t` elements, so the uniform dependent-pair
average is the active-set average of the uniform slot average. -/
theorem partner_expect_active_slots (k t : ℕ) (f : Partner k t → ℝ) :
    (𝔼 p : Partner k t, f p) =
      𝔼 a : ActiveSet k t, 𝔼 indices : ↥a.val → Fin 3, f ⟨a, indices⟩ := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.sum_sigma,
    slotTuples_card, partner_card, Fintype.card_coe,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.sum_div, div_div]
  congr 1
  exact mul_comm _ _

/-- The full-index experiment has exactly the existing `Partner` law.
No independence or equality of probability laws is assumed. -/
theorem partner_expect_fullIndices (k t : ℕ) (f : Partner k t → ℝ) :
    (𝔼 p : Partner k t, f p) =
      𝔼 a : ActiveSet k t, 𝔼 indices : Fin k → Fin 3,
        f (fromFullIndices a indices) := by
  rw [partner_expect_active_slots]
  apply Finset.expect_congr rfl
  intro a _
  exact (fixed_active_expect_fullIndices a (fun indices => f ⟨a, indices⟩)).symm

/-- Slots outside active positions have no effect on the genuine projection. -/
theorem projection_eq_of_slots_eq_on_active {P : Type}
    (rhs active : P → Bool) (slot slot' : P → PartnerProjection.Slot)
    (hslot : ∀ j, active j = true → slot j = slot' j) :
    PartnerLinear.projection rhs active slot =
      PartnerLinear.projection rhs active slot' := by
  apply LinearMap.ext
  intro x
  change PartnerProjection.project rhs active slot x =
    PartnerProjection.project rhs active slot' x
  apply PartnerProjection.partner_ext rhs active
  · rfl
  · rfl
  · funext j
    by_cases hj : active j = true
    · simp [PartnerProjection.project, hj, hslot j hj]
    · simp [PartnerProjection.project, hj]

/-- Defaulting inactive slots to `.first` gives the same map as retaining all
the independently sampled full indices. -/
theorem projection_fromFullIndices {k t : ℕ} (rhs : Fin k → Bool)
    (a : ActiveSet k t) (indices : Fin k → Fin 3) :
    PartnerLinear.projection rhs (active (fromFullIndices a indices))
        (slots (fromFullIndices a indices)) =
      PartnerLinear.projection rhs (active (fromFullIndices a indices))
        (fun j => decodeSlot (indices j)) := by
  apply projection_eq_of_slots_eq_on_active
  intro j hj
  have hmem : j ∈ a.val := by
    change decide (j ∈ a.val) = true at hj
    exact of_decide_eq_true hj
  simp [slots, fromFullIndices, restrictIndices, hmem]

/-- Drawing an occurrence and a slot at each position is the same finite
sample space as drawing the occurrence tuple and the slot tuple separately. -/
def drawProductEquiv {P Id : Type*} :
    (P → Id × Fin 3) ≃ ((P → Id) × (P → Fin 3)) where
  toFun draw := (fun j => (draw j).1, fun j => (draw j).2)
  invFun parts := fun j => (parts.1 j, parts.2 j)
  left_inv draw := by funext j; rfl
  right_inv parts := by
    apply Prod.ext <;> funext j <;> rfl

/-- The raw occurrence/slot draw induces independent uniform occurrences and
uniform active slots, with all unused slot choices marginalized exactly. -/
theorem fixed_active_rawDraw_expect {k t : ℕ} {Id : Type*} [Fintype Id]
    (a : ActiveSet k t)
    (f : (Fin k → Id) → (↥a.val → Fin 3) → ℝ) :
    (𝔼 draw : Fin k → Id × Fin 3,
      f (fun j => (draw j).1)
        (restrictIndices a.val (fun j => (draw j).2))) =
      𝔼 occurrence : Fin k → Id, 𝔼 indices : ↥a.val → Fin 3,
        f occurrence indices := by
  calc
    (𝔼 draw : Fin k → Id × Fin 3,
        f (fun j => (draw j).1)
          (restrictIndices a.val (fun j => (draw j).2))) =
        𝔼 parts : (Fin k → Id) × (Fin k → Fin 3),
          f parts.1 (restrictIndices a.val parts.2) :=
      Fintype.expect_equiv drawProductEquiv _ _ (fun _ => rfl)
    _ = 𝔼 occurrence : Fin k → Id, 𝔼 indices : Fin k → Fin 3,
        f occurrence (restrictIndices a.val indices) := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product (Finset.univ : Finset (Fin k → Id))
          (Finset.univ : Finset (Fin k → Fin 3))
          (fun parts => f parts.1 (restrictIndices a.val parts.2)))
    _ = 𝔼 occurrence : Fin k → Id, 𝔼 indices : ↥a.val → Fin 3,
        f occurrence indices := by
      apply Finset.expect_congr rfl
      intro occurrence _
      exact fixed_active_expect_fullIndices a (f occurrence)

/-- The actual raw draw, including indices outside the active set, agrees
with the occurrence-then-partner experiment for every real test function. -/
theorem occurrence_partner_expect_eq_rawDraw (k t : ℕ)
    {Id : Type*} [Fintype Id] (f : (Fin k → Id) → Partner k t → ℝ) :
    (𝔼 occurrence : Fin k → Id, 𝔼 p : Partner k t, f occurrence p) =
      𝔼 a : ActiveSet k t, 𝔼 draw : Fin k → Id × Fin 3,
        f (fun j => (draw j).1) (fromFullIndices a (fun j => (draw j).2)) := by
  symm
  calc
    (𝔼 a : ActiveSet k t, 𝔼 draw : Fin k → Id × Fin 3,
        f (fun j => (draw j).1) (fromFullIndices a (fun j => (draw j).2))) =
        𝔼 a : ActiveSet k t, 𝔼 occurrence : Fin k → Id,
          𝔼 indices : ↥a.val → Fin 3, f occurrence ⟨a, indices⟩ := by
      apply Finset.expect_congr rfl
      intro a _
      exact fixed_active_rawDraw_expect a (fun occurrence indices => f occurrence ⟨a, indices⟩)
    _ = 𝔼 occurrence : Fin k → Id, 𝔼 a : ActiveSet k t,
        𝔼 indices : ↥a.val → Fin 3, f occurrence ⟨a, indices⟩ :=
      Finset.expect_comm _ _ _
    _ = 𝔼 occurrence : Fin k → Id, 𝔼 p : Partner k t, f occurrence p := by
      apply Finset.expect_congr rfl
      intro occurrence _
      exact (partner_expect_active_slots k t (f occurrence)).symm

end

end MaxCutGames.Soundness.PartnerFullSampling

/-!
Uniform raw advice coefficients obtained by discarding unused flat coordinates.
The intercept, both full columns at every position, and one singleton column at
every position are independent. For a fixed singleton set, selecting the used
columns gives exactly the uniform law on the dynamic raw coefficient type.
The identity holds for every joint test function, not merely for marginals.
-/

namespace MaxCutGames.Clean.CoefficientSampling

open Foundations.Games
open Soundness.ConditionalIncidences
open Soundness.PartnerFullSampling
open scoped BigOperators

noncomputable section

variable {P C : Type} [Fintype P] [DecidableEq P] [Fintype C] [Nonempty C]

def selectCoefficients (J : Finset P) (extra : C × (P → C × C)) (single : P → C) :
    RawCoefficients J C :=
  fun slot => match slot with
  | none => extra.1
  | some (.inl (i, j)) => if j = 0 then (extra.2 i.val).1 else (extra.2 i.val).2
  | some (.inr i) => single i.val

/-- Splitting a raw coefficient tuple into its actual independent coordinates. -/
def coefficientProductEquiv (J : Finset P) :
    RawCoefficients J C ≃ C × ((PositionOutside J → C × C) × (PositionInside J → C)) where
  toFun gamma := (gamma none,
    ((fun i => (gamma (some (.inl (i, 0))), gamma (some (.inl (i, 1))))),
      fun i => gamma (some (.inr i))))
  invFun parts := fun slot => match slot with
    | none => parts.1
    | some (.inl (i, j)) => if j = 0 then (parts.2.1 i).1 else (parts.2.1 i).2
    | some (.inr i) => parts.2.2 i
  left_inv gamma := by
    funext slot
    cases slot with
    | none => rfl
    | some slot =>
      cases slot with
      | inl pair => rcases pair with ⟨i, j⟩; fin_cases j <;> rfl
      | inr i => rfl
  right_inv parts := by
    rcases parts with ⟨intercept, full, single⟩
    rfl

/-- The complement restriction is also uniform, including an empty complement. -/
theorem expect_outside (J : Finset P) (f : (PositionOutside J → C) → ℝ) :
    (𝔼 full : P → C, f (fun j => full j.val)) =
      𝔼 outside : PositionOutside J → C, f outside := by
  calc
    _ = 𝔼 parts : (PositionInside J → C) × (PositionOutside J → C), f parts.2 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (PositionInside J → C))
          (Finset.univ : Finset (PositionOutside J → C)) (fun parts => f parts.2))

omit [Nonempty C] in
theorem expect_rawCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (𝔼 gamma : RawCoefficients J C, F gamma) =
      𝔼 intercept : C, 𝔼 full : PositionOutside J → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm (intercept, full, single)) := by
  calc
    _ = 𝔼 parts : C × ((PositionOutside J → C × C) × (PositionInside J → C)),
        F ((coefficientProductEquiv J).symm parts) :=
      Fintype.expect_equiv (coefficientProductEquiv J) _ _ (fun _ => by simp)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      apply Finset.expect_congr rfl
      intro intercept _
      rw [← Finset.univ_product_univ, Finset.expect_product]

/-- Sampling all columns and then discarding unused ones has exactly the
uniform joint law on the coefficients used by this singleton set. -/
theorem expect_selectCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (𝔼 extra : C × (P → C × C), 𝔼 single : P → C,
      F (selectCoefficients J extra single)) =
      𝔼 gamma : RawCoefficients J C, F gamma := by
  calc
    _ = 𝔼 intercept : C, 𝔼 full : P → C × C, 𝔼 single : P → C,
        F (selectCoefficients J (intercept, full) single) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = 𝔼 intercept : C, 𝔼 full : P → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm
            (intercept, (fun i => full i.val), single)) := by
      apply Finset.expect_congr rfl
      intro intercept _
      apply Finset.expect_congr rfl
      intro full _
      exact expect_restrictIndices J (fun single =>
        F ((coefficientProductEquiv J).symm (intercept, (fun i => full i.val), single)))
    _ = 𝔼 intercept : C, 𝔼 full : PositionOutside J → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm (intercept, full, single)) := by
      apply Finset.expect_congr rfl
      intro intercept _
      exact expect_outside J (fun full => 𝔼 single : PositionInside J → C,
        F ((coefficientProductEquiv J).symm (intercept, full, single)))
    _ = _ := (expect_rawCoefficients J F).symm

private theorem uniform_expectation_eq_expect_inline_CoefficientSampling {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) : (FiniteDistribution.uniform X).expectation f = 𝔼 x : X, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

theorem uniform_selectCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (FiniteDistribution.uniform (C × (P → C × C))).expectation (fun extra =>
      (FiniteDistribution.uniform (P → C)).expectation (fun single =>
        F (selectCoefficients J extra single))) =
      (FiniteDistribution.uniform (RawCoefficients J C)).expectation F := by
  simp_rw [uniform_expectation_eq_expect_inline_CoefficientSampling]
  exact expect_selectCoefficients J F

/-- The fixed-mask identity may be averaged under any independent mask law. -/
theorem mask_average_selectCoefficients (maskLaw : FiniteDistribution (Finset P))
    (F : (J : Finset P) → RawCoefficients J C → ℝ) :
    maskLaw.expectation (fun J =>
      (FiniteDistribution.uniform (C × (P → C × C))).expectation (fun extra =>
        (FiniteDistribution.uniform (P → C)).expectation (fun single =>
          F J (selectCoefficients J extra single)))) =
      maskLaw.expectation (fun J =>
        (FiniteDistribution.uniform (RawCoefficients J C)).expectation (F J)) := by
  apply FiniteDistribution.expectation_congr
  intro J
  exact uniform_selectCoefficients J (F J)

end
end MaxCutGames.Clean.CoefficientSampling

namespace MaxCutGames.Clean.NativeExperiment

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Experiment
open scoped BigOperators

noncomputable section

private theorem expectation_transport_inline_NativeExperiment {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (e : X ≃ Y) (f : Y → ℝ) :
    (μ.transport e).expectation f = μ.expectation (fun x => f (e x)) := by
  unfold FiniteDistribution.expectation FiniteDistribution.transport
  exact Fintype.sum_equiv e.symm _ _ (fun _ => by simp)

theorem iid_product_split {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (k : ℕ) :
    ((μ.product ν).iid k).transport (Game.tupleQuestionEquiv k) =
      (μ.iid k).product (ν.iid k) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro pair
  change (∏ i, μ.weight (pair.1 i) * ν.weight (pair.2 i)) =
    (∏ i, μ.weight (pair.1 i)) * ∏ i, ν.weight (pair.2 i)
  exact Finset.prod_mul_distrib

theorem expectation_iid_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (k : ℕ)
    (f : (Fin k → X × Y) → ℝ) :
    ((μ.product ν).iid k).expectation f =
      (μ.iid k).expectation (fun x =>
        (ν.iid k).expectation (fun y => f (fun i => (x i, y i)))) := by
  have law := expectation_transport_inline_NativeExperiment ((μ.product ν).iid k)
    (Game.tupleQuestionEquiv k) (fun pair => f (fun i => (pair.1 i, pair.2 i)))
  rw [iid_product_split, FiniteDistribution.expectation_product] at law
  exact law.symm

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def maskSet {k : ℕ} (mask : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => mask i = true

abbrev MaskStrategy (k : ℕ) (R O N : Type) :=
  (mask : Fin k → Bool) → RawCoefficients (maskSet mask) (Coefficient R) →
    LocalStrategies k R O N

def liftStrategy {k : ℕ} (strategy : MaskStrategy k R O N)
    (extra : Additional k R) (seed : SparseSeed k R) : LocalStrategies k R O N :=
  strategy (fun i => (seed i).1) (coefficients extra seed)

/-- The actual law: independent singleton choices followed by one independent
uniform coefficient at the intercept and each surviving partner coordinate. -/
def success (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : MaskStrategy k R O N) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform (RawCoefficients (maskSet mask) (Coefficient R))).expectation
      fun gamma => UpperBound.fixedAdviceSuccess μ (maskSet mask) g gamma (strategy mask gamma)

omit [DecidableEq O] [Fintype N] [DecidableEq N] in

theorem success_eq_flat (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : MaskStrategy k R O N) :
    success k μ g β hβ₀ hβ₁ strategy =
      Experiment.success k μ g (FiniteDistribution.uniform (Additional k R))
        β hβ₀ hβ₁ (liftStrategy strategy) := by
  unfold success Experiment.success singletonSlopeLaw
  symm
  calc
    _ = (FiniteDistribution.uniform (Additional k R)).expectation fun extra =>
        ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
          (FiniteDistribution.uniform (Fin k → Coefficient R)).expectation fun single =>
            UpperBound.fixedAdviceSuccess μ (maskSet mask) g
              (CoefficientSampling.selectCoefficients (maskSet mask) extra single)
              (strategy mask (CoefficientSampling.selectCoefficients (maskSet mask) extra single)) := by
      apply FiniteDistribution.expectation_congr
      intro extra
      rw [expectation_iid_product, FiniteDistribution.iid_uniform]
      apply FiniteDistribution.expectation_congr
      intro mask
      apply FiniteDistribution.expectation_congr
      intro single
      have hgamma : coefficients extra (fun i => (mask i, single i)) =
          CoefficientSampling.selectCoefficients (maskSet mask) extra single := by
        funext slot
        cases slot with
        | none => rfl
        | some slot =>
          cases slot with
          | inl pair => rfl
          | inr i => rfl
      change UpperBound.fixedAdviceSuccess μ (maskSet mask) g
        (coefficients extra (fun i => (mask i, single i)))
        (strategy mask (coefficients extra (fun i => (mask i, single i)))) = _
      rw [hgamma]
    _ = ((bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Additional k R)).expectation fun extra =>
          (FiniteDistribution.uniform (Fin k → Coefficient R)).expectation fun single =>
            UpperBound.fixedAdviceSuccess μ (maskSet mask) g
              (CoefficientSampling.selectCoefficients (maskSet mask) extra single)
              (strategy mask (CoefficientSampling.selectCoefficients (maskSet mask) extra single))) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro mask
      exact CoefficientSampling.uniform_selectCoefficients (maskSet mask)
        (fun gamma => UpperBound.fixedAdviceSuccess μ (maskSet mask) g gamma (strategy mask gamma))

end
end MaxCutGames.Clean.NativeExperiment

namespace MaxCutGames.Clean.ActualAdviceBridge

open scoped BigOperators
open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Soundness.RawPartnerTarget Soundness.BinaryRowTransport
open AnswerBridge

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]

def indexSlot (i : Fin 3) : PartnerProjection.Slot :=
  if i = 0 then .first else if i = 1 then .second else .third

@[simp] theorem slotIndex_indexSlot (i : Fin 3) :
    ConcreteExtraction.slotIndex (indexSlot i) = i := by
  fin_cases i <;> rfl

structure Policies (k : ℕ) (g : IncidenceExtraction.Incidence O N) (D : Type)
    [AddCommGroup D] [Module F2 D] where
  first : (J : Finset (Fin k)) → (Fin k → O) →
    (ActualHomogeneous.E k →ₗ[F2] D) → SourceAnswer k
  second : (J : Finset (Fin k)) → RawPrivateTable.SupportedV J g.name →
    (RawPoint J →ₗ[F2] D) → TargetAnswer J

def projection (g : IncidenceExtraction.Incidence O N)
    (J : Finset (Fin k)) (draw : Draw (Fin k) O) :
    ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  rawProjection (fun j => g.rhs (draw j).1) J (fun j => indexSlot (draw j).2)

def displayedQuestion (g : IncidenceExtraction.Incidence O N)
    (J : Finset (Fin k)) (draw : Draw (Fin k) O) : RawPrivateTable.SupportedV J g.name :=
  RawPrivateTable.supported J g.name (fun j => (draw j).1) (fun j => indexSlot (draw j).2)

def agrees (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) : Prop :=
  projection g J draw
      (policy.first J (fun j => (draw j).1) (Y.comp (projection g J draw))).val =
    (policy.second J (displayedQuestion g J draw) Y).val

def strategy (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) : OuterStrategy (P := Fin k) (R := Q) (O := O) (N := N) :=
  toOuterStrategy J g (rowPointStrategies coordinates J g.rhs (policy.first J)
    (extendSupportedPolicy J g.name (policy.second J)))

def encodedMapCoefficients (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    RawCoefficients J (ZeroInformation.Bits Q) :=
  rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y))

theorem sample_question [Fintype Q] [DecidableEq Q]
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (gamma : RawCoefficients J (ZeroInformation.Bits Q)) (draw : Draw (Fin k) O) :
    (actualSecond J g.name gamma draw).question = (displayedQuestion g J draw).val := by
  funext j
  simp [actualSecond, ZeroInformation.secondInput, ZeroInformation.partnerQuestion,
    membershipBool, displayedQuestion, RawPrivateTable.supported,
    RawPrivateTable.displayed]

/-- Every actual projection-agreement event is accepted after the two separate
local input/answer conversions. This is pointwise in all sampled maps/questions. -/
theorem agrees_implies_actualWin [Fintype Q] [DecidableEq Q]
    (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O)
    (hagree : agrees g policy J Y draw) :
    actualWin J g (encodedMapCoefficients coordinates J Y)
      (strategy coordinates g policy J) draw := by
  let first := policy.first J
  let second := extendSupportedPolicy J g.name (policy.second J)
  let gamma := encodedMapCoefficients coordinates J Y
  let points := rowPointStrategies coordinates J g.rhs first second
  have repack : (fun j => ((draw j).1,
      ConcreteExtraction.slotIndex (indexSlot (draw j).2))) = draw := by
    funext j
    simp
  have hfirst := rowPointStrategies_first_actual coordinates J g.rhs first second
    (fun j => (draw j).1) (fun j => indexSlot (draw j).2) Y
  rw [repack] at hfirst
  have hsecond := rowPointStrategies_second_actual coordinates J g.rhs g.name
    first second draw Y
  have hquestion := sample_question g J gamma draw
  have htarget : second (actualSecond J g.name gamma draw).question Y =
      policy.second J (displayedQuestion g J draw) Y := by
    rw [hquestion]
    exact extendSupportedPolicy_apply J g.name (policy.second J) _ Y
  change (toOuterStrategy J g points).wins
    (Soundness.RepeatedGameBounds.ActualProjection.predicateGame g
      (PartnerMapCoordinates.activeOf J))
      (actualFirst J gamma draw) (actualSecond J g.name gamma draw)
  apply toOuterStrategy_wins J g points _ _ (fun j => indexSlot (draw j).2) hquestion
  change points.first (actualFirst J gamma draw) = _ at hfirst
  change points.second (actualSecond J g.name gamma draw) =
    second (actualSecond J g.name gamma draw).question Y at hsecond
  rw [hfirst, hsecond, htarget]
  exact hagree

variable [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

/-- Actual independent weighted occurrence/position draws, at a fixed genuine
partner map. `table` is the product of the identical coordinate laws. -/
def fixedMapSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) : ℝ :=
  (FiniteDistribution.table (fun _ : Fin k => μ)).probability
    (fun draw => decide (agrees g policy J Y draw))

omit [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem fixedMapSuccess_le (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    fixedMapSuccess μ g policy J Y ≤
      UpperBound.fixedAdviceSuccess μ J g (encodedMapCoefficients coordinates J Y)
        (strategy coordinates g policy J) := by
  apply FiniteDistribution.probability_mono
  intro draw h
  exact decide_eq_true (agrees_implies_actualWin coordinates g policy J Y draw
    (of_decide_eq_true h))

def mapBitsEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k)) :
    (RawPoint J →ₗ[F2] D) ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  (RawMapLaw.rawMapEquiv J D).symm.trans (coefficientsEquiv coordinates J)

theorem uniform_maps_to_bits (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (F : RawCoefficients J (ZeroInformation.Bits Q) → ℝ) :
    (FiniteDistribution.uniform (RawPoint J →ₗ[F2] D)).expectation
      (fun Y => F (encodedMapCoefficients coordinates J Y)) =
      (FiniteDistribution.uniform (RawCoefficients J (ZeroInformation.Bits Q))).expectation F := by
  simp only [FiniteDistribution.expectation_uniform, ← Fintype.expect_eq_sum_div_card]
  exact Fintype.expect_equiv (mapBitsEquiv coordinates J) _ F (fun _ => rfl)

def nativeStrategy (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D) :
    NativeExperiment.MaskStrategy k Q O N :=
  fun mask _ => strategy coordinates g policy (NativeExperiment.maskSet mask)

/-- Sample the Bernoulli mask, a uniform actual map on its partner space, and
independent weighted equation/position draws. This is the actual advice law. -/
def success (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] D)).expectation
      (fun Y => fixedMapSuccess μ g policy (NativeExperiment.maskSet mask) Y)

theorem expectation_mono {X : Type} [Fintype X] (μ : FiniteDistribution X)
    {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
/-- The exact map/coefficient bijection joins the actual policy success to the
already-defined native clean experiment. -/
theorem success_le_native (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    success μ g policy β hβ₀ hβ₁ ≤
      NativeExperiment.success k μ g β hβ₀ hβ₁ (nativeStrategy coordinates g policy) := by
  unfold success NativeExperiment.success nativeStrategy
  apply expectation_mono
  intro mask
  calc
    _ ≤ (FiniteDistribution.uniform
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] D)).expectation
        (fun Y => UpperBound.fixedAdviceSuccess μ (NativeExperiment.maskSet mask) g
          (encodedMapCoefficients coordinates (NativeExperiment.maskSet mask) Y)
          (strategy coordinates g policy (NativeExperiment.maskSet mask))) :=
      expectation_mono _ (fun Y => fixedMapSuccess_le coordinates μ g policy _ Y)
    _ = _ := uniform_maps_to_bits coordinates (NativeExperiment.maskSet mask)
      (fun gamma => UpperBound.fixedAdviceSuccess μ (NativeExperiment.maskSet mask) g gamma
        (strategy coordinates g policy (NativeExperiment.maskSet mask)))

end
end MaxCutGames.Clean.ActualAdviceBridge

/-!
Local randomized advice responses are bounded using complete independently
sampled response tables. The verifier questions are the actual weighted
pushforward of the occurrence/position draw, with the complete private row
input retained on each side. No response sees the opposite private question.

The outer mask and coefficient tuple may be fixed before selecting either
response kernel. Revealing these data only strengthens this upper bound; they
contain no clean question or agreement event. The quantitative game-repetition
rate is a separate input to the final averaging lemma.
-/

namespace MaxCutGames.Clean.StochasticBound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds
open scoped BigOperators

noncomputable section

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

/-- The common weighted-game interface for the actual fixed-advice experiment. -/
def actualGame (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) :
    Game (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P) :=
  Simulation.weightedGame (ActualProjection.predicateGame (R := R) g (membershipBool J))
    ((FiniteDistribution.table (fun _ : P => μ)).pushforward fun draw =>
      (actualFirst J gamma draw, actualSecond J g.name gamma draw))

abbrev fixedAdviceGame := @actualGame

omit [DecidableEq R] [DecidableEq O] [DecidableEq N] in
/-- The two deterministic strategy representations have exactly the same
winning probability under the explicitly constructed question law. -/
theorem success_eq_fixedAdviceSuccess
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : Strategy (ZeroInformation.FirstInput P R O)
      (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)) :
    (actualGame μ J g gamma).success strategy =
      UpperBound.fixedAdviceSuccess μ J g gamma ⟨strategy.1, strategy.2⟩ := by
  classical
  unfold Game.success actualGame Simulation.weightedGame UpperBound.fixedAdviceSuccess
  rw [FiniteDistribution.probability_pushforward]
  rfl

omit [DecidableEq R] [DecidableEq O] [DecidableEq N] in
/-- Each stochastic local response has a deterministic complete response table
with at least its success probability. The table is chosen before the questions. -/
theorem exists_deterministic_ge_stochastic
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (responses₁ : ZeroInformation.FirstInput P R O →
      FiniteDistribution (ActualProjection.FirstAnswer P))
    (responses₂ : ZeroInformation.SecondInput P R O N →
      FiniteDistribution (ActualProjection.SecondAnswer P)) :
    ∃ strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N),
      (actualGame μ J g gamma).stochasticSuccess responses₁ responses₂ ≤
        UpperBound.fixedAdviceSuccess μ J g gamma strategy := by
  classical
  obtain ⟨strategy, h⟩ :=
    (actualGame μ J g gamma).exists_deterministic_ge_stochastic responses₁ responses₂
  refine ⟨⟨strategy.1, strategy.2⟩, ?_⟩
  calc
    _ ≤ (actualGame μ J g gamma).success strategy := h
    _ = _ := success_eq_fixedAdviceSuccess μ J g gamma strategy

theorem fixed_advice_stochastic_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (responses₁ : ZeroInformation.FirstInput P R O →
      FiniteDistribution (ActualProjection.FirstAnswer P))
    (responses₂ : ZeroInformation.SecondInput P R O N →
      FiniteDistribution (ActualProjection.SecondAnswer P))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    (actualGame μ J g gamma).stochasticSuccess responses₁ responses₂ ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  obtain ⟨strategy, h⟩ := exists_deterministic_ge_stochastic μ J g gamma responses₁ responses₂
  exact h.trans (UpperBound.fixed_advice_success_le_repeated_value μ J g gamma strategy distinct)

/-- A pair of response kernels, each indexed only by its own complete input. -/
abbrev Responses (P R O N : Type) [Fintype P] [DecidableEq P] :=
  (ZeroInformation.FirstInput P R O → FiniteDistribution (ActualProjection.FirstAnswer P)) ×
  (ZeroInformation.SecondInput P R O N → FiniteDistribution (ActualProjection.SecondAnswer P))

/-- The native experiment samples a mask, then the actual coefficient tuple.
The kernels may depend on these public choices but not on an opposite input. -/
def nativeStochasticSuccess (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      (RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R))).expectation
      fun gamma => (actualGame μ (NativeExperiment.maskSet mask) g gamma).stochasticSuccess
        (responses mask gamma).1 (responses mask gamma).2

private theorem expectation_mono_inline_StochasticBound {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

omit [DecidableEq O] [DecidableEq N] in
/-- The deterministic witness family is indexed by the pre-question public
data only. No single global deterministic strategy is claimed here. -/
theorem native_stochastic_le_deterministic
    (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N) :
    ∃ strategy : NativeExperiment.MaskStrategy k R O N,
      nativeStochasticSuccess k μ g β hβ₀ hβ₁ responses ≤
        NativeExperiment.success k μ g β hβ₀ hβ₁ strategy := by
  classical
  let strategy : NativeExperiment.MaskStrategy k R O N := fun mask gamma =>
    Classical.choose (exists_deterministic_ge_stochastic μ (NativeExperiment.maskSet mask)
      g gamma (responses mask gamma).1 (responses mask gamma).2)
  refine ⟨strategy, ?_⟩
  unfold nativeStochasticSuccess NativeExperiment.success
  apply expectation_mono_inline_StochasticBound
  intro mask
  apply expectation_mono_inline_StochasticBound
  intro gamma
  exact Classical.choose_spec (exists_deterministic_ge_stochastic μ
    (NativeExperiment.maskSet mask) g gamma (responses mask gamma).1 (responses mask gamma).2)

/-- Stochastic kernels satisfy the same exact clean-mask moment as deterministic
ones. The only supplied rate is for the actual ordinary repeated incidence game. -/
theorem native_stochastic_le_mask_moment
    (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) (ρ : ℝ)
    (rate : ∀ n, ((incidenceGame g (μ.pushforward (incidence g.name))).repetition n).value ≤ ρ ^ n) :
    nativeStochasticSuccess k μ g β hβ₀ hβ₁ responses ≤
      (1 - cleanProbability β (ZeroInformation.Bits R) * (1 - ρ)) ^ k := by
  obtain ⟨strategy, h⟩ := native_stochastic_le_deterministic k μ g β hβ₀ hβ₁ responses
  rw [NativeExperiment.success_eq_flat] at h
  exact h.trans (Experiment.success_le_of_repetition k μ g
    (FiniteDistribution.uniform (Experiment.Additional k R)) β hβ₀ hβ₁
    (NativeExperiment.liftStrategy strategy) distinct ρ rate)

end
end MaxCutGames.Clean.StochasticBound

end OAI
