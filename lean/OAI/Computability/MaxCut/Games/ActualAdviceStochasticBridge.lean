import Mathlib
import OAI.Computability.MaxCut.Games.PartnerFullSampling

namespace OAI

/-! Actual randomized point policies are transported locally into Boolean
answer kernels. Complete response tables are selected only after public advice
is fixed and before the remaining questions. No global deterministic policy
independent of public advice is asserted or needed for this upper bound. -/

namespace MaxCutGames.Clean.ActualAdviceStochasticBridge

open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.RawPartnerTarget
open Soundness.RepeatedGameBounds
open AnswerBridge ActualAdviceBridge

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

instance sourceAnswerNonempty : Nonempty (SourceAnswer k) := ⟨⟨(1, 0), rfl⟩⟩
instance targetAnswerNonempty (J : Finset (Fin k)) : Nonempty (TargetAnswer J) :=
  ⟨defaultTargetAnswer J⟩

structure Policies (k : ℕ) (g : IncidenceExtraction.Incidence O N) (D : Type)
    [AddCommGroup D] [Module F2 D] where
  first : (J : Finset (Fin k)) → (Fin k → O) →
    (ActualHomogeneous.E k →ₗ[F2] D) → FiniteDistribution (SourceAnswer k)
  second : (J : Finset (Fin k)) → RawPrivateTable.SupportedV J g.name →
    (RawPoint J →ₗ[F2] D) → FiniteDistribution (TargetAnswer J)

def extendTargetKernel (J : Finset (Fin k)) (names : O → Fin 3 → N)
    (kernel : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) →
      FiniteDistribution (TargetAnswer J))
    (question : Fin k → Sum O N) (Y : RawPoint J →ₗ[F2] D) :
    FiniteDistribution (TargetAnswer J) :=
  if h : question ∈ Set.range
      (fun e : RawPrivateTable.Extension k O => RawPrivateTable.displayed J names e.1 e.2)
  then kernel ⟨question, h⟩ Y else FiniteDistribution.uniform (TargetAnswer J)

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem extendTargetKernel_apply (J : Finset (Fin k)) (names : O → Fin 3 → N)
    (kernel : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) →
      FiniteDistribution (TargetAnswer J))
    (V : RawPrivateTable.SupportedV J names) (Y : RawPoint J →ₗ[F2] D) :
    extendTargetKernel J names kernel V.val Y = kernel V Y := by
  unfold extendTargetKernel
  rw [dite_eq_left V.property]
  congr 1

def firstResponse (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (qa : ZeroInformation.FirstInput (Fin k) Q O) :
    FiniteDistribution (ActualProjection.FirstAnswer (Fin k)) :=
  (policy.first J qa.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap g.rhs qa))).pushforward
      (fun x => ActualPointAnswers.firstAnswer (fun j => g.rhs (qa.question j)) x.val)

def secondResponse (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (qb : ZeroInformation.SecondInput (Fin k) Q O N) :
    FiniteDistribution (ActualProjection.SecondAnswer (Fin k)) :=
  (extendTargetKernel J g.name (policy.second J) qb.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J qb))).pushforward
      (fun v => ActualPointAnswers.secondAnswer
        (ActualPointAnswers.displayedRhs g.rhs qb.question) J v.val)

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem decodeFirstMap_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap g.rhs
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw)) =
      Y.comp (projection g J draw) := by
  have h := ActualInputRows.firstMap_actual J g.rhs (fun j => (draw j).1)
    (fun j => indexSlot (draw j).2) (coordinates.toLinearMap.comp Y)
  have repack : (fun j => ((draw j).1,
      ConcreteExtraction.slotIndex (indexSlot (draw j).2))) = draw := by
    funext j
    simp
  rw [repack] at h
  unfold encodedMapCoefficients projection
  rw [h]
  apply LinearMap.ext
  intro x
  exact coordinates.symm_apply_apply _

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem decodeSecondMap_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)) = Y := by
  unfold encodedMapCoefficients
  rw [ActualInputRows.secondMap_actual]
  ext x
  simp

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem firstResponse_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    firstResponse coordinates g policy J
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw) =
      (policy.first J (fun j => (draw j).1) (Y.comp (projection g J draw))).pushforward
        (fun x => ActualPointAnswers.firstAnswer (fun j => g.rhs (draw j).1) x.val) := by
  unfold firstResponse
  rw [decodeFirstMap_actual]
  rfl

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem secondResponse_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    secondResponse coordinates g policy J
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw) =
      (policy.second J (displayedQuestion g J draw) Y).pushforward
        (fun v => ActualPointAnswers.secondAnswer
          (ActualPointAnswers.displayedRhs g.rhs (displayedQuestion g J draw).val) J v.val) := by
  unfold secondResponse
  rw [decodeSecondMap_actual, sample_question, extendTargetKernel_apply]

/-- Two private finite answer draws, after receiving the respective actual
question and linear row map. Acceptance is equality under the real projection. -/
def fixedMapSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) : ℝ :=
  (FiniteDistribution.table (fun _ : Fin k => μ)).expectation fun draw =>
    (policy.first J (fun j => (draw j).1) (Y.comp (projection g J draw))).expectation fun x =>
      (policy.second J (displayedQuestion g J draw) Y).expectation fun v =>
        if projection g J draw x.val = v.val then 1 else 0

omit [DecidableEq O] [DecidableEq N] [Fintype D] in
theorem fixedMapSuccess_le (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    fixedMapSuccess μ g policy J Y ≤
      (StochasticBound.actualGame μ J g (encodedMapCoefficients coordinates J Y)).stochasticSuccess
        (firstResponse coordinates g policy J) (secondResponse coordinates g policy J) := by
  unfold fixedMapSuccess Game.stochasticSuccess StochasticBound.actualGame
    Simulation.weightedGame
  rw [FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro draw
  rw [firstResponse_actual, secondResponse_actual,
    FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro x
  rw [FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro v
  by_cases h : projection g J draw x.val = v.val
  · have accepted := ActualPointAnswers.actual_accepts J g
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw)
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)
      (fun j => indexSlot (draw j).2)
      (sample_question g J (encodedMapCoefficients coordinates J Y) draw)
      x.val v.val x.property h
    have firstQuestion :
        (actualFirst J (encodedMapCoefficients coordinates J Y) draw).question =
          (fun j => (draw j).1) := rfl
    rw [firstQuestion] at accepted
    have accepted' : (ActualProjection.predicateGame g (membershipBool J)).accepts
        (actualFirst J (encodedMapCoefficients coordinates J Y) draw)
        (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)
        (ActualPointAnswers.firstAnswer (fun j => g.rhs (draw j).1) x.val)
        (ActualPointAnswers.secondAnswer
          (ActualPointAnswers.displayedRhs g.rhs (displayedQuestion g J draw).val)
          J v.val) := by
      change ActualProjection.accepts g (PartnerMapCoordinates.activeOf J) _ _ _ _
      rw [← sample_question g J (encodedMapCoefficients coordinates J Y) draw]
      exact accepted
    simp only [h, ite_eq_left, accepted', decide_true, le_refl]
  · simp only [h, ite_false]
    split <;> norm_num

def responses (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (mask : Fin k → Bool)
    (_ : RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits Q)) :
    StochasticBound.Responses (Fin k) Q O N :=
  (firstResponse coordinates g policy (NativeExperiment.maskSet mask),
   secondResponse coordinates g policy (NativeExperiment.maskSet mask))

def success (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] D)).expectation
      (fun Y => fixedMapSuccess μ g policy (NativeExperiment.maskSet mask) Y)

omit [DecidableEq O] [DecidableEq N] in
theorem success_le_native_stochastic (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    success μ g policy β hβ₀ hβ₁ ≤
      StochasticBound.nativeStochasticSuccess k μ g β hβ₀ hβ₁
        (responses coordinates g policy) := by
  unfold success StochasticBound.nativeStochasticSuccess responses
  apply expectation_mono
  intro mask
  calc
    _ ≤ (FiniteDistribution.uniform
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] D)).expectation
        (fun Y => (StochasticBound.actualGame μ (NativeExperiment.maskSet mask) g
          (encodedMapCoefficients coordinates (NativeExperiment.maskSet mask) Y)).stochasticSuccess
          (firstResponse coordinates g policy (NativeExperiment.maskSet mask))
          (secondResponse coordinates g policy (NativeExperiment.maskSet mask))) :=
      expectation_mono _ (fun Y => fixedMapSuccess_le coordinates μ g policy _ Y)
    _ = _ := uniform_maps_to_bits coordinates (NativeExperiment.maskSet mask)
      (fun gamma => (StochasticBound.actualGame μ (NativeExperiment.maskSet mask) g gamma).stochasticSuccess
        (firstResponse coordinates g policy (NativeExperiment.maskSet mask))
        (secondResponse coordinates g policy (NativeExperiment.maskSet mask)))

omit [DecidableEq O] [DecidableEq N] in
theorem success_le_some_native (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    ∃ strategy : NativeExperiment.MaskStrategy k Q O N,
      success μ g policy β hβ₀ hβ₁ ≤ NativeExperiment.success k μ g β hβ₀ hβ₁ strategy := by
  obtain ⟨strategy, h⟩ := StochasticBound.native_stochastic_le_deterministic
    k μ g β hβ₀ hβ₁ (responses coordinates g policy)
  exact ⟨strategy, (success_le_native_stochastic coordinates μ g policy β hβ₀ hβ₁).trans h⟩

end
end MaxCutGames.Clean.ActualAdviceStochasticBridge

/-!
The exact combined-map density formula of Lemma 6.3 for genuine finite-dimensional
binary linear maps. Subspaces are supplied as kernels; their annihilator counts
and all normalized first and second moments are proved, not assumed.
-/

namespace MaxCutGames.Soundness.LinearMapDensity

open scoped BigOperators

universe u v w

variable {E : Type u} {R : Type v}
variable [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
variable [AddCommGroup R] [Module (ZMod 2) R] [FiniteDimensional (ZMod 2) R]

noncomputable def uniformMean {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  Finset.expect Finset.univ f

theorem uniformMean_eq_sum_div_card {α : Type*} [Fintype α] (f : α → ℝ) :
    uniformMean f = (∑ a, f a) / (Fintype.card α : ℝ) := by
  simp [uniformMean, Finset.expect_eq_sum_div_card]

theorem uniformMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) :=
  Finset.expect_comm _ _ _

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f :=
  (Finset.mul_expect _ _ _).symm

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c :=
  Fintype.expect_const _

omit [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) R] in
theorem restriction_surjective (K : Submodule (ZMod 2) E) :
    Function.Surjective (LinearMap.domRestrict' (M₂ := R) K) := by
  intro f
  obtain ⟨g, hg⟩ := f.exists_extend
  exact ⟨g, hg⟩

omit [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) R] in
theorem restriction_zero_iff (K : Submodule (ZMod 2) E) (M : E →ₗ[ZMod 2] R) :
    LinearMap.domRestrict' K M = 0 ↔ K ≤ M.ker := by
  constructor
  · intro h x hx
    have := LinearMap.congr_fun h (⟨x, hx⟩ : K)
    exact this
  · intro h
    ext x
    exact h x.property

/-- Pulling back a map along a projection produces a map annihilating its kernel. -/
def pullbackMap {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (π : E →ₗ[ZMod 2] V) (B : V →ₗ[ZMod 2] R) :
    {M : E →ₗ[ZMod 2] R // π.ker ≤ M.ker} :=
  ⟨B.comp π, by
    intro x hx
    change B (π x) = 0
    change π x = 0 at hx
    rw [hx, map_zero]⟩

omit [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) R] in
/-- The pullback map is a bijection onto the genuine kernel-annihilator event.
This connects the density calculation to uniform maps on the partner space. -/
theorem pullbackMap_bijective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (π : E →ₗ[ZMod 2] V) (hπ : Function.Surjective π) :
    Function.Bijective (pullbackMap (R := R) π) := by
  constructor
  · intro B C h
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    exact LinearMap.congr_fun (congrArg Subtype.val h) x
  · intro M
    obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
    refine ⟨M.val.comp s, ?_⟩
    apply Subtype.ext
    ext x
    change M.val (s (π x)) = M.val x
    have hx : x - s (π x) ∈ π.ker := by
      have hsx := LinearMap.congr_fun hs (π x)
      change π (s (π x)) = π x at hsx
      change π (x - s (π x)) = 0
      rw [map_sub, hsx, sub_self]
    have hz : M.val (x - s (π x)) = 0 := M.property hx
    rw [map_sub] at hz
    exact (sub_eq_zero.mp hz).symm

theorem annihilator_count [Fintype (E →ₗ[ZMod 2] R)] (K : Submodule (ZMod 2) E) :
    Nat.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} *
      2 ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) =
        Fintype.card (E →ₗ[ZMod 2] R) := by
  classical
  let restriction := LinearMap.domRestrict' (M₂ := R) K
  have h := Gadget.LinearKernelCount.zero_event_card_mul_pow_rank restriction
  have hrange : restriction.range = ⊤ :=
    LinearMap.range_eq_top.mpr (restriction_surjective K)
  have hcard : Nat.card {M : E →ₗ[ZMod 2] R // restriction M = 0} =
      Nat.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} :=
    Nat.card_congr (Equiv.subtypeEquivRight (restriction_zero_iff K))
  rw [hcard, hrange, finrank_top, Module.finrank_linearMap] at h
  simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using h

noncomputable def kernelDensity (K : Submodule (ZMod 2) E)
    (M : E →ₗ[ZMod 2] R) : ℝ := by
  classical
  exact if K ≤ M.ker then (2 : ℝ) ^
    (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) else 0

theorem kernelDensity_mean [Fintype (E →ₗ[ZMod 2] R)]
    (K : Submodule (ZMod 2) E) : uniformMean (kernelDensity (R := R) K) = 1 := by
  classical
  have hc := annihilator_count (R := R) K
  have hreal : (Nat.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} : ℝ) *
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) =
        Fintype.card (E →ₗ[ZMod 2] R) := by exact_mod_cast hc
  rw [uniformMean_eq_sum_div_card]
  have hsum : (∑ M : E →ₗ[ZMod 2] R, kernelDensity K M) =
      (Nat.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} : ℝ) *
        (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) := by
    simp [kernelDensity, Nat.card_eq_fintype_card, Fintype.card_subtype,
      ← Finset.sum_filter]
  rw [hsum, hreal]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

omit [FiniteDimensional (ZMod 2) R] in
/-- Pointwise overlap formula, using the actual dimension formula for subspaces. -/
theorem kernelDensity_product (K L : Submodule (ZMod 2) E)
    (M : E →ₗ[ZMod 2] R) :
    kernelDensity K M * kernelDensity L M =
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊓ L : Submodule (ZMod 2) E)) *
        kernelDensity (K ⊔ L) M := by
  classical
  have hd := K.finrank_sup_add_finrank_inf_eq L
  have hexp :
      Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K +
        Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) L =
      Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊓ L : Submodule (ZMod 2) E) +
        Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊔ L : Submodule (ZMod 2) E) := by
    have hm := congrArg (fun n => Module.finrank (ZMod 2) R * n) hd.symm
    simpa [Nat.mul_add, Nat.add_comm] using hm
  have hp :
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) *
        2 ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) L) =
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊓ L : Submodule (ZMod 2) E)) *
        2 ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊔ L : Submodule (ZMod 2) E)) := by
    rw [← pow_add, ← pow_add, hexp]
  by_cases hK : K ≤ M.ker <;> by_cases hL : L ≤ M.ker <;>
    simp [kernelDensity, sup_le_iff, hK, hL, hp]

/-- The two-kernel second-moment identity for the uniform law on all genuine
linear maps E→R. No annihilator probability is a hypothesis. -/
theorem kernelDensity_pair_mean [Fintype (E →ₗ[ZMod 2] R)]
    (K L : Submodule (ZMod 2) E) :
    uniformMean (fun M : E →ₗ[ZMod 2] R => kernelDensity K M * kernelDensity L M) =
      (2 : ℝ) ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(K ⊓ L : Submodule (ZMod 2) E)) := by
  simp_rw [kernelDensity_product]
  rw [uniformMean_const_mul, kernelDensity_mean, mul_one]

noncomputable def mixtureDensity {Partner : Type w} [Fintype Partner]
    (kernels : Partner → Submodule (ZMod 2) E) (M : E →ₗ[ZMod 2] R) : ℝ :=
  uniformMean (fun p => kernelDensity (kernels p) M)

theorem mixtureDensity_mean {Partner : Type w} [Fintype Partner] [Nonempty Partner]
    [Fintype (E →ₗ[ZMod 2] R)] (kernels : Partner → Submodule (ZMod 2) E) :
    uniformMean (mixtureDensity (R := R) kernels) = 1 := by
  unfold mixtureDensity
  rw [uniformMean_comm]
  simp_rw [kernelDensity_mean]
  exact uniformMean_const 1

/-- Lemma 6.3's exact second-moment identity for an arbitrary finite uniform
list of genuine kernel subspaces. The two partner indices are independent
because the right side is an iterated uniform expectation. -/
theorem mixtureDensity_second_moment {Partner : Type w} [Fintype Partner]
    [Fintype (E →ₗ[ZMod 2] R)] (kernels : Partner → Submodule (ZMod 2) E) :
    uniformMean (fun M : E →ₗ[ZMod 2] R => (mixtureDensity kernels M) ^ 2) =
      uniformMean (fun p => uniformMean (fun q => (2 : ℝ) ^
        (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) ↥(kernels p ⊓ kernels q : Submodule (ZMod 2) E)))) := by
  have hexpand (M : E →ₗ[ZMod 2] R) :
      (mixtureDensity kernels M) ^ 2 =
        uniformMean (fun p => uniformMean (fun q =>
          kernelDensity (kernels p) M * kernelDensity (kernels q) M)) := by
    simpa [mixtureDensity, uniformMean, pow_two] using
      (Fintype.expect_mul_expect (fun p => kernelDensity (kernels p) M)
        (fun q => kernelDensity (kernels q) M))
  simp_rw [hexpand]
  rw [uniformMean_comm]
  congr 1
  funext p
  rw [uniformMean_comm]
  simp_rw [kernelDensity_pair_mean]

theorem kernelDensity_weighted_mean [Fintype (E →ₗ[ZMod 2] R)]
    (K : Submodule (ZMod 2) E)
    [Fintype {M : E →ₗ[ZMod 2] R // K ≤ M.ker}]
    (H : (E →ₗ[ZMod 2] R) → ℝ) :
    uniformMean (fun M => kernelDensity K M * H M) =
      uniformMean (fun M : {M : E →ₗ[ZMod 2] R // K ≤ M.ker} => H M.val) := by
  classical
  let c : ℝ := (2 : ℝ) ^
    (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hcount :
      Fintype.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} *
        2 ^ (Module.finrank (ZMod 2) R * Module.finrank (ZMod 2) K) =
      Fintype.card (E →ₗ[ZMod 2] R) := by
    simpa only [Nat.card_eq_fintype_card] using annihilator_count (R := R) K
  have hr : (Fintype.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} : ℝ) * c =
      (Fintype.card (E →ₗ[ZMod 2] R) : ℝ) := by
    dsimp [c]
    exact_mod_cast hcount
  have hdenom : (Fintype.card (E →ₗ[ZMod 2] R) : ℝ) =
      c * (Fintype.card {M : E →ₗ[ZMod 2] R // K ≤ M.ker} : ℝ) := by
    simpa only [mul_comm] using hr.symm
  have hsum : (∑ M : E →ₗ[ZMod 2] R, kernelDensity K M * H M) =
      c * ∑ M : {M : E →ₗ[ZMod 2] R // K ≤ M.ker}, H M.val := by
    simp only [kernelDensity, ite_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_subtype _ (fun M => by simp) H
  rw [uniformMean_eq_sum_div_card, uniformMean_eq_sum_div_card, hsum, hdenom]
  exact mul_div_mul_left _ _ hc

theorem pullback_uniformMean {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype (E →ₗ[ZMod 2] R)] [Fintype (V →ₗ[ZMod 2] R)]
    (π : E →ₗ[ZMod 2] V) (hπ : Function.Surjective π)
    (H : (E →ₗ[ZMod 2] R) → ℝ) :
    uniformMean (fun B : V →ₗ[ZMod 2] R => H (B.comp π)) =
      uniformMean (fun M => kernelDensity π.ker M * H M) := by
  classical
  rw [kernelDensity_weighted_mean]
  exact Fintype.expect_bijective (pullbackMap (R := R) π)
    (pullbackMap_bijective (R := R) π hπ) _ _ (fun _ => rfl)

theorem mixture_pullback_uniformMean {Partner : Type*} [Fintype Partner]
    {V : Partner → Type*} [∀ p, AddCommGroup (V p)] [∀ p, Module (ZMod 2) (V p)]
    [Fintype (E →ₗ[ZMod 2] R)] [∀ p, Fintype (V p →ₗ[ZMod 2] R)]
    (π : ∀ p, E →ₗ[ZMod 2] V p) (hπ : ∀ p, Function.Surjective (π p))
    (H : (E →ₗ[ZMod 2] R) → ℝ) :
    uniformMean (fun p => uniformMean (fun B : V p →ₗ[ZMod 2] R => H (B.comp (π p)))) =
    uniformMean (fun M => mixtureDensity (fun p => (π p).ker) M * H M) := by
  have hp (p : Partner) :
      uniformMean (fun B : V p →ₗ[ZMod 2] R => H (B.comp (π p))) =
      uniformMean (fun M : E →ₗ[ZMod 2] R => kernelDensity (π p).ker M * H M) :=
    pullback_uniformMean (π p) (hπ p) H
  simp_rw [hp]
  rw [uniformMean_comm]
  congr 1
  funext M
  exact (Finset.expect_mul Finset.univ (fun p => kernelDensity (π p).ker M) (H M)).symm

end MaxCutGames.Soundness.LinearMapDensity

/-!
The real-valued finite-expectation argument in Lemma 6.3 and equation (6.11).
The density's normalization and second-moment bound are inputs; the variance,
Cauchy--Schwarz comparison, parameter error, and transferred signal are proved.
The test is allowed to depend on every coordinate of the sampled map.
-/

namespace MaxCutGames.Soundness.ExpectationComparison

open scoped BigOperators

variable {ι : Type*}

/-- Centering a normalized density subtracts exactly one from its second moment. -/
theorem density_variance_identity (s : Finset ι) (hs : s.Nonempty)
    (d : ι → ℝ) (hd : (𝔼 i ∈ s, d i) = 1) :
    (𝔼 i ∈ s, (d i - 1) ^ 2) = (𝔼 i ∈ s, d i ^ 2) - 1 := by
  calc
    (𝔼 i ∈ s, (d i - 1) ^ 2)
        = (𝔼 i ∈ s, ((d i ^ 2 - 2 * d i) + 1)) := by
          apply Finset.expect_congr rfl
          intro i _
          ring
    _ = (𝔼 i ∈ s, d i ^ 2) - 1 := by
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
        ← Finset.mul_expect, Finset.expect_const hs, hd]
      ring

theorem density_variance_le (s : Finset ι) (hs : s.Nonempty)
    (d : ι → ℝ) (ε : ℝ) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε) :
    (𝔼 i ∈ s, (d i - 1) ^ 2) ≤ ε := by
  rw [density_variance_identity s hs d hd]
  linarith

theorem bounded_test_second_moment (s : Finset ι) (hs : s.Nonempty)
    (H : ι → ℝ) (hH : ∀ i ∈ s, |H i| ≤ 1) :
    (𝔼 i ∈ s, H i ^ 2) ≤ 1 := by
  apply Finset.expect_le hs
  intro i hi
  exact (sq_le_one_iff_abs_le_one (H i)).mpr (hH i hi)

/-- Cauchy--Schwarz for an arbitrary whole-map test, in squared form. -/
theorem bounded_test_centered_square (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε : ℝ) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) :
    (𝔼 i ∈ s, H i * (d i - 1)) ^ 2 ≤ ε := by
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq s H (fun i => d i - 1)
  have hvnonneg : 0 ≤ (𝔼 i ∈ s, (d i - 1) ^ 2) :=
    Finset.expect_nonneg (fun i _ => sq_nonneg (d i - 1))
  have hHsecond := bounded_test_second_moment s hs H hH
  have hproduct := mul_le_mul_of_nonneg_right hHsecond hvnonneg
  have hvariance := density_variance_le s hs d ε hd hsecond
  nlinarith

/-- The actual difference of the two normalized finite expectations. -/
theorem bounded_test_expectation_comparison (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε : ℝ) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) :
    |(𝔼 i ∈ s, H i * d i) - (𝔼 i ∈ s, H i)| ≤ Real.sqrt ε := by
  have hdiff : (𝔼 i ∈ s, H i * d i) - (𝔼 i ∈ s, H i) =
      (𝔼 i ∈ s, H i * (d i - 1)) := by
    rw [← Finset.expect_sub_distrib]
    apply Finset.expect_congr rfl
    intro i _
    ring
  rw [hdiff]
  exact Real.abs_le_sqrt (bounded_test_centered_square s hs d H ε hd hsecond hH)

/-- The squared parameter inequality implies error at most θ/4. -/
theorem comparison_error_le_quarter (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2) : Real.sqrt ε ≤ θ / 4 := by
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hε⟩

/-- The real inequality selected by equation (4.4) gives its stated error. -/
theorem parameter_error_le_quarter (t k cap θ : ℝ) (hk : 0 < k)
    (hθ : 0 < θ) (hsize : 16 * t ^ 2 * cap / θ ^ 2 ≤ k) :
    Real.sqrt (t ^ 2 / k * cap) ≤ θ / 4 := by
  apply comparison_error_le_quarter _ θ hθ.le
  have hmult : 16 * t ^ 2 * cap ≤ k * θ ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hθ)).mp hsize
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hk).mpr
  nlinarith

theorem map_law_parameter_error (t k L : ℕ) (θ : ℝ) (hk : 0 < k)
    (hθ : 0 < θ)
    (hsize : 16 * (t : ℝ) ^ 2 * (2 : ℝ) ^ (t * L) / θ ^ 2 ≤ (k : ℝ)) :
    Real.sqrt ((t : ℝ) ^ 2 / (k : ℝ) * (2 : ℝ) ^ (t * L)) ≤ θ / 4 := by
  exact parameter_error_le_quarter (t : ℝ) (k : ℝ) ((2 : ℝ) ^ (t * L)) θ
    (by exact_mod_cast hk) hθ hsize

theorem bounded_test_expectation_quarter (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) :
    |(𝔼 i ∈ s, H i * d i) - (𝔼 i ∈ s, H i)| ≤ θ / 4 :=
  (bounded_test_expectation_comparison s hs d H ε hd hsecond hH).trans
    (comparison_error_le_quarter ε θ hθ hε)

/-- A signal at least θ under the uniform law stays at least θ/2 after transfer. -/
theorem transferred_signal_lower (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) (hsignal : θ ≤ (𝔼 i ∈ s, H i)) :
    θ / 2 ≤ (𝔼 i ∈ s, H i * d i) := by
  have h := abs_le.mp
    (bounded_test_expectation_quarter s hs d H ε θ hθ hε hd hsecond hH)
  linarith

/-- Equation (6.10), allowing the chosen index and sign to depend on the row. -/
def wholeMapTest {Map Row Column Index : Type*} (row : Map → Row)
    (column : Map → Column) (sign : Row → ℝ) (value : Row → Column → ℝ)
    (chosen : Row → Index) (character : Index → Column → ℝ) (M : Map) : ℝ :=
  sign (row M) * value (row M) (column M) * character (chosen (row M)) (column M)

theorem wholeMapTest_abs_le_one {Map Row Column Index : Type*}
    (row : Map → Row) (column : Map → Column) (sign : Row → ℝ)
    (value : Row → Column → ℝ) (chosen : Row → Index)
    (character : Index → Column → ℝ)
    (hsign : ∀ r, |sign r| ≤ 1) (hvalue : ∀ r c, |value r c| ≤ 1)
    (hcharacter : ∀ t c, |character t c| ≤ 1) (M : Map) :
    |wholeMapTest row column sign value chosen character M| ≤ 1 := by
  simp only [wholeMapTest, abs_mul]
  have hfirst : |sign (row M)| * |value (row M) (column M)| ≤ 1 := by
    nlinarith [hsign (row M), hvalue (row M) (column M),
      abs_nonneg (sign (row M)), abs_nonneg (value (row M) (column M)),
      mul_le_mul (hsign (row M)) (hvalue (row M) (column M))
        (abs_nonneg (value (row M) (column M))) (by norm_num : (0 : ℝ) ≤ 1)]
  have hmul := mul_le_mul hfirst (hcharacter (chosen (row M)) (column M))
    (abs_nonneg (character (chosen (row M)) (column M))) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using hmul

/-- Instantiate comparison with equation (6.10), including its row-dependent index. -/
theorem wholeMapTest_comparison {Map Row Column Index : Type*}
    (s : Finset Map) (hs : s.Nonempty) (d : Map → ℝ) (ε : ℝ)
    (row : Map → Row) (column : Map → Column) (sign : Row → ℝ)
    (value : Row → Column → ℝ) (chosen : Row → Index)
    (character : Index → Column → ℝ)
    (hd : (𝔼 M ∈ s, d M) = 1)
    (hsecond : (𝔼 M ∈ s, d M ^ 2) ≤ 1 + ε)
    (hsign : ∀ r, |sign r| ≤ 1) (hvalue : ∀ r c, |value r c| ≤ 1)
    (hcharacter : ∀ t c, |character t c| ≤ 1) :
    |(𝔼 M ∈ s, wholeMapTest row column sign value chosen character M * d M) -
      (𝔼 M ∈ s, wholeMapTest row column sign value chosen character M)|
      ≤ Real.sqrt ε := by
  apply bounded_test_expectation_comparison s hs d _ ε hd hsecond
  intro M _
  exact wholeMapTest_abs_le_one row column sign value chosen character
    hsign hvalue hcharacter M

/-- Average a uniform per-U error, allowing the map sample space to depend on U. -/
theorem averaged_expectation_comparison {U : Type*} (Map : U → Type*)
    (us : Finset U) (hus : us.Nonempty) (maps : (u : U) → Finset (Map u))
    (hmaps : ∀ u ∈ us, (maps u).Nonempty)
    (d H : (u : U) → Map u → ℝ) (ε : ℝ)
    (hd : ∀ u ∈ us, (𝔼 M ∈ maps u, d u M) = 1)
    (hsecond : ∀ u ∈ us, (𝔼 M ∈ maps u, d u M ^ 2) ≤ 1 + ε)
    (hH : ∀ u ∈ us, ∀ M ∈ maps u, |H u M| ≤ 1) :
    |(𝔼 u ∈ us, 𝔼 M ∈ maps u, H u M * d u M) -
      (𝔼 u ∈ us, 𝔼 M ∈ maps u, H u M)| ≤ Real.sqrt ε := by
  rw [← Finset.expect_sub_distrib]
  calc
    _ ≤ 𝔼 u ∈ us,
        |(𝔼 M ∈ maps u, H u M * d u M) - (𝔼 M ∈ maps u, H u M)| :=
      Finset.abs_expect_le _ _
    _ ≤ Real.sqrt ε := by
      apply Finset.expect_le hus
      intro u hu
      exact bounded_test_expectation_comparison (maps u) (hmaps u hu)
        (d u) (H u) ε (hd u hu) (hsecond u hu) (hH u hu)

/-- Equation (6.11): only the signal averaged over U is assumed large. -/
theorem averaged_transferred_signal_lower {U : Type*} (Map : U → Type*)
    (us : Finset U) (hus : us.Nonempty) (maps : (u : U) → Finset (Map u))
    (hmaps : ∀ u ∈ us, (maps u).Nonempty)
    (d H : (u : U) → Map u → ℝ) (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2)
    (hd : ∀ u ∈ us, (𝔼 M ∈ maps u, d u M) = 1)
    (hsecond : ∀ u ∈ us, (𝔼 M ∈ maps u, d u M ^ 2) ≤ 1 + ε)
    (hH : ∀ u ∈ us, ∀ M ∈ maps u, |H u M| ≤ 1)
    (hsignal : θ ≤ (𝔼 u ∈ us, 𝔼 M ∈ maps u, H u M)) :
    θ / 2 ≤ (𝔼 u ∈ us, 𝔼 M ∈ maps u, H u M * d u M) := by
  have hcomparison := averaged_expectation_comparison Map us hus maps hmaps d H ε
    hd hsecond hH
  have hquarter := comparison_error_le_quarter ε θ hθ hε
  have hbounds := abs_le.mp (hcomparison.trans hquarter)
  linarith

/-- Uniform finite means in the quotient-of-sums convention. -/
theorem uniform_expect_eq_sum_div_card [Fintype ι] (f : ι → ℝ) :
    (𝔼 i, f i) = (∑ i, f i) / (Fintype.card ι : ℝ) :=
  Fintype.expect_eq_sum_div_card f

end MaxCutGames.Soundness.ExpectationComparison

end OAI
