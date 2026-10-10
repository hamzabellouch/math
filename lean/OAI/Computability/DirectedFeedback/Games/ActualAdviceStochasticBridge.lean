import Mathlib
import OAI.Computability.DirectedFeedback.Games.PartnerFullSampling

namespace OAI

namespace DFVSGames.Clean.ActualAdviceStochasticBridge

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
end DFVSGames.Clean.ActualAdviceStochasticBridge

namespace DFVSGames.Soundness.LinearMapDensity

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

def pullbackMap {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (π : E →ₗ[ZMod 2] V) (B : V →ₗ[ZMod 2] R) :
    {M : E →ₗ[ZMod 2] R // π.ker ≤ M.ker} :=
  ⟨B.comp π, by
    intro x hx
    change B (π x) = 0
    change π x = 0 at hx
    rw [hx, map_zero]⟩

omit [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) R] in

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

end DFVSGames.Soundness.LinearMapDensity

namespace DFVSGames.Soundness.ExpectationComparison

open scoped BigOperators

variable {ι : Type*}

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

theorem comparison_error_le_quarter (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2) : Real.sqrt ε ≤ θ / 4 := by
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hε⟩

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

theorem transferred_signal_lower (s : Finset ι) (hs : s.Nonempty)
    (d H : ι → ℝ) (ε θ : ℝ) (hθ : 0 ≤ θ)
    (hε : ε ≤ (θ / 4) ^ 2) (hd : (𝔼 i ∈ s, d i) = 1)
    (hsecond : (𝔼 i ∈ s, d i ^ 2) ≤ 1 + ε)
    (hH : ∀ i ∈ s, |H i| ≤ 1) (hsignal : θ ≤ (𝔼 i ∈ s, H i)) :
    θ / 2 ≤ (𝔼 i ∈ s, H i * d i) := by
  have h := abs_le.mp
    (bounded_test_expectation_quarter s hs d H ε θ hθ hε hd hsecond hH)
  linarith

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

theorem uniform_expect_eq_sum_div_card [Fintype ι] (f : ι → ℝ) :
    (𝔼 i, f i) = (∑ i, f i) / (Fintype.card ι : ℝ) :=
  Fintype.expect_eq_sum_div_card f

end DFVSGames.Soundness.ExpectationComparison

namespace DFVSGames.Soundness.RepetitionUpper

def bernoulliAverage (p : Rat) : Nat → (Nat → Rat) → Rat
  | 0, f => f 0
  | n + 1, f =>
      (1 - p) * bernoulliAverage p n f +
        p * bernoulliAverage p n (fun k => f (k + 1))

theorem bernoulliAverage_scale (p c : Rat) (n : Nat) (f : Nat → Rat) :
    bernoulliAverage p n (fun k => c * f k) = c * bernoulliAverage p n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [bernoulliAverage, ih]
      grind

theorem bernoulliAverage_geometric (p a : Rat) (n : Nat) :
    bernoulliAverage p n (fun k => a ^ k) = (1 - p * (1 - a)) ^ n := by
  induction n with
  | zero => simp [bernoulliAverage]
  | succ n ih =>
      simp only [bernoulliAverage]
      have hs : (fun k : Nat => a ^ (k + 1)) = fun k => a * a ^ k := by
        funext k
        rw [Rat.pow_succ, Rat.mul_comm]
      rw [hs, bernoulliAverage_scale, ih, Rat.pow_succ]
      grind

theorem bernoulliAverage_mono (p : Rat) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : Nat) (f g : Nat → Rat) (h : ∀ k, f k ≤ g k) :
    bernoulliAverage p n f ≤ bernoulliAverage p n g := by
  induction n generalizing f g with
  | zero => exact h 0
  | succ n ih =>
      have hleft := ih f g h
      have hright := ih (fun k => f (k + 1)) (fun k => g (k + 1))
        (fun k => h (k + 1))
      have hnp : 0 ≤ 1 - p := by grind
      have hl := Rat.mul_le_mul_of_nonneg_left hleft hnp
      have hr := Rat.mul_le_mul_of_nonneg_left hright hp
      simp only [bernoulliAverage]
      grind

theorem success_le_geometric
    (p a success : Rat) (n : Nat) (conditionalSuccess : Nat → Rat)
    (hp : 0 ≤ p) (hp' : p ≤ 1)
    (conditional : ∀ k, conditionalSuccess k ≤ a ^ k)
    (averaged : success ≤ bernoulliAverage p n conditionalSuccess) :
    success ≤ (1 - p * (1 - a)) ^ n := by
  have h := bernoulliAverage_mono p hp hp' n conditionalSuccess
    (fun k => a ^ k) conditional
  rw [bernoulliAverage_geometric] at h
  exact Rat.le_trans averaged h

theorem pow_mono_nonneg (x y : Rat) (hx : 0 ≤ x) (hxy : x ≤ y) (n : Nat) :
    x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp []
  | succ n ih =>
      have hy : 0 ≤ y := Rat.le_trans hx hxy
      have hp : 0 ≤ x ^ n := Rat.pow_nonneg hx
      have h₁ := Rat.mul_le_mul_of_nonneg_left hxy hp
      have h₂ := Rat.mul_le_mul_of_nonneg_right ih hy
      simp only [Rat.pow_succ]
      exact Rat.le_trans h₁ h₂

def zeroProbability (d : Nat) : Rat := (1 / 2 : Rat) ^ d

theorem zeroProbability_nonneg (d : Nat) : 0 ≤ zeroProbability d := by
  exact Rat.pow_nonneg (by grind)

theorem zeroProbability_le_one (d : Nat) : zeroProbability d ≤ 1 := by
  induction d with
  | zero => simp [zeroProbability]
  | succ d ih =>
      have hp := zeroProbability_nonneg d
      simp only [zeroProbability, Rat.pow_succ] at *
      grind

theorem zeroProbability_antitone (d L : Nat) (hd : d ≤ L) :
    zeroProbability L ≤ zeroProbability d := by
  induction L with
  | zero =>
      have : d = 0 := by omega
      subst d
      exact Rat.le_refl
  | succ L ih =>
      by_cases heq : d = L + 1
      · subst d
        exact Rat.le_refl
      · have hdL : d ≤ L := by omega
        have h := ih hdL
        have hp := zeroProbability_nonneg L
        have hs : zeroProbability (L + 1) ≤ zeroProbability L := by
          simp only [zeroProbability, Rat.pow_succ] at *
          grind
        exact Rat.le_trans hs h

theorem geometric_le_dimension_bound (d L n : Nat) (hd : d ≤ L)
    (a : Rat) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (1 - zeroProbability d * (1 - a)) ^ n ≤
      (1 - zeroProbability L * (1 - a)) ^ n := by
  have hp := zeroProbability_nonneg d
  have hp' := zeroProbability_le_one d
  have hdL := zeroProbability_antitone d L hd
  have hna : 0 ≤ 1 - a := by grind
  have hprod := Rat.mul_le_mul_of_nonneg_right hdL hna
  have hnprod := Rat.mul_le_mul_of_nonneg_right hp' hna
  apply pow_mono_nonneg
  · grind
  · grind

theorem projection_upper_bound
    (d L n : Nat) (hd : d ≤ L) (a success : Rat)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (conditionalSuccess : Nat → Rat)
    (conditional : ∀ k, conditionalSuccess k ≤ a ^ k)
    (averaged : success ≤ bernoulliAverage (zeroProbability d) n conditionalSuccess) :
    success ≤ (1 - zeroProbability L * (1 - a)) ^ n := by
  have hs := success_le_geometric (zeroProbability d) a success n
    conditionalSuccess (zeroProbability_nonneg d) (zeroProbability_le_one d)
    conditional averaged
  exact Rat.le_trans hs (geometric_le_dimension_bound d L n hd a ha ha')

def decoderThreshold (theta : Rat) (q : Nat) : Rat := theta ^ 3 / (64 * (q : Rat))

theorem decoderThreshold_pos (theta : Rat) (q : Nat)
    (htheta : 0 < theta) (hq : 0 < q) : 0 < decoderThreshold theta q := by
  have hq' : (0 : Rat) < (q : Rat) := Rat.natCast_pos.mpr hq
  have ht := Rat.pow_pos (n := 3) htheta
  have hd : (0 : Rat) < 64 * (q : Rat) := by grind
  unfold decoderThreshold
  apply (Rat.lt_div_iff hd).mpr
  simpa using ht

theorem exists_pos_nat_gt (x : Rat) : ∃ n : Nat, 0 < n ∧ x < (n : Rat) := by
  refine ⟨x.ceil.toNat + 1, by omega, ?_⟩
  have hceil := Rat.le_ceil (x := x)
  have hint : x.ceil ≤ (x.ceil.toNat : Int) := by omega
  have hcast := Rat.intCast_le_intCast.mpr hint
  simp only [Rat.intCast_natCast] at hcast
  rw [Rat.natCast_add, Rat.natCast_ofNat]
  grind

theorem power_mul_growth_le_one (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : Rat) * (1 - b)) ≤ 1 := by
  induction n with
  | zero => simp []
  | succ n ih =>
      have hn := Rat.natCast_nonneg (a := n)
      have hc : 0 ≤ 1 - b := by grind
      have hnc : 0 ≤ ((n : Rat) + 1) * (1 - b) :=
        Rat.mul_nonneg (by grind) hc
      have hscaled := Rat.mul_le_mul_of_nonneg_right hb' hnc
      have hstep : b * (1 + ((n : Rat) + 1) * (1 - b)) ≤
          1 + (n : Rat) * (1 - b) := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hstep (Rat.pow_nonneg (n := n) hb)
      simp only [Rat.pow_succ, Rat.natCast_add, Rat.natCast_ofNat]
      grind

theorem exists_power_lt (b threshold : Rat) (hb : 0 ≤ b) (hb' : b < 1)
    (ht : 0 < threshold) : ∃ n : Nat, 0 < n ∧ b ^ n < threshold := by
  have hc : 0 < 1 - b := by grind
  have hden : 0 < threshold * (1 - b) := Rat.mul_pos ht hc
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (1 / (threshold * (1 - b)))
  refine ⟨n, hn, ?_⟩
  have hlarge' := (Rat.div_lt_iff hden).mp hlarge
  have hn' := Rat.natCast_nonneg (a := n)
  have hg : 0 ≤ 1 + (n : Rat) * (1 - b) := by
    have h := Rat.mul_nonneg hn' (Rat.le_of_lt hc)
    grind
  have hbnd := power_mul_growth_le_one b hb (Rat.le_of_lt hb') n
  apply Rat.not_le.mp
  intro hbad
  have hmul := Rat.mul_le_mul_of_nonneg_right hbad hg
  grind

theorem zeroProbability_pos (d : Nat) : 0 < zeroProbability d := by
  exact Rat.pow_pos (by grind)

theorem exists_repetition_length (L q : Nat) (a theta : Rat)
    (ha : 0 ≤ a) (ha' : a < 1) (htheta : 0 < theta) (hq : 0 < q) :
    ∃ t : Nat, 0 < t ∧
      (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q := by
  have hp := zeroProbability_pos L
  have hp' := zeroProbability_le_one L
  have hc : 0 < 1 - a := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_right hp' (Rat.le_of_lt hc)
  have hpos := Rat.mul_pos hp hc
  apply exists_power_lt
  · grind
  · grind
  · exact decoderThreshold_pos theta q htheta hq

theorem soundness_of_bounds
    {Labeling Strategy : Type} (acceptance : Labeling → Rat)
    (success : Strategy → Rat) (delta lower upperBound : Rat)
    (extraction : ∀ labeling, delta < acceptance labeling →
      ∃ strategy, lower ≤ success strategy)
    (upper : ∀ strategy, success strategy ≤ upperBound)
    (gap : upperBound < lower) :
    ∀ labeling, acceptance labeling ≤ delta := by
  intro labeling
  apply Rat.not_lt.mp
  intro hbad
  obtain ⟨strategy, hlow⟩ := extraction labeling hbad
  have h : lower ≤ upperBound := Rat.le_trans hlow (upper strategy)
  exact (Rat.not_lt.mpr h) gap

theorem soundness_from_repetition
    {Labeling Strategy : Type} (acceptance : Labeling → Rat)
    (success : Strategy → Rat) (dimension : Strategy → Nat)
    (conditionalSuccess : Strategy → Nat → Rat)
    (delta a theta : Rat) (q L t : Nat) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (dimension_le : ∀ strategy, dimension strategy ≤ L)
    (conditional : ∀ strategy k, conditionalSuccess strategy k ≤ a ^ k)
    (averaged : ∀ strategy, success strategy ≤
      bernoulliAverage (zeroProbability (dimension strategy)) t
        (conditionalSuccess strategy))
    (extraction : ∀ labeling, delta < acceptance labeling →
      ∃ strategy, decoderThreshold theta q ≤ success strategy)
    (gap : (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q) :
    ∀ labeling, acceptance labeling ≤ delta := by
  apply soundness_of_bounds acceptance success delta (decoderThreshold theta q)
    ((1 - zeroProbability L * (1 - a)) ^ t) extraction
  · intro strategy
    exact projection_upper_bound (dimension strategy) L t (dimension_le strategy)
      a (success strategy) ha ha' (conditionalSuccess strategy)
      (conditional strategy) (averaged strategy)
  · exact gap

end DFVSGames.Soundness.RepetitionUpper

end OAI
