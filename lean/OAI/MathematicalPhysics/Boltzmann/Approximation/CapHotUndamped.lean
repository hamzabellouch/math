import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLabelFreeLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCharacteristics
import OAI.MathematicalPhysics.Boltzmann.Branching.BackgroundCappedLoss
import OAI.MathematicalPhysics.Boltzmann.Branching.HotWindowGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.LinearHotLocalization
import OAI.MathematicalPhysics.Boltzmann.Branching.SpaceTimeDilationAE
import OAI.MathematicalPhysics.Boltzmann.Branching.VanishingMajorant
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeSurvival

namespace OAI

section

/-! # A single measurable hot limit from the compatible local weak limits -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.hotLimit (E : HotLimitExtraction S) (z : HotKineticPhase) : ℝ :=
  max 0 (liminf (fun j => E.profile j z) atTop)

theorem HotLimitExtraction.hotLimit_measurable (E : HotLimitExtraction S) :
    Measurable E.hotLimit :=
  measurable_const.max (Measurable.liminf (fun j => (E.weak j).1))

theorem HotLimitExtraction.hotLimit_nonneg (E : HotLimitExtraction S) (z : HotKineticPhase) :
    0 ≤ E.hotLimit z := le_max_left _ _

theorem HotLimitExtraction.hotLimit_eq_local (E : HotLimitExtraction S) (j : ℕ) :
    E.hotLimit =ᵐ[hotWindowVolume (j+1) (j+1)] E.profile j := by
  have he (k : ℕ) : ∀ᵐ z ∂hotWindowVolume (j+1) (j+1), j ≤ k → E.profile k z = E.profile j z := by
    by_cases hjk : j ≤ k
    · exact (E.compatible hjk).mono (fun _ hz _ => hz)
    · exact ae_of_all _ (fun _ h => (hjk h).elim)
  filter_upwards [ae_all_iff.mpr he,E.nonneg j] with z hz hn
  have hevent : (fun k => E.profile k z) =ᶠ[atTop] (fun _ => E.profile j z) := by
    filter_upwards [eventually_ge_atTop j] with k hk
    exact hz k hk
  have ht : Tendsto (fun k => E.profile k z) atTop (𝓝 (E.profile j z)) :=
    (tendsto_congr' hevent).mpr tendsto_const_nhds
  exact (congrArg (max (0:ℝ)) ht.liminf_eq).trans (max_eq_right hn)

theorem HotLimitExtraction.hotLimit_weak (E : HotLimitExtraction S) (A R : ℝ) :
    Published.WeakL1Converges (hotWindowVolume A R)
      (fun n => S.hotDensity (E.indices n)) E.hotLimit := by
  obtain ⟨j,hj⟩ := exists_nat_gt (max A R)
  have hA : A ≤ (j:ℝ)+1 := by have := (le_max_left A R).trans_lt hj; linarith
  have hR : R ≤ (j:ℝ)+1 := by have := (le_max_right A R).trans_lt hj; linarith
  have hjw := (E.weak j).congr_limit E.hotLimit_measurable (E.hotLimit_eq_local j).symm
  have h := hjw.restrict (hotWindowSet_measurable A R)
  rw [hotWindowVolume_restrict hA hR] at h
  exact h

theorem HotLimitExtraction.hotLimit_cap (E : HotLimitExtraction S) (A R : ℝ) :
    ∀ᵐ z ∂hotWindowVolume A R, E.hotLimit z ≤ (z.1.1+E.fraction)*H q z.2 := by
  obtain ⟨j,hj⟩ := exists_nat_gt (max A R)
  have hA : A ≤ (j:ℝ)+1 := by have := (le_max_left A R).trans_lt hj; linarith
  have hR : R ≤ (j:ℝ)+1 := by have := (le_max_right A R).trans_lt hj; linarith
  have hb : ∀ᵐ z ∂hotWindowVolume (j+1) (j+1),
      E.hotLimit z ≤ (z.1.1+E.fraction)*H q z.2 := by
    filter_upwards [E.hotLimit_eq_local j,E.cap j] with z he hc
    exact he ▸ hc
  have h := ae_restrict_of_ae (s := hotWindowSet A R) hb
  rw [hotWindowVolume_restrict hA hR] at h
  exact h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The local weak limit is a limit of the physical, unextended cap shots -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.congr_eventually {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f k : ℕ → X → ℝ} {g : X → ℝ}
    (hg : WeakL1Converges μ f g) (he : ∀ᶠ n in atTop, f n =ᵐ[μ] k n) :
    WeakL1Converges μ k g := by
  refine ⟨hg.1,hg.2.1,?_⟩
  intro ψ hψ hB
  apply (hg.2.2 ψ hψ hB).congr'
  filter_upwards [he] with n hn
  exact integral_congr_ae (hn.mono (fun x hx => congrArg (fun y => ψ x*y) hx))

end BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def physicalHotDensity (S : AttainedCapSequence F) (n : ℕ) (z : HotKineticPhase) : ℝ :=
  S.rescaledHot n (z.1.1,(z.1.2,z.2))

theorem HotLimitExtraction.physical_weak (S : AttainedCapSequence F)
    (E : HotLimitExtraction S) (hs₀ : 0 < s₀) {A : ℝ}
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges (hotWindowVolume A R)
      (fun n => S.physicalHotDensity (E.indices n)) E.hotLimit := by
  apply (E.hotLimit_weak A R).congr_eventually
  filter_upwards [S.eventually_extendedHot_eq hs₀ E.horizon_limit hA] with n hn
  filter_upwards [hotWindow_time_mem A R] with z hz
  exact hn z.1.1 hz (z.1.2,z.2)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform upper source bounds after the actual cap dilation -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledHotSource (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  (F.approximation n).hotNetSource (S.radius n*u.1,(S.radius n • u.2.1,u.2.2))

def sourceError (S : AttainedCapSequence F) (C B A : ℝ) (m n : ℕ) : ℝ :=
  C*(S.radius n)^2*(A+1)^2+B*(S.radius n)^m*A^m

theorem sourceError_tendsto (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    (C B A : ℝ) {m : ℕ} (hm : 0 < m) :
    Tendsto (S.sourceError C B A m) atTop (𝓝 0) := by
  have hr := S.radius_tendsto_zero hs₀
  have hleft := ((hr.pow 2).const_mul C).mul_const ((A+1)^2)
  have hright := ((hr.pow m).const_mul B).mul_const (A^m)
  change Tendsto (fun n => C*(S.radius n)^2*(A+1)^2+B*(S.radius n)^m*A^m) atTop (𝓝 0)
  simpa only [zero_pow (by omega : 2 ≠ 0),zero_pow (Nat.ne_zero_of_lt hm),
    mul_zero,zero_mul,add_zero] using hleft.add hright

theorem eventually_source_tail_small (F : ShrinkingCapFamily s₀ η K α γ d₀ q)
    (E : ℝ) (m : ℕ) :
    ∀ᶠ n in atTop, E*(shrinkingHorizon F.horizonScale n)^(m+1) ≤ 1 := by
  have h := ((shrinkingHorizon_tendsto_zero F.horizonScale).pow (m+1)).const_mul E
  have hzero : Tendsto (fun n => E*(shrinkingHorizon F.horizonScale n)^(m+1)) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : m+1 ≠ 0),mul_zero] using h
  exact (hzero.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ hn => hn.le)

theorem eventually_rescaledHotSource_upper (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) (m : ℕ) :
    let C := 2*HotApplication.realBound q
    let B := (2*JetMainGain.coefficient K α γ q+C)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ))
    ∀ᶠ n in atTop, ∀ᵐ u ∂WeightedLocal.spacetimeVolume, u.1 ∈ Ioc 0 A →
      S.rescaledHotSource (κ n) u ≤ 2*JetMainGain.coefficient K α γ q+
        S.sourceError C B A m (κ n) := by
  intro C B
  let E := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have hE : 0 ≤ E := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (HotApplication.realBound_pos q).le
  have hB : 0 ≤ B := mul_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q)) hC) hE
  filter_upwards [hκ.tendsto_atTop.eventually (eventually_source_tail_small F E m),
    S.eventually_scaled_slab hs₀ hU hA] with n hn hslab
  have hb := (F.approximation (κ n)).hot_net_source_cap hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    (shrinkingHorizon_pos F.horizonScale_pos _).le
    ((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le) m hn
  have hr := S.radius_pos hs₀ (κ n)
  filter_upwards [(ColdDilationMeasure.spacetime_dilation_quasiMeasurePreserving hr).ae hb]
    with u hu hut
  have hphysical := hslab u.1 ⟨hut.1.le,hut.2⟩
  have hp := hu ⟨mul_pos hr hut.1,hphysical.2⟩
  have hδ : DatumBounds.scale s₀ η (F.indices (κ n)+1) ≤ S.radius (κ n) := by
    dsimp [radius]
    linarith [(S.time_mem (κ n)).1]
  have ht : 0 ≤ S.radius (κ n)*u.1 := mul_nonneg hr.le hut.1.le
  have hlin : S.radius (κ n)*u.1+DatumBounds.scale s₀ η (F.indices (κ n)+1) ≤
      S.radius (κ n)*(A+1) := by nlinarith [mul_le_mul_of_nonneg_left hut.2 hr.le]
  have hquad := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (add_nonneg ht (DatumBounds.scale_pos hs₀ _).le) hlin 2) hC
  have htail := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ht (mul_le_mul_of_nonneg_left hut.2 hr.le) m) hB
  apply hp.trans
  simpa only [sourceError,mul_pow,mul_assoc,add_assoc,C,B,E] using
    add_le_add (add_le_add (le_rfl : 2*JetMainGain.coefficient K α γ q ≤
      2*JetMainGain.coefficient K α γ q) hquad) htail

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The exact linear mild equation of the rescaled hot component -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def normalizedHot (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  (F.approximation n).hot (S.radius n*u.1,PositiveIntegral.scalePhase (S.radius n) u.2)/S.radius n

def rescaledHotForcing (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  remainderForcing q (F.indices n+1) (damping q (F.indices n+1) (F.approximation n).amplitude)
    (F.approximation n).solution.value (F.approximation n).cold
      (S.radius n*u.1,PositiveIntegral.scalePhase (S.radius n) u.2)

theorem normalizedHot_mild (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {A : ℝ}
    (hA : S.radius n*A ≤ shrinkingHorizon F.horizonScale n) :
    ∀ t ∈ Icc 0 A, (fun p => S.normalizedHot n (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value A
        (S.radius n*damping q (F.indices n+1) (F.approximation n).amplitude) JetBarrier.flight
        (fun p => (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n)
        (S.rescaledHotForcing n) (t,p)) :=
  PositiveIntegral.mild_dilation (S.radius_pos hs₀ n) hA
    ((F.approximation n).hot_mild hs₀ hsmax hη hηmax hK hd₀ hq
      (shrinkingHorizon_pos F.horizonScale_pos n).le)

theorem normalizedHot_netSource (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    (n : ℕ) (u : ℝ × JetPrototype.Phase) :
    S.rescaledHotForcing n u-
      (S.radius n*damping q (F.indices n+1) (F.approximation n).amplitude)*S.normalizedHot n u =
        S.rescaledHotSource n u := by
  have hr := (S.radius_pos hs₀ n).ne'
  dsimp [rescaledHotForcing,normalizedHot,rescaledHotSource,CapApproximation.hotNetSource,
    CapApproximation.cold,PositiveIntegral.scalePhase]
  field_simp
  rfl

theorem rescaledHot_eq_weighted (S : AttainedCapSequence F) (n : ℕ)
    (u : ℝ × JetPrototype.Phase) :
    S.rescaledHot n u = VelocityWeight.H q u.2.2*S.normalizedHot n u := by
  dsimp [rescaledHot,normalizedHot,PositiveIntegral.scalePhase]
  ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Further extraction preserves every scale and the same global hot limit -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.subsequence (E : HotLimitExtraction S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : HotLimitExtraction S where
  fraction := E.fraction
  fraction_mem := E.fraction_mem
  phase := E.phase
  phase_mem := E.phase_mem
  horizon := E.horizon
  horizon_ge := E.horizon_ge
  indices := E.indices ∘ φ
  indices_strict := E.indices_strict.comp hφ
  fraction_limit := E.fraction_limit.comp hφ.tendsto_atTop
  phase_limit := E.phase_limit.comp hφ.tendsto_atTop
  horizon_limit := E.horizon_limit.comp hφ.tendsto_atTop
  profile := E.profile
  weak := fun j => (E.weak j).comp hφ.tendsto_atTop
  nonneg := E.nonneg
  cap := E.cap

theorem HotLimitExtraction.subsequence_hotLimit (E : HotLimitExtraction S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : (E.subsequence φ hφ).hotLimit = E.hotLimit := rfl

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual rescaled cold density, before taking its atomic limit -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.coldTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (u : ℝ × JetPrototype.Phase) : ℝ :=
  ∑' i, F.cold i u

theorem CapApproximation.coldTotal_properties {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.coldTotal ∧ ∀ u, Summable (fun i => F.cold i u) ∧
      0 ≤ F.coldTotal u ∧ F.coldTotal u ≤ F.solution.value u := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  refine ⟨Measurable.tsum hc.1,fun u => ?_⟩
  exact ⟨summable_of_sum_le (fun i => hc.2.1 i u) (fun s => hc.2.2.1 s u),
    tsum_nonneg (fun i => hc.2.1 i u),
    Real.tsum_le_of_sum_le (fun i => hc.2.1 i u) (fun s => hc.2.2.1 s u)⟩

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledColdDensity (S : AttainedCapSequence F) (n : ℕ) (z : HotKineticPhase) : ℝ :=
  S.radius n*H q z.2*(F.approximation n).coldTotal
    (S.radius n*z.1.1,(S.radius n • z.1.2,z.2))

theorem rescaledColdDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.rescaledColdDensity n) := by
  have hc := ((F.approximation n).coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).1
  have hm : Measurable (fun z : HotKineticPhase =>
      (S.radius n*z.1.1,(S.radius n • z.1.2,z.2))) := by fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd).const_mul _).mul (hc.comp hm)

theorem rescaledColdDensity_bounds (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (z : HotKineticPhase) :
    0 ≤ S.rescaledColdDensity n z ∧ S.rescaledColdDensity n z ≤
      (S.radius n*(2*(F.approximation n).amplitude))*H q z.2 := by
  have hc := ((F.approximation n).coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).2
      (S.radius n*z.1.1,(S.radius n • z.1.2,z.2))
  have hrH := mul_nonneg (S.radius_pos hs₀ n).le (H_nonneg q z.2)
  refine ⟨mul_nonneg hrH hc.2.1,?_⟩
  calc
    _ ≤ S.radius n*H q z.2*(2*(F.approximation n).amplitude) :=
      mul_le_mul_of_nonneg_left (hc.2.2.trans ((F.approximation n).solution.value_bounds _).2) hrH
    _ = _ := by ring

theorem rescaledColdDensity_integrable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    (x : ℝ × JetPrototype.Space) : Integrable (fun v => S.rescaledColdDensity n (x,v)) := by
  have hm : Measurable (fun v => S.rescaledColdDensity n (x,v)) :=
    (S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).comp
    (measurable_const.prodMk measurable_id)
  apply ((integrable_H hq).const_mul (S.radius n*(2*(F.approximation n).amplitude))).mono'
    hm.aestronglyMeasurable
  filter_upwards [] with v
  have hb := S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n (x,v)
  simpa only [Real.norm_of_nonneg hb.1] using hb.2

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual hot-limit representative and its geometric background bounds -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.cappedHot (E : HotLimitExtraction S) (z : HotKineticPhase) : ℝ :=
  min (E.hotLimit z) (max 0 (z.1.1+E.fraction)*H q z.2)

theorem HotLimitExtraction.cappedHot_measurable (E : HotLimitExtraction S) :
    Measurable E.cappedHot :=
  E.hotLimit_measurable.min ((measurable_const.max (measurable_fst.fst.add_const _)).mul
    ((ChartKernel.measurable_H q).comp measurable_snd))

theorem HotLimitExtraction.cappedHot_nonneg (E : HotLimitExtraction S) (z : HotKineticPhase) :
    0 ≤ E.cappedHot z :=
  le_min (E.hotLimit_nonneg z) (mul_nonneg (le_max_left _ _) (H_nonneg q z.2))

theorem HotLimitExtraction.cappedHot_le (E : HotLimitExtraction S)
    {t : ℝ} (ht : 0 ≤ t) (x : JetPrototype.Space) (v : Velocity) :
    E.cappedHot ((t,x),v) ≤ (t+E.fraction)*H q v := by
  have hp : 0 ≤ t+E.fraction := add_nonneg ht E.fraction_mem.1
  simpa only [cappedHot,max_eq_right hp] using
    (min_le_right (E.hotLimit ((t,x),v)) (max 0 (t+E.fraction)*H q v))

theorem HotLimitExtraction.cappedHot_eq (E : HotLimitExtraction S) (A R : ℝ) :
    E.cappedHot =ᵐ[hotWindowVolume A R] E.hotLimit := by
  filter_upwards [E.hotLimit_cap A R] with z hz
  apply min_eq_left
  exact hz.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (H_nonneg q z.2))

theorem HotLimitExtraction.cappedHot_physical_weak (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) {A : ℝ} (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges (hotWindowVolume A R)
      (fun n => S.physicalHotDensity (E.indices n)) E.cappedHot :=
  (E.physical_weak S hs₀ hA R).congr_limit E.cappedHot_measurable (E.cappedHot_eq A R).symm

def HotLimitExtraction.background (E : HotLimitExtraction S) (t : ℝ)
    (x : JetPrototype.Space) : Measure Velocity :=
  GeometricBackground.background E.phase η E.fraction K α γ t x

theorem HotLimitExtraction.background_gain_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) {t : ℝ} (ht : 0 < t)
    (hq₁ : 1 < q) (hq₂ : q < 2) (x : JetPrototype.Space) :
    ∀ᵐ v ∂volume, chartGain (E.background t x)
      (fun w => ENNReal.ofReal (E.cappedHot ((t,x),w))) v ≤
        ENNReal.ofReal (H q v)*GeometricBackground.gainCoefficient K α γ q := by
  apply GeometricBackground.capped_chartGain_ae_bound
    (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ ht hq₁ hq₂
  intro w
  simpa only [add_comm] using E.cappedHot_le ht.le x w

theorem HotLimitExtraction.background_loss_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) {t : ℝ} (ht : 0 < t)
    (x : JetPrototype.Space) (v : Velocity) :
    E.cappedHot ((t,x),v)*GeometricBackground.frequency E.phase η E.fraction K α γ t x v ≤
      GeometricBackground.lossCoefficient K α γ*(‖v‖+1+α)*H q v := by
  apply GeometricBackground.capped_loss_bound
    (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ ht
  simpa only [add_comm] using E.cappedHot_le ht.le x v

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual limiting cold--hot product kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.hotKernel (E : HotLimitExtraction S) :
    Kernel (ℝ × JetPrototype.Space) Velocity :=
  (Kernel.const _ (volume : Measure Velocity)).withDensity
    (fun x v => ENNReal.ofReal (E.cappedHot (x,v)))

instance HotLimitExtraction.hotKernel_sFinite (E : HotLimitExtraction S) :
    IsSFiniteKernel E.hotKernel :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem HotLimitExtraction.hotKernel_apply (E : HotLimitExtraction S) (x : ℝ × JetPrototype.Space) :
    E.hotKernel x = volume.withDensity (fun v => ENNReal.ofReal (E.cappedHot (x,v))) := by
  exact Kernel.withDensity_apply _ E.cappedHot_measurable.ennreal_ofReal x

theorem HotLimitExtraction.cappedHot_integrable (E : HotLimitExtraction S) (hq : q < 2)
    (x : ℝ × JetPrototype.Space) : Integrable (fun v => E.cappedHot (x,v)) := by
  have hm : Measurable (fun v => E.cappedHot (x,v)) :=
    E.cappedHot_measurable.comp (measurable_const.prodMk measurable_id)
  apply ((integrable_H hq).const_mul (max 0 (x.1+E.fraction))).mono' hm.aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (E.cappedHot_nonneg (x,v))]
  exact min_le_right _ _

theorem HotLimitExtraction.hotKernel_mass (E : HotLimitExtraction S) (hq : q < 2)
    (x : ℝ × JetPrototype.Space) :
    E.hotKernel x univ = ENNReal.ofReal (∫ v, E.cappedHot (x,v)) := by
  rw [E.hotKernel_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (E.cappedHot_integrable hq x)
    (ae_of_all _ (fun v => E.cappedHot_nonneg (x,v)))).symm

theorem HotLimitExtraction.hotKernel_mass_bound (E : HotLimitExtraction S) (hq : q < 2)
    (x : ℝ × JetPrototype.Space) :
    E.hotKernel x univ ≤ ENNReal.ofReal (max 0 (x.1+E.fraction)*(∫ v, H q v)) := by
  rw [E.hotKernel_mass hq]
  apply ENNReal.ofReal_le_ofReal
  have hb := integral_mono (E.cappedHot_integrable hq x)
    ((integrable_H hq).const_mul (max 0 (x.1+E.fraction))) (fun v => min_le_right _ _)
  simpa only [integral_const_mul] using hb

theorem HotLimitExtraction.hotKernel_finite (E : HotLimitExtraction S) (hq : q < 2)
    (x : ℝ × JetPrototype.Space) : IsFiniteMeasure (E.hotKernel x) :=
  ⟨(E.hotKernel_mass_bound hq x).trans_lt ENNReal.ofReal_lt_top⟩

def HotLimitExtraction.mixedKernel (E : HotLimitExtraction S) {a : ℝ} (ha : 0 < a)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    Kernel (ℝ × JetPrototype.Space) (Velocity × Velocity) :=
  GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1) hK hα hγ η E.fraction ×ₖ
    E.hotKernel

instance HotLimitExtraction.mixedKernel_sFinite (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    IsSFiniteKernel (E.mixedKernel ha hK hα hγ) := by
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  unfold HotLimitExtraction.mixedKernel
  infer_instance

theorem HotLimitExtraction.mixedKernel_apply (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (x : ℝ × JetPrototype.Space) :
    E.mixedKernel ha hK hα hγ x =
      (E.background (max a x.1) x.2).prod (E.hotKernel x) := by
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  exact Kernel.prod_apply _ _ x

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Finite mixed cold--hot measures on bounded spacetime windows -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotKernel_integral (E : HotLimitExtraction S)
    (x : ℝ × JetPrototype.Space) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂E.hotKernel x) = ∫ v, E.cappedHot (x,v)*ψ v := by
  rw [E.hotKernel_apply,integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [ENNReal.toReal_ofReal (E.cappedHot_nonneg _),smul_eq_mul]
  · exact (E.cappedHot_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

theorem HotLimitExtraction.mixedKernel_tensor (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (x : ℝ × JetPrototype.Space) (ψ χ : Velocity → ℝ) :
    (∫ p : Velocity × Velocity, ψ p.1*χ p.2 ∂E.mixedKernel ha hK hα hγ x) =
      (∫ p, ψ p ∂E.background (max a x.1) x.2)*(∫ v, E.cappedHot (x,v)*χ v) := by
  let _ : IsFiniteMeasure (E.background (max a x.1) x.2) :=
    GeometricBackground.background_finite E.phase η E.fraction K α γ (max a x.1) x.2
  rw [E.mixedKernel_apply,integral_prod_mul,E.hotKernel_integral]

def HotLimitExtraction.mixedMeasure (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (μ : Measure (ℝ × JetPrototype.Space)) :
    Measure ((ℝ × JetPrototype.Space) × (Velocity × Velocity)) :=
  μ ⊗ₘ E.mixedKernel ha hK hα hγ

theorem HotLimitExtraction.mixedMeasure_tensor (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (μ : Measure (ℝ × JetPrototype.Space)) [SFinite μ]
    (θ : ℝ × JetPrototype.Space → ℝ) (ψ χ : Velocity → ℝ)
    (hf : Integrable (fun z => θ z.1*(ψ z.2.1*χ z.2.2))
      (E.mixedMeasure ha hK hα hγ μ)) :
    (∫ z, θ z.1*(ψ z.2.1*χ z.2.2) ∂E.mixedMeasure ha hK hα hγ μ) =
      ∫ x, θ x*((∫ p, ψ p ∂E.background (max a x.1) x.2)*
        (∫ v, E.cappedHot (x,v)*χ v)) ∂μ := by
  rw [mixedMeasure,Measure.integral_compProd hf]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_const_mul,E.mixedKernel_tensor]

theorem HotLimitExtraction.mixedMeasure_tensor_on_slab (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (μ : Measure (ℝ × JetPrototype.Space)) [SFinite μ]
    (hμ : ∀ᵐ x ∂μ, a ≤ x.1)
    (θ : ℝ × JetPrototype.Space → ℝ) (ψ χ : Velocity → ℝ)
    (hf : Integrable (fun z => θ z.1*(ψ z.2.1*χ z.2.2))
      (E.mixedMeasure ha hK hα hγ μ)) :
    (∫ z, θ z.1*(ψ z.2.1*χ z.2.2) ∂E.mixedMeasure ha hK hα hγ μ) =
      ∫ x, θ x*((∫ p, ψ p ∂E.background x.1 x.2)*
        (∫ v, E.cappedHot (x,v)*χ v)) ∂μ := by
  rw [E.mixedMeasure_tensor ha hK hα hγ μ θ ψ χ hf]
  apply integral_congr_ae
  filter_upwards [hμ] with x hx
  rw [max_eq_right hx]

theorem HotLimitExtraction.mixedMeasure_finite (E : HotLimitExtraction S) {a A : ℝ}
    (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq : q < 2)
    (μ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x.1 ≤ A) : IsFiniteMeasure (E.mixedMeasure ha hK hα hγ μ) := by
  let κ := GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  let B := κ.bound*ENNReal.ofReal ((A+1)*(∫ v, H q v))
  have hB : B < ⊤ := ENNReal.mul_lt_top κ.bound_lt_top ENNReal.ofReal_lt_top
  have hb : ∀ᵐ x ∂μ, E.mixedKernel ha hK hα hγ x univ ≤ B := by
    filter_upwards [hμ] with x hx
    have hh : E.hotKernel x univ ≤ ENNReal.ofReal ((A+1)*(∫ v, H q v)) := by
      apply (E.hotKernel_mass_bound hq x).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg (H_nonneg q))
      apply max_le (by linarith)
      linarith [E.fraction_mem.2]
    change (κ ×ₖ E.hotKernel) x univ ≤ B
    rw [← univ_prod_univ,Kernel.prod_apply_prod]
    exact mul_le_mul' (κ.measure_le_bound x univ) hh
  constructor
  change (μ ⊗ₘ E.mixedKernel ha hK hα hγ) univ < ⊤
  rw [Measure.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  apply (lintegral_mono_ae hb).trans_lt
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hB (measure_lt_top μ univ)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Product Gaussian moment of the actual limiting mixed measure -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotKernel_gaussian_moment (E : HotLimitExtraction S)
    (x : ℝ × JetPrototype.Space) :
    (∫⁻ v, ENNReal.ofReal (weight v) ∂E.hotKernel x) =
      moment (fun v => E.cappedHot (x,v)) := by
  have hm : Measurable (fun v : Velocity => ENNReal.ofReal (E.cappedHot (x,v))) :=
    (E.cappedHot_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hw : Measurable (fun v : Velocity => ENNReal.ofReal (weight v)) := by unfold weight; fun_prop
  rw [E.hotKernel_apply,lintegral_withDensity_eq_lintegral_mul _ hm hw]
  apply lintegral_congr
  intro v
  rw [Pi.mul_apply,← ENNReal.ofReal_mul (E.cappedHot_nonneg _),mul_comm]

theorem HotLimitExtraction.mixedKernel_gaussian_moment (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (x : ℝ × JetPrototype.Space) :
    (∫⁻ p, ENNReal.ofReal (weight p.1*weight p.2) ∂E.mixedKernel ha hK hα hγ x) =
      (∫⁻ v, ENNReal.ofReal (weight v) ∂E.background (max a x.1) x.2)*
        moment (fun v => E.cappedHot (x,v)) := by
  let _ := GeometricBackground.background_finite E.phase η E.fraction K α γ (max a x.1) x.2
  have hw : Measurable (fun v : Velocity => ENNReal.ofReal (weight v)) := by unfold weight; fun_prop
  rw [E.mixedKernel_apply]
  simp_rw [ENNReal.ofReal_mul (weight_pos _).le]
  rw [lintegral_prod_mul hw.aemeasurable hw.aemeasurable,E.hotKernel_gaussian_moment]

theorem HotLimitExtraction.mixedMeasure_gaussian_bound (E : HotLimitExtraction S)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) (ρ : Measure (ℝ × JetPrototype.Space)) [SFinite ρ]
    (ht : ∀ᵐ x ∂ρ, x.1 ≤ A) :
    (∫⁻ z, ENNReal.ofReal (weight z.2.1*weight z.2.2)
      ∂E.mixedMeasure ha hK hα hγ ρ) ≤
      ENNReal.ofReal ((2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))*
        Real.exp ((1+α)^2/2))*((A+1)*hotConstant q))*ρ univ := by
  rw [mixedMeasure,Measure.lintegral_compProd (by unfold weight; fun_prop)]
  calc
    _ ≤ ∫⁻ _x : ℝ × JetPrototype.Space, ENNReal.ofReal (2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))*
        Real.exp ((1+α)^2/2))*ENNReal.ofReal ((A+1)*hotConstant q) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [ht] with x hx
      rw [E.mixedKernel_gaussian_moment ha hK hα hγ]
      apply mul_le_mul'
      · apply (GeometricBackground.gaussian_moment_bound
          (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ
          (ha.trans_le (le_max_left a x.1)) x.2).trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha
          (by linarith [le_max_left a x.1,E.fraction_mem.1])
      · apply (moment_mono (fun v => min_le_right _ _)).trans
        rw [hot_moment hq (le_max_left 0 (x.1+E.fraction))]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (hotConstant_nonneg q)
        exact max_le (by linarith) (by linarith [E.fraction_mem.2])
    _ = _ := by
      rw [lintegral_const,← ENNReal.ofReal_mul]
      exact mul_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
          (div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha.le)))
        (Real.exp_pos _).le

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Velocity kernels of the actual rescaled cold approximations -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def coldKernel (S : AttainedCapSequence F) (n : ℕ) :
    Kernel (ℝ × JetPrototype.Space) Velocity :=
  (Kernel.const _ (volume : Measure Velocity)).withDensity
    (fun x v => ENNReal.ofReal (S.rescaledColdDensity n (x,v)))

instance coldKernel_sFinite (S : AttainedCapSequence F) (n : ℕ) :
    IsSFiniteKernel (S.coldKernel n) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem coldKernel_apply (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (x : ℝ × JetPrototype.Space) :
    S.coldKernel n x = volume.withDensity (fun v => ENNReal.ofReal (S.rescaledColdDensity n (x,v))) :=
  Kernel.withDensity_apply _
    (S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).ennreal_ofReal x

theorem coldKernel_integral (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    (x : ℝ × JetPrototype.Space) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂S.coldKernel n x) = ∫ v, S.rescaledColdDensity n (x,v)*ψ v := by
  rw [S.coldKernel_apply hs₀ hsmax hη hηmax hK hd₀ hq n x,
    integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [ENNReal.toReal_ofReal (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n _).1,
      smul_eq_mul]
  · exact ((S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

theorem coldKernel_mass (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (x : ℝ × JetPrototype.Space) :
    S.coldKernel n x univ = ENNReal.ofReal (∫ v, S.rescaledColdDensity n (x,v)) := by
  rw [S.coldKernel_apply hs₀ hsmax hη hηmax hK hd₀ hq n x,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal
    (S.rescaledColdDensity_integrable hs₀ hsmax hη hηmax hK hd₀ hq n x)
    (ae_of_all _ (fun v => (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n (x,v)).1))).symm

theorem coldKernel_finite (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    IsFiniteKernel (S.coldKernel n) := by
  let B := (S.radius n*(2*(F.approximation n).amplitude))*(∫ v, H q v)
  refine ⟨⟨ENNReal.ofReal B,ENNReal.ofReal_lt_top,fun x => ?_⟩⟩
  rw [S.coldKernel_mass hs₀ hsmax hη hηmax hK hd₀ hq n x]
  apply ENNReal.ofReal_le_ofReal
  have hb := integral_mono
    (S.rescaledColdDensity_integrable hs₀ hsmax hη hηmax hK hd₀ hq n x)
    ((integrable_H hq).const_mul (S.radius n*(2*(F.approximation n).amplitude)))
    (fun v => (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n (x,v)).2)
  simpa only [integral_const_mul] using hb

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The mixed-cold source becomes small under the cap dilation -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledColdSource (S : AttainedCapSequence F) (n : ℕ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  (F.approximation n).coldSource (S.radius n*u.1,(S.radius n • u.2.1,u.2.2))

theorem eventually_rescaledColdSource_bound (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) (m : ℕ) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ))
    ∀ᶠ n in atTop, ∀ᵐ u ∂WeightedLocal.spacetimeVolume, u.1 ∈ Ioc 0 A →
      0 ≤ S.rescaledColdSource (κ n) u ∧
        S.rescaledColdSource (κ n) u ≤ B*(S.radius (κ n))^m*A^m := by
  intro B
  let E := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have hE : 0 ≤ E := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  have hB : 0 ≤ B := mul_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q))
      (mul_nonneg (by norm_num) (HotApplication.realBound_pos q).le)) hE
  filter_upwards [hκ.tendsto_atTop.eventually (eventually_source_tail_small F E m),
    S.eventually_scaled_slab hs₀ hU hA] with n hn hslab
  have hb := (F.approximation (κ n)).cold_source_bound hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    (shrinkingHorizon_pos F.horizonScale_pos _).le
    ((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le) m hn
  have hr := S.radius_pos hs₀ (κ n)
  filter_upwards [(ColdDilationMeasure.spacetime_dilation_quasiMeasurePreserving hr).ae hb]
    with u hu hut
  have hp := hu ⟨mul_pos hr hut.1,(hslab u.1 ⟨hut.1.le,hut.2⟩).2⟩
  refine ⟨hp.1,hp.2.trans ?_⟩
  have hpow := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_nonneg hr.le hut.1.le)
      (mul_le_mul_of_nonneg_left hut.2 hr.le) m) hB
  simpa only [B,E,mul_pow,mul_assoc] using hpow

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual mixed-cold source vanishes in local spacetime L1 -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def coldSourceDensity (S : AttainedCapSequence F) (a A : ℝ) (n : ℕ)
    (z : HotKineticPhase) : ℝ :=
  {z : HotKineticPhase | z.1.1 ∈ Icc a A}.indicator
    (fun z => H q z.2*S.rescaledColdSource n (z.1.1,(z.1.2,z.2))) z

theorem coldSourceDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (a A : ℝ) (n : ℕ) :
    Measurable (S.coldSourceDensity a A n) := by
  have hm := (F.approximation n).coldSource_measurable hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le
  exact (((ChartKernel.measurable_H q).comp measurable_snd).mul
    (hm.comp (by fun_prop))).indicator (measurableSet_Icc.preimage measurable_fst.fst)

theorem eventually_coldSourceDensity_bound (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) (R : ℝ) (m : ℕ) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ))
    ∀ᶠ n in atTop, ∀ᵐ z ∂hotWindowVolume A R,
      |S.coldSourceDensity a A (κ n) z| ≤ B*(S.radius (κ n))^m*A^m*H q z.2 := by
  intro B
  have hB : 0 ≤ B := mul_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q))
      (mul_nonneg (by norm_num) (HotApplication.realBound_pos q).le))
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)
  filter_upwards [S.eventually_rescaledColdSource_bound hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU hA m] with n hn
  have hg : ∀ᵐ z ∂(volume : Measure HotKineticPhase), z.1.1 ∈ Ioc 0 A →
      0 ≤ S.rescaledColdSource (κ n) (z.1.1,(z.1.2,z.2)) ∧
        S.rescaledColdSource (κ n) (z.1.1,(z.1.2,z.2)) ≤ B*(S.radius (κ n))^m*A^m := by
    have hh := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure JetPrototype.Space)
      (volume : Measure Velocity)).quasiMeasurePreserving.ae hn
    change ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure JetPrototype.Space)).prod
      (volume : Measure Velocity), z.1.1 ∈ Ioc 0 A →
        0 ≤ S.rescaledColdSource (κ n) (z.1.1,(z.1.2,z.2)) ∧
          S.rescaledColdSource (κ n) (z.1.1,(z.1.2,z.2)) ≤ B*(S.radius (κ n))^m*A^m at hh
    simpa only [Measure.volume_eq_prod] using hh
  rw [hotWindowVolume_eq]
  filter_upwards [hg.filter_mono ae_restrict_le] with z hz
  by_cases ht : z.1.1 ∈ Icc a A
  · have hp := hz ⟨ha.trans_le ht.1,ht.2⟩
    rw [coldSourceDensity,indicator_of_mem
      (show z ∈ {z : HotKineticPhase | z.1.1 ∈ Icc a A} from ht),
      abs_mul,abs_of_nonneg (H_nonneg q z.2),abs_of_nonneg hp.1]
    exact (mul_le_mul_of_nonneg_left hp.2 (H_nonneg q z.2)).trans_eq (mul_comm _ _)
  · rw [coldSourceDensity,indicator_of_notMem
      (show z ∉ {z : HotKineticPhase | z.1.1 ∈ Icc a A} from ht),abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hB
      (pow_nonneg (S.radius_pos hs₀ _).le _)) (pow_nonneg (ha.le.trans haA) _)) (H_nonneg q z.2)

theorem coldSourceDensity_tendsto_zero (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) (R : ℝ) :
    Tendsto (fun n => eLpNorm (S.coldSourceDensity a A (κ n)) 1 (hotWindowVolume A R))
      atTop (𝓝 0) := by
  let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
    JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
  have hi : Integrable (fun z : HotKineticPhase => H q z.2) (hotWindowVolume A R) := by
    unfold hotWindowVolume
    have : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict
        (Metric.closedBall 0 R)) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
    exact (integrable_H hq₂).comp_snd _
  apply Compactness.tendsto_L1_of_vanishing_majorant
    (fun n => (S.coldSourceDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ a A _).aestronglyMeasurable)
    ((ChartKernel.measurable_H q).comp measurable_snd) hi (ae_of_all _ (fun z => H_nonneg q z.2))
    (c := fun n => B*S.radius (κ n)*A)
  · simpa only [Function.comp_def,mul_zero,zero_mul] using
      (((S.radius_tendsto_zero hs₀).comp hκ.tendsto_atTop).const_mul B).mul_const A
  · simpa only [B,Function.comp_def,pow_one,Nat.reduceAdd] using S.eventually_coldSourceDensity_bound hcarleman hs₀ hsmax
      hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA R 1

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Regularity needed to localize the actual rescaled hot mild equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.hotInitial_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) : Measurable F.hotInitial := by
  unfold hotInitial initial
  exact ((measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q _).const_mul F.coefficient)).sub
    (Measurable.tsum (measurable_color s₀ η K α γ d₀ q N))

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem normalizedHot_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.normalizedHot n) := by
  have hm := ((F.approximation n).hot_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).1
  exact (hm.comp (by unfold PositiveIntegral.scalePhase; fun_prop)).div_const _

theorem rescaledHotForcing_properties (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.rescaledHotForcing n) ∧
      ∃ B : ℝ, ∀ u, |S.rescaledHotForcing n u| ≤ B := by
  let Fn := F.approximation n
  have hc := Fn.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le
  have hb := family_hot_bounds hq (by positivity : 0 ≤ (F.indices n+1:ℝ))
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) Fn.amplitude_pos.le) le_rfl
    Fn.solution.measurable_value hc.1 Fn.solution.value_bounds hc.2.1 hc.2.2.1
  refine ⟨hb.2.2.1.comp (by unfold PositiveIntegral.scalePhase; fun_prop),
    HotApplication.realBound q*(2*Fn.amplitude)^2+
      damping q (F.indices n+1) Fn.amplitude*(2*Fn.amplitude),fun u => ?_⟩
  change |remainderForcing q (F.indices n+1) _ Fn.solution.value Fn.cold
    (S.radius n*u.1,PositiveIntegral.scalePhase (S.radius n) u.2)| ≤ _
  have hp := hb.2.2.2 (S.radius n*u.1,PositiveIntegral.scalePhase (S.radius n) u.2)
  exact (abs_of_nonneg hp.1).le.trans hp.2

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual rescaled hot solutions have the GLPS resolvent representation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def euclideanHot (S : AttainedCapSequence F) (n : ℕ) : Published.KineticPhase → ℝ :=
  EuclideanFlight.density q (S.normalizedHot n)

def euclideanHotSource (S : AttainedCapSequence F) (n : ℕ) (z : Published.KineticPhase) : ℝ :=
  H q z.2*S.rescaledHotSource n (z.1.1,EuclideanFlight.phaseEquiv (z.1.2,z.2))

theorem euclideanHotSource_eq (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (n : ℕ) :
    EuclideanFlight.linearSource q
      (S.radius n*damping q (F.indices n+1) (F.approximation n).amplitude)
      (S.normalizedHot n) (S.rescaledHotForcing n) = S.euclideanHotSource n := by
  funext z
  exact congrArg (fun a : ℝ => H q z.2*a)
    (S.normalizedHot_netSource hs₀ n (z.1.1,EuclideanFlight.phaseEquiv (z.1.2,z.2)))

theorem hot_resolvent (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {A t : ℝ}
    (hA : S.radius n*A ≤ shrinkingHorizon F.horizonScale n) (ht : t ∈ Icc 0 A)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ ((t,p.1),p.2)*S.euclideanHot n ((t,p.1),p.2) =
        Published.transportResolvent
          (localizedSource A χ (S.euclideanHot n) (S.euclideanHotSource n)) ((t,p.1),p.2) := by
  have hRt := (mul_le_mul_of_nonneg_left ht.2 (S.radius_pos hs₀ n).le).trans hA
  have hm := S.normalizedHot_mild hs₀ hsmax hη hηmax hK hd₀ hq n hRt
  have hfm := S.normalizedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  obtain ⟨hgm,B,hB⟩ := S.rescaledHotForcing_properties hs₀ hsmax hη hηmax hK hd₀ hq n
  have hi : Measurable (fun p =>
      (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n) :=
    (((F.approximation n).hotInitial_measurable).comp
      (by unfold PositiveIntegral.scalePhase; fun_prop)).div_const _
  have he := EuclideanFlight.linear_resolvent (q := q) ht.1 ht.2 hi hfm hgm hB hm hχ hzero
  simpa only [euclideanHot,S.euclideanHotSource_eq hs₀ n] using he

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The same weak hot density in the Euclidean averaging coordinates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotChart : Published.KineticPhase ≃ᵐ JetCopyDatum.AttainedCapSequence.HotKineticPhase :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) spaceEquiv)
    (MeasurableEquiv.refl Velocity)

def hotBaseVolume (A R : ℝ) : Measure Published.SpaceTime :=
  (volume.restrict (Icc (0:ℝ) A)).prod
    (volume.restrict (spaceEquiv ⁻¹' Metric.closedBall (0 : JetPrototype.Space) R))

theorem hotChart_measurePreserving (A R : ℝ) : MeasurePreserving hotChart
    ((hotBaseVolume A R).prod volume) (JetCopyDatum.AttainedCapSequence.hotWindowVolume A R) := by
  have hs : MeasurePreserving spaceEquiv (volume : Measure Velocity) volume := by
    convert JetPeriodicDatum.spatialMap_measurePreserving using 1
    funext x
    exact spaceEquiv_apply x
  exact ((MeasurePreserving.id (volume.restrict (Icc (0:ℝ) A))).prod
    (hs.restrict_preimage measurableSet_closedBall)).prod (MeasurePreserving.id volume)

end BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem euclideanHot_eq_chart (S : AttainedCapSequence F) (n : ℕ) :
    S.euclideanHot n = S.physicalHotDensity n ∘ EuclideanFlight.hotChart := by
  funext z
  change VelocityWeight.H q z.2 *
      ((F.approximation n).hot (S.radius n*z.1.1,
        S.radius n • EuclideanFlight.spaceEquiv z.1.2,z.2)/S.radius n) =
    VelocityWeight.H q z.2 *
      (F.approximation n).hot (S.radius n*z.1.1,
        S.radius n • EuclideanFlight.spaceEquiv z.1.2,z.2)/S.radius n
  ring

theorem physicalHotDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.physicalHotDensity n) :=
  (S.rescaledHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

theorem HotLimitExtraction.euclidean_weak (S : AttainedCapSequence F)
    (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ}
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges ((EuclideanFlight.hotBaseVolume A R).prod volume)
      (fun n => S.euclideanHot (E.indices n)) (E.hotLimit ∘ EuclideanFlight.hotChart) := by
  have h := (E.physical_weak S hs₀ hA R).comp_measurableEquiv EuclideanFlight.hotChart
    (EuclideanFlight.hotChart_measurePreserving A R)
    (fun n => S.physicalHotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq _)
  simpa only [euclideanHot_eq_chart] using h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weak limits of the actual hot velocity averages -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_euclideanHot_integrable (S : AttainedCapSequence F)
    (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ}
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    ∀ᶠ n in atTop, Integrable (S.euclideanHot (E.indices n))
      ((EuclideanFlight.hotBaseVolume A R).prod volume) := by
  have hui := S.hotDensity_uniformIntegrable hs₀ hsmax hη hηmax hK hd₀ hq A R
  filter_upwards [S.eventually_extendedHot_eq hs₀ E.horizon_limit hA] with n hn
  have hi : Integrable (S.hotDensity (E.indices n)) (hotWindowVolume A R) :=
    memLp_one_iff_integrable.mp (hui.memLp (E.indices n))
  have he : S.hotDensity (E.indices n) =ᵐ[hotWindowVolume A R]
      S.physicalHotDensity (E.indices n) := by
    filter_upwards [hotWindow_time_mem A R] with z hz
    exact hn z.1.1 hz (z.1.2,z.2)
  have hp := (EuclideanFlight.hotChart_measurePreserving A R).integrable_comp_of_integrable
    (hi.congr he)
  simpa only [euclideanHot_eq_chart] using hp

theorem HotLimitExtraction.average_weak (S : AttainedCapSequence F)
    (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A : ℝ}
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ)
    {χ : Published.KineticPhase → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Published.WeakL1Converges (EuclideanFlight.hotBaseVolume A R)
      (fun n z => ∫ v, ψ v*(χ (z,v)*S.euclideanHot (E.indices n) (z,v)))
      (fun z => ∫ v, ψ v*(χ (z,v)*E.hotLimit (EuclideanFlight.hotChart (z,v)))) := by
  have : SFinite (EuclideanFlight.hotBaseVolume A R) := by
    unfold EuclideanFlight.hotBaseVolume
    infer_instance
  obtain ⟨C,hC⟩ := hχ.bounded_above_of_compact_support hc
  obtain ⟨D,hD⟩ := hψ.bounded_above_of_compact_support hψc
  have hm : Measurable (fun z : Published.KineticPhase => ψ z.2*χ z) :=
    (hψ.measurable.comp measurable_snd).mul hχ.measurable
  have hb (z : Published.KineticPhase) : |ψ z.2*χ z| ≤ |D| * |C| := by
    rw [abs_mul]
    exact mul_le_mul ((hD z.2).trans (le_abs_self D)) ((hC z).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  have h := (E.euclidean_weak S hs₀ hsmax hη hηmax hK hd₀ hq hA R).marginal_eventually
    (S.eventually_euclideanHot_integrable E hs₀ hsmax hη hηmax hK hd₀ hq hA R) hm
    (|D| * |C|) hb
  simpa only [mul_assoc,Function.comp_apply] using h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual rescaled hot solution satisfies the undamped source formula -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem normalizedHot_undamped (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hT : S.radius n*t ≤ shrinkingHorizon F.horizonScale n) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      S.normalizedHot n (t,JetBarrier.flight t p) =
        (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n+
        ∫ s in 0..t, S.rescaledHotSource n (s,JetBarrier.flight s p) := by
  have hm := S.normalizedHot_mild hs₀ hsmax hη hηmax hK hd₀ hq n hT
  have hfm := S.normalizedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  obtain ⟨hgm,B,hB⟩ := S.rescaledHotForcing_properties hs₀ hsmax hη hηmax hK hd₀ hq n
  have hi : Measurable (fun p =>
      (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n) :=
    (((F.approximation n).hotInitial_measurable).comp
      (by unfold PositiveIntegral.scalePhase; fun_prop)).div_const _
  have hh := PositiveIntegral.undamped_characteristic ht hi hfm hgm hB hm
  simpa only [S.normalizedHot_netSource hs₀ n] using hh

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
