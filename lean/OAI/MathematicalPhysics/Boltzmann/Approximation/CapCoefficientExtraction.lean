import OAI.MathematicalPhysics.Boltzmann.Approximation.CapActualLossDensity
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLimitTransport
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLabelFreeLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLocalAdmissibility
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMixedPositiveBound
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapNonlinearHotLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffLossFrequency
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveEndpointHistory
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.HotRatioCollisionTrace
import OAI.MathematicalPhysics.Boltzmann.Branching.MainPositiveRemainderBound
import OAI.MathematicalPhysics.Boltzmann.Branching.NormalGainMeasureActions
import OAI.MathematicalPhysics.Boltzmann.Branching.TightCapFamily
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedCoreSelection

namespace OAI

section

/-! # The actual normalized source is bounded by the positive main action -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def euclideanColdSource (S : AttainedCapSequence F) (n : ℕ) (z : KineticPhase) : ℝ :=
  S.rescaledColdSource n (EuclideanFlight.kineticMap z)

theorem euclideanColdSource_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.euclideanColdSource n) := by
  have hm := (F.approximation n).coldSource_measurable hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le
  have hr : Measurable (fun u : ℝ × JetPrototype.Phase =>
      (S.radius n*u.1,(S.radius n • u.2.1,u.2.2))) := by fun_prop
  exact (hm.comp hr).comp EuclideanFlight.kineticMap_measurePreserving.measurable

theorem normalizedHotSource_le_positive_at (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (n : ℕ) {t : ℝ}
    (ht : S.radius n*t ∈ Ioc 0 (shrinkingHorizon F.horizonScale n)) (htmax : t ≤ 1) :
    ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.euclideanHotSource n ((t,p.1),p.2)/H q p.2) ≤
        (ChartKernel.action (positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n))
          (fun z => ENNReal.ofReal (S.boundedHotRatio n z)) ((t,p.1),p.2)+
          4*(ENNReal.ofReal (S.radius n)*coldGainErrorConstant s₀ η K α d₀ q))+
        ENNReal.ofReal ((S.radius n)^2*(4*HotApplication.realBound q))+
        ENNReal.ofReal (S.euclideanColdSource n ((t,p.1),p.2)) := by
  let J := positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n)
  let f := S.boundedHotRatio n
  have hf : Measurable f := S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ n
  have hleft : Measurable (fun p : Velocity × Velocity =>
      ENNReal.ofReal (S.euclideanHotSource n ((t,p.1),p.2)/H q p.2)) :=
    (((S.euclideanHotSource_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ n).comp
      (by fun_prop)).div ((ChartKernel.measurable_H q).comp measurable_snd)).ennreal_ofReal
  have hright : Measurable (fun p : Velocity × Velocity =>
      (ChartKernel.action J (fun z => ENNReal.ofReal (f z)) ((t,p.1),p.2)+
        4*(ENNReal.ofReal (S.radius n)*coldGainErrorConstant s₀ η K α d₀ q))+
      ENNReal.ofReal ((S.radius n)^2*(4*HotApplication.realBound q))+
      ENNReal.ofReal (S.euclideanColdSource n ((t,p.1),p.2))) := by
    apply Measurable.add
    · exact (((ChartKernel.action_measurable J hf.ennreal_ofReal).comp
        (by fun_prop)).add measurable_const).add measurable_const
    · exact ((S.euclideanColdSource_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ n).comp
        (by fun_prop)).ennreal_ofReal
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hleft hright)).mpr
  have htrace := S.boundedHotRatio_collision_trace hs₀ hsmax hη hηmax hK hd₀.le hq₂ n
    ⟨ht.1.le,ht.2⟩ htmax
  rw [Measure.volume_eq_prod] at htrace
  filter_upwards [ae_ae_of_ae_prod htrace] with x hxtrace
  have hm := (F.approximation n).normalized_mixed_gain_le_positive hcarleman
    (S.radius_pos hs₀ n) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂
    (shrinkingHorizon_pos F.horizonScale_pos n).le
    ((shrinkingHorizon_le F.horizonScale_pos n).trans F.horizonScale_le) (t,x) ht
    (F.indices n+1) hf (fun z => (S.boundedHotRatio_bounds n z).1)
    (fun z => (S.boundedHotRatio_bounds n z).2)
  have hg := normalized_cutoff_hot_gain_bound hcarleman hq₁ hq₂ (F.indices n+1) hf
    (fun z => (S.boundedHotRatio_bounds n z).1) (fun z => (S.boundedHotRatio_bounds n z).2) (t,x)
  filter_upwards [hxtrace,hm,hg,HotRepresentative.ae_good hcarleman hq₁ hq₂] with v he hm hg hv
  have hu := S.normalizedHotSource_le_gains hs₀ hsmax hη hηmax hK hd₀.le hq₂ n ((t,x),v) hv
  rw [← he.1,← he.2] at hu
  have hu' := hu.trans (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hg (sq_nonneg (S.radius n)))) le_rfl)
  apply (ENNReal.ofReal_le_ofReal hu').trans
  apply (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)).trans
  exact add_le_add (add_le_add hm le_rfl) le_rfl

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual positive source inequality on each admissible time slab -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem normalizedHotSource_le_positive_slab (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (n : ℕ) {A : ℝ}
    (hA : S.radius n*A ≤ shrinkingHorizon F.horizonScale n) (hAmax : A ≤ 1) :
    ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 A →
      ENNReal.ofReal (S.euclideanHotSource n z/H q z.2) ≤
        (ChartKernel.action (positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n))
          (fun w => ENNReal.ofReal (S.boundedHotRatio n w)) z+
          4*(ENNReal.ofReal (S.radius n)*coldGainErrorConstant s₀ η K α d₀ q))+
        ENNReal.ofReal ((S.radius n)^2*(4*HotApplication.realBound q))+
        ENNReal.ofReal (S.euclideanColdSource n z) := by
  let J := positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n)
  have hf := S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ n
  have hl : Measurable (fun z => ENNReal.ofReal (S.euclideanHotSource n z/H q z.2)) :=
    ((S.euclideanHotSource_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ n).div
      ((ChartKernel.measurable_H q).comp measurable_snd)).ennreal_ofReal
  have hr : Measurable (fun z => (ChartKernel.action J
      (fun w => ENNReal.ofReal (S.boundedHotRatio n w)) z+
        4*(ENNReal.ofReal (S.radius n)*coldGainErrorConstant s₀ η K α d₀ q))+
      ENNReal.ofReal ((S.radius n)^2*(4*HotApplication.realBound q))+
      ENNReal.ofReal (S.euclideanColdSource n z)) :=
    (((ChartKernel.action_measurable J hf.ennreal_ofReal).add measurable_const).add
      measurable_const).add
      (S.euclideanColdSource_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ n).ennreal_ofReal
  apply KineticTraceAE.of_traces ((measurableSet_Ioc.preimage measurable_fst.fst).imp
    (measurableSet_le hl hr))
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t ∈ Ioc 0 A
  · have hrt : S.radius n*t ∈ Ioc 0 (shrinkingHorizon F.horizonScale n) :=
      ⟨mul_pos (S.radius_pos hs₀ n) ht.1,
        (mul_le_mul_of_nonneg_left ht.2 (S.radius_pos hs₀ n).le).trans hA⟩
    filter_upwards [S.normalizedHotSource_le_positive_at hcarleman hs₀ hsmax hη hηmax hK
      hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ n hrt (ht.2.trans hAmax)] with p hp _
    exact hp
  · exact Filter.Eventually.of_forall (fun _ hp => (ht hp).elim)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A vanishing uniform error in the actual positive source inequality -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def positiveSourceError (S : AttainedCapSequence F) (B A : ℝ) (n : ℕ) : ℝ≥0∞ :=
  4*(ENNReal.ofReal (S.radius n)*coldGainErrorConstant s₀ η K α d₀ q)+
    ENNReal.ofReal ((S.radius n)^2*(4*HotApplication.realBound q))+
    ENNReal.ofReal (B*S.radius n*A)

theorem positiveSourceError_tendsto_zero (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    (B A : ℝ) {κ : ℕ → ℕ} (hκ : StrictMono κ) :
    Tendsto (fun n => S.positiveSourceError B A (κ n)) atTop (𝓝 0) := by
  have hr := (S.radius_tendsto_zero hs₀).comp hκ.tendsto_atTop
  have hc := cold_gain_error_tendsto_zero hr s₀ η K α d₀ q
  have hq := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (CollisionCompactness.quadratic_hot_error_tendsto_zero hr q)
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hr.const_mul B).mul_const A)
  simpa only [positiveSourceError,Function.comp_def,ENNReal.ofReal_zero,mul_zero,zero_mul,zero_add]
    using (hc.add hq).add he

theorem eventually_euclideanColdSource_bound (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 A →
      0 ≤ S.euclideanColdSource (κ n) z ∧ S.euclideanColdSource (κ n) z ≤ B*S.radius (κ n)*A := by
  intro B
  filter_upwards [S.eventually_rescaledColdSource_bound hcarleman hs₀ hsmax hη hηmax hK
    hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hκ hU hA 1] with n hn
  filter_upwards [EuclideanFlight.kineticMap_measurePreserving.quasiMeasurePreserving.ae hn] with z hz ht
  simpa only [euclideanColdSource,EuclideanFlight.kineticMap,pow_one,Nat.reduceAdd] using hz ht

theorem eventually_normalizedHotSource_le_positive (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ENNReal.ofReal A < U) (hAmax : A ≤ 1) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 A →
      ENNReal.ofReal (S.euclideanHotSource (κ n) z/H q z.2) ≤
        ChartKernel.action (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
          (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) z+S.positiveSourceError B A (κ n) := by
  intro B
  filter_upwards [S.eventually_euclideanColdSource_bound hcarleman hs₀ hsmax hη hηmax hK
    hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hκ hU hA,S.eventually_scaled_slab hs₀ hU hA] with n hc ht
  have hp := S.normalizedHotSource_le_positive_slab hcarleman hs₀ hsmax hη hηmax hK hα.le
    hαmax hγ.le hd₀ hdmax hsmall hq₁ hq₂ (κ n) (ht A ⟨hA0,le_rfl⟩).2 hAmax
  filter_upwards [hc,hp] with z hc hp hz
  have he := (hp hz).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hc hz).2))
  simpa only [positiveSourceError,add_assoc] using he

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # One positive Volterra step for the actual attained-cap solution -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem normalizedHot_positive_mild (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {a t : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (hT : S.radius n*t ≤ shrinkingHorizon F.horizonScale n)
    (δ : ℝ≥0∞)
    (hsrc : ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 t →
      ENNReal.ofReal (S.euclideanHotSource n z/H q z.2) ≤
        ChartKernel.action (positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n))
          (fun w => ENNReal.ofReal (S.boundedHotRatio n w)) z+δ) :
    ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.euclideanHot n ((t,p.1),p.2)/H q p.2) ≤
        ENNReal.ofReal (a+S.coldFraction n)+
          (PositiveIteration.step a
            (positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n))
            (fun w => ENNReal.ofReal (S.boundedHotRatio n w)) ((t,p.1),p.2)+δ*ENNReal.ofReal (t-a)) := by
  let J := positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n)
  have hf := (S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).ennreal_ofReal
  have hsrc' : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Velocity)).prod volume,
      z.1.1 ∈ Ioc 0 t →
      ENNReal.ofReal (S.euclideanHotSource n z/H q z.2) ≤
        ChartKernel.action J (fun w => ENNReal.ofReal (S.boundedHotRatio n w)) z+δ := by
    simpa only [Measure.volume_eq_prod] using hsrc
  have hpull := (PositiveIteration.backward_measurePreserving t volume).quasiMeasurePreserving.ae hsrc'
  have hs := ae_ae_of_ae_prod ((measurePreserving_swap (μ := (volume : Measure (Velocity × Velocity)))
    (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hpull)
  have hba := S.normalizedHot_backward_between hs₀ hsmax hη hηmax hK hd₀ hq n ha hat hT
  have hi := S.normalizedHot_backward_source_integrable hs₀ hsmax hη hηmax hK hd₀ hq n
    (ha.trans hat) hT
  have hcap := S.normalizedHot_cap_backward hs₀ hsmax hη hηmax hK hd₀ hq n
    ⟨mul_nonneg (S.radius_pos hs₀ n).le ha,
      (mul_le_mul_of_nonneg_left hat (S.radius_pos hs₀ n).le).trans hT⟩ t
  filter_upwards [hs,hba,hi,hcap] with p hs hb hi hc
  have hs' : ∀ᵐ s ∂volume.restrict (Ioc a t),
      ENNReal.ofReal (S.euclideanHotSource n (PositiveIteration.flight ((t,p.1),p.2) s)/H q p.2) ≤
        ChartKernel.action J (fun w => ENNReal.ofReal (S.boundedHotRatio n w))
          (PositiveIteration.flight ((t,p.1),p.2) s)+δ := by
    filter_upwards [ae_restrict_of_ae hs,ae_restrict_mem measurableSet_Ioc] with s hs hst
    exact hs ⟨lt_of_le_of_lt ha hst.1,hst.2⟩
  have hi' := hi.mono_set (show uIcc a t ⊆ uIcc 0 t by
    rw [uIcc_of_le hat,uIcc_of_le (ha.trans hat)]
    exact Icc_subset_Icc ha le_rfl)
  rw [hb]
  exact (PositiveIteration.step_source_upper hat J hf p hi' δ hs').trans
    (add_le_add (ENNReal.ofReal_le_ofReal hc) le_rfl)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual positive mild bound has a uniform vanishing error -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_boundedHotRatio_positive_mild (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 ≤ a) (hA0 : 0 ≤ A) (hA : ENNReal.ofReal A < U) (hAmax : A ≤ 1) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ t ∈ Icc a A, ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.boundedHotRatio (κ n) ((t,p.1),p.2)) ≤
        ENNReal.ofReal (a+S.coldFraction (κ n))+
          (PositiveIteration.step a
            (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
            (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) ((t,p.1),p.2)+
              S.positiveSourceError B A (κ n)*ENNReal.ofReal (t-a)) := by
  intro B
  filter_upwards [S.eventually_normalizedHotSource_le_positive hcarleman hs₀ hsmax hη hηmax hK
    hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hκ hU hA0 hA hAmax,
    S.eventually_scaled_slab hs₀ hU hA] with n hsrc hslab
  intro t ht
  have htime := hslab t ⟨ha.trans ht.1,ht.2⟩
  have hs : ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 t →
      ENNReal.ofReal (S.euclideanHotSource (κ n) z/H q z.2) ≤
        ChartKernel.action (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
          (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) z+S.positiveSourceError B A (κ n) := by
    filter_upwards [hsrc] with z hz hzt
    exact hz ⟨hzt.1,hzt.2.trans ht.2⟩
  have hm := S.normalizedHot_positive_mild hs₀ hsmax hη hηmax hK hd₀.le hq₂ (κ n)
    ha ht.1 htime.2 (S.positiveSourceError B A (κ n)) hs
  have he := S.boundedHotRatio_preserves_trace hs₀ hsmax hη hηmax hK hd₀.le hq₂ (κ n)
    htime (ht.2.trans hAmax)
  filter_upwards [hm,he] with p hp he
  have hv : S.euclideanHot (κ n) ((t,p.1),p.2)/H q p.2 =
      S.boundedHotRatio (κ n) ((t,p.1),p.2) := by
    rw [← he,mul_div_cancel_left₀ _ (H_pos q p.2).ne']
  rw [hv] at hp
  exact hp

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Finite positive residual bounds for the actual attained-cap approximations -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_boundedHotRatio_residual (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 ≤ a) (hA0 : 0 ≤ A) (hA : ENNReal.ofReal A < U) (hAmax : A ≤ 1) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ k : ℕ, ∀ t ∈ Icc a A, ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.boundedHotRatio (κ n) ((t,p.1),p.2)) ≤
        (∑ j ∈ Finset.range k, iterate a
          (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
          (fun _ => ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B A (κ n))
          j ((t,p.1),p.2))+
        iterate a (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
          (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) k ((t,p.1),p.2) := by
  intro B
  filter_upwards [S.eventually_boundedHotRatio_positive_mild hcarleman hs₀ hsmax hη hηmax hK
    hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hκ hU ha hA0 hA hAmax] with n hn
  let J := positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n))
  let f : KineticPhase → ℝ≥0∞ := fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)
  let c := ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B A (κ n)
  have hconst : ∀ t ∈ Icc a A, ∀ᵐ p : Velocity × Velocity,
      f ((t,p.1),p.2) ≤ c+step a J f ((t,p.1),p.2) := by
    intro t ht
    have hlen : ENNReal.ofReal (t-a) ≤ 1 := by
      have h := ENNReal.ofReal_le_ofReal (show t-a ≤ 1 by linarith [ht.2])
      simpa only [ENNReal.ofReal_one] using h
    have he : S.positiveSourceError B A (κ n)*ENNReal.ofReal (t-a) ≤
        S.positiveSourceError B A (κ n) :=
      (mul_le_mul' le_rfl hlen).trans_eq (mul_one _)
    filter_upwards [hn t ht] with p hp
    apply (hp.trans (add_le_add le_rfl (add_le_add le_rfl he))).trans_eq
    dsimp only [c]
    ac_rfl
  intro k t ht
  exact positiveMain_residual_on_slab hcarleman (S.radius (κ n)) s₀ η K α γ d₀ q a A
    (F.indices (κ n))
    (S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ (κ n)).ennreal_ofReal
    c hconst k ht

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Finiteness and limiting size of the actual positive source error -/

noncomputable section

open Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem positiveSourceError_ne_top (S : AttainedCapSequence F) (B A : ℝ) (n : ℕ) :
    S.positiveSourceError B A n ≠ ∞ := by
  unfold positiveSourceError
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (coldGainErrorConstant_ne_top s₀ η K α d₀ q)),ENNReal.ofReal_ne_top⟩,
    ENNReal.ofReal_ne_top⟩

theorem positiveResidualConstant_tendsto (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    (a B A l : ℝ) {κ : ℕ → ℕ} (hκ : StrictMono κ)
    (hl : Tendsto (fun n => S.coldFraction (κ n)) atTop (𝓝 l)) :
    Tendsto (fun n => ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B A (κ n))
      atTop (𝓝 (ENNReal.ofReal (a+l))) := by
  have hc := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hl.const_add a)
  simpa only [Function.comp_def,add_zero] using hc.add (S.positiveSourceError_tendsto_zero hs₀ B A hκ)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform positive source control up to each actual attained cap time -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem attained_time_mul_radius (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (n : ℕ) :
    S.radius n*(S.time n/S.radius n) = S.time n := by
  field_simp [(S.radius_pos hs₀ n).ne']

theorem attained_time_mem (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (n : ℕ) :
    S.time n/S.radius n ∈ Icc (0:ℝ) 1 := by
  rw [S.normalized_time hs₀]
  constructor <;> linarith [(S.coldFraction_mem hs₀ n).1,(S.coldFraction_mem hs₀ n).2]

theorem eventually_attained_normalizedHotSource_le_positive
    (hcarleman : Published.GPV2009CarlemanInput) (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 (S.time (κ n)/S.radius (κ n)) →
      ENNReal.ofReal (S.euclideanHotSource (κ n) z/H q z.2) ≤
        ChartKernel.action (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
          (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) z+S.positiveSourceError B 1 (κ n) := by
  intro B
  let E := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
  have hB : 0 ≤ B := mul_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q))
      (mul_nonneg (by norm_num) (HotApplication.realBound_pos q).le))
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)
  filter_upwards [hκ.tendsto_atTop.eventually (eventually_source_tail_small F E 1)] with n hn
  have hc := (F.approximation (κ n)).cold_source_bound hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂
    (shrinkingHorizon_pos F.horizonScale_pos _).le
    ((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le) 1 hn
  have hr := S.radius_pos hs₀ (κ n)
  have hd := (ColdDilationMeasure.spacetime_dilation_quasiMeasurePreserving hr).ae hc
  have hkc := EuclideanFlight.kineticMap_measurePreserving.quasiMeasurePreserving.ae hd
  have hp := S.normalizedHotSource_le_positive_slab hcarleman hs₀ hsmax hη hηmax hK hα.le
    hαmax hγ.le hd₀ hdmax hsmall hq₁ hq₂ (κ n)
    ((S.attained_time_mul_radius hs₀ _).trans_le (S.time_mem _).2) (S.attained_time_mem hs₀ _).2
  filter_upwards [hkc,hp] with z hcz hpz hz
  have hrt : S.radius (κ n)*z.1.1 ∈ Ioc 0 (shrinkingHorizon F.horizonScale (κ n)) := by
    refine ⟨mul_pos hr hz.1,?_⟩
    exact (mul_le_mul_of_nonneg_left hz.2 hr.le).trans
      ((S.attained_time_mul_radius hs₀ _).trans_le (S.time_mem _).2)
  have hcz' := hcz hrt
  have hcold : S.euclideanColdSource (κ n) z ≤ B*S.radius (κ n) := by
    apply hcz'.2.trans
    change B*(S.radius (κ n)*z.1.1)^1 ≤ _
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left (hz.2.trans (S.attained_time_mem hs₀ _).2) hr.le).trans_eq
        (mul_one _)) hB
  have he := (hpz hz).trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hcold))
  simpa only [positiveSourceError,mul_one,add_assoc] using he

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual characteristic gain is the physical normal-angle kernel source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness

theorem CollisionCompactness.two_smul_incomingGain
    {X : Type*} [MeasurableSpace X] (μ : Measure (X × (Velocity × Velocity))) :
    (2 : ℝ≥0) • incomingGainMeasure μ =
      (incomingCollisionMeasure μ).map incomingLeft+
      (incomingCollisionMeasure μ).map incomingRight := by
  change (2 : ℝ≥0∞) • ((1/2 : ℝ≥0∞) •
    ((incomingCollisionMeasure μ).map incomingLeft+
      (incomingCollisionMeasure μ).map incomingRight)) = _
  rw [smul_smul,one_div,ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp),one_smul]

namespace JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicGain_eq_normal (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    E.characteristicGainMeasure ha hK hα hγ A R =
      sourcePullback (normalPhaseGainKernel
        (GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
          hK hα hγ η E.fraction) ∘ₘ (coldCylinderVolume a A R ⊗ₘ E.hotKernel)) := by
  let κ := GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  rw [normalPhaseGain_comp]
  change (2 : ℝ≥0) • sourcePullback (incomingGainMeasure
    (coldCylinderVolume a A R ⊗ₘ (κ ×ₖ E.hotKernel))) = _
  rw [← two_smul_incomingGain]
  exact (Measure.map_smul (2 : ℝ≥0) hotCharacteristicEquiv.symm.measurable.aemeasurable).symm

end JetCopyDatum.AttainedCapSequence
end BoltzmannNonuniqueness

end

end

section

/-! # The attained cap norm supplies large-ratio witnesses in the central cell -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem euclideanHot_div_weight_eq_normalized (S : AttainedCapSequence F)
    (n : ℕ) (t : ℝ) (p : Velocity × Velocity) :
    S.euclideanHot n ((t,p.1),p.2)/H q p.2 =
      S.normalizedHot n (t,EuclideanFlight.phaseEquiv p) := by
  rw [S.euclideanHot_eq_rescaledHot,S.rescaledHot_eq_weighted]
  exact mul_div_cancel_left₀ _ (H_pos q p.2).ne'

private theorem le_half_of_clamp_le_half {x : ℝ} (h : max 0 (min 2 x) ≤ 1/2) : x ≤ 1/2 := by
  by_contra hx
  have hmin : (1:ℝ)/2 < min 2 x := lt_min (by norm_num) (lt_of_not_ge hx)
  exact (not_lt_of_ge ((le_max_right _ _).trans h)) hmin

theorem exists_central_cap_witness (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {P : Velocity × Velocity → Prop} (hP : ∀ᵐ p, P p) :
    ∃ p : Velocity × Velocity, P p ∧ S.radius n • p.1 ∈ TorusChart.cube ∧
      1/2 < S.boundedHotRatio n ((S.time n/S.radius n,p.1),p.2) := by
  classical
  let t := S.time n/S.radius n
  let f := fun p : Velocity × Velocity => S.boundedHotRatio n ((t,p.1),p.2)
  by_contra h
  have hcell : ∀ᵐ p : Velocity × Velocity, S.radius n • p.1 ∈ TorusChart.cube → f p ≤ 1/2 := by
    filter_upwards [hP] with p hp hc
    exact le_of_not_gt (fun hf => h ⟨p,hp,hc,hf⟩)
  have hall := TorusChart.ae_le_of_central (S.radius_pos hs₀ n)
    (S.boundedHotRatio_periodic hs₀ n t) hcell
  have hratio : ∀ᵐ p : Velocity × Velocity,
      S.normalizedHot n (t,EuclideanFlight.phaseEquiv p) ≤ 1/2 := by
    filter_upwards [hall] with p hp
    rw [← S.euclideanHot_div_weight_eq_normalized]
    exact le_half_of_clamp_le_half hp
  have he := (MeasurePreserving.symm EuclideanFlight.phaseEquiv
    EuclideanFlight.phaseEquiv_measurePreserving).quasiMeasurePreserving.ae hratio
  have hjet : ∀ᵐ p ∂FlightMeasure.phaseVolume, S.normalizedHot n (t,p) ≤ 1/2 := by
    simpa only [MeasurableEquiv.apply_symm_apply] using he
  have hd := (ColdDilationMeasure.spatial_dilation_quasiMeasurePreserving
    (inv_pos.mpr (S.radius_pos hs₀ n))).ae hjet
  have hhot := (F.approximation n).hot_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le
  have hb : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      |(F.approximation n).hot (S.time n,p)| ≤ S.radius n/2 := by
    filter_upwards [hd] with p hp
    have hmul : S.radius n • ((S.radius n)⁻¹ • p.1) = p.1 := by
      rw [smul_smul,mul_inv_cancel₀ (S.radius_pos hs₀ n).ne',one_smul]
    change (F.approximation n).hot (S.radius n*t,
      (S.radius n • ((S.radius n)⁻¹ • p.1),p.2))/S.radius n ≤ 1/2 at hp
    rw [hmul,S.attained_time_mul_radius hs₀ n] at hp
    rw [abs_of_nonneg (hhot.2.1 _)]
    have h' := (div_le_iff₀ (S.radius_pos hs₀ n)).mp hp
    linarith
  have heLp : eLpNorm (fun p => (F.approximation n).hot (S.time n,p)) ∞
      FlightMeasure.phaseVolume ≤ ENNReal.ofReal (S.radius n/2) := by
    have hm : Measurable (fun p : JetPrototype.Phase =>
        (F.approximation n).hot (S.time n,p)) :=
      hhot.1.comp (measurable_const.prodMk measurable_id)
    rw [eLpNorm_exponent_top hm.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (hb.mono (fun p hp => by simpa only [Real.norm_eq_abs] using hp))
  have hsize := ENNReal.toReal_mono ENNReal.ofReal_ne_top heLp
  rw [ENNReal.toReal_ofReal (half_pos (S.radius_pos hs₀ n)).le] at hsize
  change (F.approximation n).hotSize (S.time n) ≤ S.radius n/2 at hsize
  rw [S.attained n] at hsize
  have hr := S.radius_pos hs₀ n
  change S.radius n ≤ S.radius n/2 at hsize
  linarith

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The positive mild inequality with the actual initial shot coefficient -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem normalizedHot_initial_positive_mild (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (hT : S.radius n*t ≤ shrinkingHorizon F.horizonScale n)
    (δ : ℝ≥0∞)
    (hsrc : ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 t →
      ENNReal.ofReal (S.euclideanHotSource n z/H q z.2) ≤
        ChartKernel.action (positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n))
          (fun w => ENNReal.ofReal (S.boundedHotRatio n w)) z+δ) :
    ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.euclideanHot n ((t,p.1),p.2)/H q p.2) ≤
        ENNReal.ofReal ((F.approximation n).coefficient*(HotSeedProfile.bound/HotSeedProfile.normLower q))+
          (PositiveIteration.step 0
            (positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n))
            (fun w => ENNReal.ofReal (S.boundedHotRatio n w)) ((t,p.1),p.2)+δ*ENNReal.ofReal t) := by
  let J := positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n)
  have hf := (S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀ hq₂ n).ennreal_ofReal
  have hsrc' : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Velocity)).prod volume,
      z.1.1 ∈ Ioc 0 t → ENNReal.ofReal (S.euclideanHotSource n z/H q z.2) ≤
        ChartKernel.action J (fun w => ENNReal.ofReal (S.boundedHotRatio n w)) z+δ := by
    simpa only [Measure.volume_eq_prod] using hsrc
  have hpull := (PositiveIteration.backward_measurePreserving t volume).quasiMeasurePreserving.ae hsrc'
  have hs := ae_ae_of_ae_prod ((measurePreserving_swap (μ := (volume : Measure (Velocity × Velocity)))
    (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hpull)
  have hm := S.normalizedHot_backward_mild hs₀ hsmax hη hηmax hK hd₀ hq₂ n ht hT
  have hi := S.normalizedHot_backward_source_integrable hs₀ hsmax hη hηmax hK hd₀ hq₂ n ht hT
  filter_upwards [hs,hm,hi] with p hs hm hi
  have hs' : ∀ᵐ s ∂volume.restrict (Ioc 0 t),
      ENNReal.ofReal (S.euclideanHotSource n (PositiveIteration.flight ((t,p.1),p.2) s)/H q p.2) ≤
        ChartKernel.action J (fun w => ENNReal.ofReal (S.boundedHotRatio n w))
          (PositiveIteration.flight ((t,p.1),p.2) s)+δ := by
    filter_upwards [ae_restrict_of_ae hs,ae_restrict_mem measurableSet_Ioc] with s hs hst
    exact hs hst
  rw [hm]
  have hb := S.hotInitial_ratio_bound hs₀ hsmax hη.le (by linarith) n
    (PositiveIntegral.scalePhase (S.radius n) (EuclideanFlight.phaseEquiv (EuclideanFlight.flight (-t) p)))
  have hh := PositiveIteration.step_source_upper
    (c := (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n)
      (EuclideanFlight.phaseEquiv (EuclideanFlight.flight (-t) p)))/S.radius n) ht J hf p hi δ hs'
  simpa only [sub_zero] using hh.trans (add_le_add (ENNReal.ofReal_le_ofReal hb) le_rfl)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Compact cap families on every sufficiently small prescribed horizon -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_tight_cap_family_at (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧ ∀ T : ℝ, 0 < T → T ≤ τ →
      ∃ A : TightCapFamily s₀ η K α γ d₀ q, A.time = T := by
  obtain ⟨τ,hτ,hτmax,hcap⟩ := exists_uniform_cap_solution hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  refine ⟨τ,hτ,hτmax,?_⟩
  intro T hT hTτ
  have hex (N : ℕ) : Nonempty (CapApproximation s₀ η K α γ d₀ q T N) := by
    obtain ⟨B,ell,hB,hell,hinit,F,hF⟩ := hcap N (N+1) T (by positivity) hT.le hTτ
    exact ⟨⟨B,ell,hB,hell,hinit,F,hF⟩⟩
  let F := fun N => Classical.choice (hex N)
  have hαone : α ≤ 1 := hαmax.trans (by norm_num)
  have hTmax := hTτ.trans hτmax
  have hc := cap_family_cutoff_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαone hγ hd₀ hd₀max
    hsmall hq₂ hT.le hTmax F
  let C : CompactCapFamily s₀ η K α γ d₀ q :=
    ⟨T,hT,hTmax,F,
      cap_family_density_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαone hγ hd₀ hd₀max
        hsmall hq₂ hT.le hTmax F,
      cap_family_pairs_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαone hγ hd₀ hd₀max
        hsmall hq₂ hT.le hTmax F,
      hc.1,hc.2,periodicInitial_L1_tendsto hs₀ hsmax hη hηmax hK hγ hd₀ (by linarith) hq₂ α
        (fun N => (F N).coefficient_mem)⟩
  have ht := cap_family_unifTight hs₀ hsmax hη hηmax hK hα hαone hγ hd₀ hd₀max
    hsmall hq₂ hT.le hTmax F
  exact ⟨⟨C,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2⟩,rfl⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Positive limiting cold fraction gives a bounded gain kernel at time zero -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem positiveMainKernel_fraction_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (n : ℕ) (z : Published.KineticPhase) (ht : 0 ≤ z.1.1) :
    positiveMainKernel (S.radius n) s₀ η K α γ d₀ q (F.indices n) z univ ≤
      ENNReal.ofReal (2*JetCoreSheet.growthConstant K α γ q/(z.1.1+S.coldFraction n)) :=
  positiveMainKernel_scale_time_bound (S.radius_pos hs₀ n) hs₀ hsmax hη hηmax hK hα hγ
    hd₀ hdmax hq₁ hq₂ (F.indices n) z ht

theorem HotLimitExtraction.eventually_positive_fraction_mass {S : AttainedCapSequence F}
    (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hl : 0 < E.fraction) :
    ∀ᶠ n in atTop, ∀ z : Published.KineticPhase, 0 ≤ z.1.1 →
      positiveMainKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)) z univ ≤
        ENNReal.ofReal (4*JetCoreSheet.growthConstant K α γ q/E.fraction) := by
  filter_upwards [E.fraction_limit.eventually_const_lt (half_lt_self hl)] with n hn
  intro z hz
  apply (S.positiveMainKernel_fraction_bound hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax
    hq₁ hq₂ (E.indices n) z hz).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 2*JetCoreSheet.growthConstant K α γ q/(E.fraction/2) :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (JetCoreSheet.growthConstant_nonneg hK α γ q))
        (half_pos hl) (by linarith)
    _ = _ := by ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A uniform exponential bound from the actual shot coefficient -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.eventually_positive_fraction_bound (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hl : 0 < E.fraction) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (S.time (E.indices n)/S.radius (E.indices n)),
      ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.boundedHotRatio (E.indices n) ((t,p.1),p.2)) ≤
        ENNReal.ofReal (((F.approximation (E.indices n)).coefficient*
          (HotSeedProfile.bound/HotSeedProfile.normLower q)+(S.positiveSourceError B 1 (E.indices n)).toReal)*
            Real.exp (4*JetCoreSheet.growthConstant K α γ q/E.fraction)) := by
  intro B
  filter_upwards [E.eventually_positive_fraction_mass hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax hq₁ hq₂ hl,
    S.eventually_attained_normalizedHotSource_le_positive hcarleman hs₀ hsmax hη hηmax hK hα hαmax
      hγ hd₀ hdmax hsmall hq₁ hq₂ E.indices_strict] with n hmass hsrc
  let A := S.time (E.indices n)/S.radius (E.indices n)
  let J := positiveMainKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n))
  let f := fun y => ENNReal.ofReal (S.boundedHotRatio (E.indices n) y)
  let δ := S.positiveSourceError B 1 (E.indices n)
  let c₀ := (F.approximation (E.indices n)).coefficient*(HotSeedProfile.bound/HotSeedProfile.normLower q)
  have hc₀ : 0 ≤ c₀ := mul_nonneg (F.approximation (E.indices n)).coefficient_mem.1
    (div_nonneg HotSeedProfile.bound_pos.le (HotSeedProfile.normLower_pos q).le)
  have hδ : ENNReal.ofReal δ.toReal = δ := ENNReal.ofReal_toReal (S.positiveSourceError_ne_top B 1 _)
  have hconst : ∀ t ∈ Icc 0 A, ∀ᵐ p : Velocity × Velocity,
      f ((t,p.1),p.2) ≤ ENNReal.ofReal (c₀+δ.toReal)+step 0 J f ((t,p.1),p.2) := by
    intro t ht
    have htime : S.radius (E.indices n)*t ∈ Icc 0 (shrinkingHorizon F.horizonScale (E.indices n)) :=
      ⟨mul_nonneg (S.radius_pos hs₀ _).le ht.1,
        (mul_le_mul_of_nonneg_left ht.2 (S.radius_pos hs₀ _).le).trans
          ((S.attained_time_mul_radius hs₀ _).trans_le (S.time_mem _).2)⟩
    have hs : ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 t →
        ENNReal.ofReal (S.euclideanHotSource (E.indices n) z/H q z.2) ≤
          ChartKernel.action J f z+δ := by
      filter_upwards [hsrc] with z hz hzt
      exact hz ⟨hzt.1,hzt.2.trans ht.2⟩
    have hm := S.normalizedHot_initial_positive_mild hs₀ hsmax hη hηmax hK hd₀.le hq₁ hq₂
      (E.indices n) ht.1 htime.2 δ hs
    have he := S.boundedHotRatio_preserves_trace hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n)
      htime (ht.2.trans (S.attained_time_mem hs₀ _).2)
    have hlen : ENNReal.ofReal t ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
        (ht.2.trans (S.attained_time_mem hs₀ _).2)
    filter_upwards [hm,he] with p hp he
    have hv : S.euclideanHot (E.indices n) ((t,p.1),p.2)/H q p.2 =
        S.boundedHotRatio (E.indices n) ((t,p.1),p.2) := by
      rw [← he,mul_div_cancel_left₀ _ (H_pos q p.2).ne']
    rw [hv] at hp
    have hδt : δ*ENNReal.ofReal t ≤ δ := (mul_le_mul' le_rfl hlen).trans_eq (mul_one δ)
    apply (hp.trans (add_le_add le_rfl (add_le_add le_rfl hδt))).trans_eq
    rw [ENNReal.ofReal_add hc₀ ENNReal.toReal_nonneg,hδ]
    dsimp only [c₀,J,f]
    ac_rfl
  intro t ht
  exact positiveMain_exponential_bound hcarleman (S.radius (E.indices n)) s₀ η K α γ d₀ q A
    (4*JetCoreSheet.growthConstant K α γ q/E.fraction) 2 (c₀+δ.toReal) (F.indices (E.indices n))
    (S.attained_time_mem hs₀ _).2
    (div_nonneg (mul_nonneg (by norm_num) (JetCoreSheet.growthConstant_nonneg hK α γ q)) hl.le) (by norm_num) (add_nonneg hc₀ ENNReal.toReal_nonneg)
    (S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n)).ennreal_ofReal
    (fun y _ => ENNReal.ofReal_le_ofReal (S.boundedHotRatio_bounds _ y).2)
    (fun y hy => hmass y hy.1) hconst ht

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # An admissible cap limit retaining its actual approximation sequence -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl
namespace BoltzmannNonuniqueness.JetCopyDatum

structure CapLocalLimit {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q) where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  density : (ℝ × Position) × Velocity → ℝ
  weak_limit : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume A.time).prod volume)
    (fun n => torusPhysical q (A.approximation (subsequence n)).solution.value) density
  mild : MildCollisionSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) density
  admissible : AdmissibleLocal A.time (JetPeriodicDatum.datum s₀ η K α γ d₀)
    (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) density)

theorem TightCapFamily.exists_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2) :
    Nonempty (CapLocalLimit A) := by
  obtain ⟨φ,g,hφ,hg,S,hpair,htrace⟩ := A.exists_mild_limit_with_traces_and_convergence
    hcarleman hGLPS hDP hs₀ hsmax hη hηmax hK.le hγ hd₀ hq₁ hq₂
  have hH := A.entropy_mild_limit_of_convergence hcarleman hs₀ hsmax hη hηmax hK hγ hd₀
    hwidth hα.le hαmax hq₁ hq₂ hφ S hpair htrace
  have hdatum := JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα.le hαmax
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  obtain ⟨hfinite,hentropy⟩ := S.entropy_admissible A.time_pos hdatum hm hn hH
  have hbound := A.toCompactCapFamily.weak_limit_moment hs₀ hsmax hη hηmax hK.le hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ hg S.nonnegative
  have hbase := momentBase_nonneg hs₀ hK.le hd₀ η α q
  have hgain := JetEnvelopeGain.momentConstant_nonneg hK.le α γ
  have hE := CollisionCompactness.exponentialPair_integrable S.measurable S.nonnegative
    (fun u => AnnularEnvelope.commonMoment_nonneg hbase hgain s₀ η (AnnularEnvelope.torusChart u))
    (AnnularEnvelope.torus_common_square_integrable hs₀ hη hηmax A.time_pos.le
      (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)) hbound
  exact ⟨⟨φ,hφ,g,hg,S,S.localAdmissible A.time_pos hm hn hdatum hfinite hentropy hE⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A positive limiting cold fraction rules out vanishing shot coefficients -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coefficient_not_tendsto_zero (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hl : 0 < E.fraction) :
    ¬ Tendsto (fun n => (F.approximation (E.indices n)).coefficient) atTop (𝓝 0) := by
  intro hcoef
  let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
    JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
  let C := 4*JetCoreSheet.growthConstant K α γ q/E.fraction
  let M := HotSeedProfile.bound/HotSeedProfile.normLower q
  let b := fun n => ((F.approximation (E.indices n)).coefficient*M+
    (S.positiveSourceError B 1 (E.indices n)).toReal)*Real.exp C
  have he := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (S.positiveSourceError_tendsto_zero hs₀ B 1 E.indices_strict)
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [b,Function.comp_def,ENNReal.toReal_zero,zero_mul,zero_add] using ((hcoef.mul_const M).add he).mul_const (Real.exp C)
  have hbound := E.eventually_positive_fraction_bound hcarleman hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hdmax hsmall hq₁ hq₂ hl
  have hle : ∀ᶠ n in atTop, ENNReal.ofReal (1/2:ℝ) ≤ ENNReal.ofReal (b n) := by
    filter_upwards [hbound] with n hn
    have ht := S.attained_time_mem hs₀ (E.indices n)
    obtain ⟨p,hp,_,hlarge⟩ := S.exists_central_cap_witness hs₀ hsmax hη hηmax hK hd₀.le hq₂
      (E.indices n) (hn (S.time (E.indices n)/S.radius (E.indices n)) ⟨ht.1,le_rfl⟩)
    exact (ENNReal.ofReal_le_ofReal hlarge.le).trans hp
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
  have hfalse : ENNReal.ofReal (1/2:ℝ) ≤ 0 := by
    simpa only [ENNReal.ofReal_zero] using
      le_of_tendsto_of_tendsto tendsto_const_nhds ht hle
  norm_num at hfalse

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform logarithmic remainders for the actual finite positive expansion -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_boundedHotRatio_log_residual (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (hA0 : 0 ≤ A) (hA : ENNReal.ofReal A < U) (hAmax : A ≤ 1) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ k : ℕ, ∀ t ∈ Icc a A, ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.boundedHotRatio (κ n) ((t,p.1),p.2)) ≤
        ((ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B A (κ n))*
          ENNReal.ofReal (∑ j ∈ Finset.range k,
            ((2*JetCoreSheet.growthConstant K α γ q)*Real.log (1/a))^j))+
        iterate a (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
          (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) k ((t,p.1),p.2) := by
  intro B
  filter_upwards [S.eventually_boundedHotRatio_residual hcarleman hs₀ hsmax hη hηmax hK
    hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hκ hU ha.le hA0 hA hAmax] with n hn
  intro k t ht
  have hc : ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B A (κ n) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,S.positiveSourceError_ne_top B A (κ n)⟩
  filter_upwards [hn k t ht] with p hp
  apply hp.trans
  apply add_le_add _ le_rfl
  exact positiveMain_constant_sum_uniform (S.radius_pos hs₀ (κ n)) hs₀ hsmax hη hηmax hK
    hα hγ hd₀ hdmax hq₁ hq₂ ha hAmax (F.indices (κ n)) _ hc k
    (z := ((t,p.1),p.2)) ht

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The logarithmic residual inequality at the actual attained cap time -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_attained_boundedHotRatio_log_residual
    (hcarleman : Published.GPV2009CarlemanInput) (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ)
    {a : ℝ} (ha : 0 < a) :
    let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
    ∀ᶠ n in atTop, ∀ k : ℕ, ∀ t ∈ Icc a (S.time (κ n)/S.radius (κ n)),
      ∀ᵐ p : Velocity × Velocity,
      ENNReal.ofReal (S.boundedHotRatio (κ n) ((t,p.1),p.2)) ≤
        ((ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B 1 (κ n))*
          ENNReal.ofReal (∑ j ∈ Finset.range k,
            ((2*JetCoreSheet.growthConstant K α γ q)*Real.log (1/a))^j))+
        iterate a (positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n)))
          (fun w => ENNReal.ofReal (S.boundedHotRatio (κ n) w)) k ((t,p.1),p.2) := by
  intro B
  filter_upwards [S.eventually_attained_normalizedHotSource_le_positive hcarleman hs₀ hsmax
    hη hηmax hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hκ] with n hsrc
  let A := S.time (κ n)/S.radius (κ n)
  let J := positiveMainKernel (S.radius (κ n)) s₀ η K α γ d₀ q (F.indices (κ n))
  let f := fun w : KineticPhase => ENNReal.ofReal (S.boundedHotRatio (κ n) w)
  let c := ENNReal.ofReal (a+S.coldFraction (κ n))+S.positiveSourceError B 1 (κ n)
  have hA : A ≤ 1 := (S.attained_time_mem hs₀ _).2
  have hc : c ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.ofReal_ne_top,S.positiveSourceError_ne_top B 1 (κ n)⟩
  have hconst : ∀ t ∈ Icc a A, ∀ᵐ p : Velocity × Velocity,
      f ((t,p.1),p.2) ≤ c+step a J f ((t,p.1),p.2) := by
    intro t ht
    have htime : S.radius (κ n)*t ∈ Icc 0 (shrinkingHorizon F.horizonScale (κ n)) :=
      ⟨mul_nonneg (S.radius_pos hs₀ _).le (ha.le.trans ht.1),
        (mul_le_mul_of_nonneg_left ht.2 (S.radius_pos hs₀ _).le).trans
          ((S.attained_time_mul_radius hs₀ _).trans_le (S.time_mem _).2)⟩
    have hs : ∀ᵐ z : KineticPhase, z.1.1 ∈ Ioc 0 t →
        ENNReal.ofReal (S.euclideanHotSource (κ n) z/H q z.2) ≤
        ChartKernel.action J f z+S.positiveSourceError B 1 (κ n) := by
      filter_upwards [hsrc] with z hz hzt
      exact hz ⟨hzt.1,hzt.2.trans ht.2⟩
    have hm := S.normalizedHot_positive_mild hs₀ hsmax hη hηmax hK hd₀.le hq₂ (κ n)
      ha.le ht.1 htime.2 (S.positiveSourceError B 1 (κ n)) hs
    have he := S.boundedHotRatio_preserves_trace hs₀ hsmax hη hηmax hK hd₀.le hq₂ (κ n)
      htime (ht.2.trans hA)
    have hlen : ENNReal.ofReal (t-a) ≤ 1 := by
      exact (ENNReal.ofReal_le_ofReal (show t-a ≤ 1 by linarith [ht.2])).trans_eq ENNReal.ofReal_one
    filter_upwards [hm,he] with p hp he
    have hv : S.euclideanHot (κ n) ((t,p.1),p.2)/H q p.2 =
        S.boundedHotRatio (κ n) ((t,p.1),p.2) := by
      rw [← he,mul_div_cancel_left₀ _ (H_pos q p.2).ne']
    rw [hv] at hp
    have he' := (mul_le_mul' (le_rfl : S.positiveSourceError B 1 (κ n) ≤ _) hlen).trans_eq
      (mul_one (S.positiveSourceError B 1 (κ n)))
    exact (hp.trans (add_le_add le_rfl (add_le_add le_rfl he'))).trans_eq (by dsimp [c]; ac_rfl)
  intro k t ht
  have hh := positiveMain_residual_on_slab hcarleman (S.radius (κ n)) s₀ η K α γ d₀ q a A
    (F.indices (κ n))
    (S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ (κ n)).ennreal_ofReal
    c hconst k ht
  filter_upwards [hh] with p hp
  apply hp.trans
  apply add_le_add _ le_rfl
  exact positiveMain_constant_sum_uniform (S.radius_pos hs₀ (κ n)) hs₀ hsmax hη hηmax hK
    hα hγ hd₀ hdmax hq₁ hq₂ ha hA (F.indices (κ n)) c hc k ht

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A positive limiting shot coefficient when the cold fraction stays positive -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.positive_coefficient_subsequence (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hl : 0 < E.fraction) :
    ∃ ell ∈ Ioc (0:ℝ) 2, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (F.approximation (E.indices (φ n))).coefficient) atTop (𝓝 ell) := by
  obtain ⟨ell,hell,φ,hφ,hlim⟩ := isCompact_Icc.tendsto_subseq
    (fun n => (F.approximation (E.indices n)).coefficient_mem)
  have hne : ell ≠ 0 := by
    intro he
    have hzero := (E.subsequence φ hφ).coefficient_not_tendsto_zero hcarleman hs₀ hsmax hη hηmax
      hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hl
    apply hzero
    simpa only [he, HotLimitExtraction.subsequence, Function.comp_def] using hlim
  exact ⟨ell,⟨lt_of_le_of_ne hell.1 hne.symm,hell.2⟩,φ,hφ,hlim⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
