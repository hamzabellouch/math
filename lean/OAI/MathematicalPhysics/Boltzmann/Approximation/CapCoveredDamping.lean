import OAI.MathematicalPhysics.Boltzmann.Approximation.CapActualLossDensity
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLimitTransport
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapCoefficientExtraction
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotSourceIntegrability
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCharacteristics
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Approximation.SurvivalProfile
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCutoffGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicPhysicalGain
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainPullback
import OAI.MathematicalPhysics.Boltzmann.Branching.GainMeasureLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.MovingBoxMass
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Collision.KernelInvariantPowers
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedNonaxialLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalOutgoing
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricEntry

namespace OAI

section

/-! # Uniform proportional loss for the actual hot solutions at positive cold fraction -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def positiveFractionLoss (s₀ η K α γ d₀ q ell : ℝ) : ℝ :=
  (2+escapedConstant s₀ η K α d₀)*hotConstant q+
    2*JetEnvelopeGain.momentConstant K α γ/ell

theorem HotLimitExtraction.eventually_proportional_loss (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hl : 0 < E.fraction) {A : ℝ} (hAmax : A ≤ 1)
    (hA : ENNReal.ofReal A < E.horizon) :
    ∀ᶠ n in atTop, ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 A →
      -(2*Real.pi*(‖u.2.2‖+1)*positiveFractionLoss s₀ η K α γ d₀ q E.fraction)*
        S.normalizedHot (E.indices n) u ≤ S.rescaledHotSource (E.indices n) u := by
  have hrsmall := ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop).eventually
    (gt_mem_nhds zero_lt_one)
  have hlsmall := E.fraction_limit.eventually (lt_mem_nhds (show E.fraction/2 < E.fraction by linarith))
  filter_upwards [hrsmall,hlsmall,S.eventually_scaled_slab hs₀ E.horizon_limit hA]
    with n hr₁ hln hslab
  let Fn := F.approximation (E.indices n)
  have hT := (shrinkingHorizon_pos F.horizonScale_pos (E.indices n)).le
  have hTmax := (shrinkingHorizon_le F.horizonScale_pos (E.indices n)).trans F.horizonScale_le
  have hν := Fn.loss_scale_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax hsmall hq hT hTmax
  have hn := (Fn.hot_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT).2.1
  have hr := S.radius_pos hs₀ (E.indices n)
  have hqp := ColdDilationMeasure.spacetime_dilation_quasiMeasurePreserving hr
  filter_upwards [hqp.ae hν] with u hu ht
  have hphys := hslab u.1 ⟨ht.1.le,ht.2⟩
  have hνp := hu ⟨mul_pos hr ht.1,hphys.2⟩
  have hδ : S.radius (E.indices n)*S.coldFraction (E.indices n) =
      DatumBounds.scale s₀ η (F.indices (E.indices n)+1) := by
    dsimp [coldFraction]
    field_simp
  change lossFrequency q (F.indices (E.indices n)+1) Fn.solution.value
    (S.radius (E.indices n)*u.1,(S.radius (E.indices n) • u.2.1,u.2.2)) ≤
      2*Real.pi*(‖u.2.2‖+1)*
        ((S.radius (E.indices n)*u.1+DatumBounds.scale s₀ η (F.indices (E.indices n)+1)+
          escapedConstant s₀ η K α d₀)*hotConstant q+
          JetEnvelopeGain.momentConstant K α γ/
            (S.radius (E.indices n)*u.1+DatumBounds.scale s₀ η (F.indices (E.indices n)+1))) at hνp
  conv_rhs at hνp => rw [← hδ]
  have hbound := Cap.positive_fraction_loss_scaling hr hr₁.le
    (S.coldFraction_mem hs₀ (E.indices n)) hl hln.le ⟨ht.1.le,ht.2.trans hAmax⟩
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)
    (hotConstant_nonneg q) (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    (by positivity : 0 ≤ 2*Real.pi*(‖u.2.2‖+1)) hνp
  have hlow := Fn.hot_net_lower hs₀ hsmax hη hηmax hK hd₀.le hq hT
    (S.radius (E.indices n)*u.1,(S.radius (E.indices n) • u.2.1,u.2.2))
  have hz : 0 ≤ S.normalizedHot (E.indices n) u := div_nonneg (hn _) hr.le
  have he : S.radius (E.indices n)*S.normalizedHot (E.indices n) u =
      Fn.hot (S.radius (E.indices n)*u.1,(S.radius (E.indices n) • u.2.1,u.2.2)) := by
    dsimp [normalizedHot, PositiveIntegral.scalePhase]
    field_simp
    rfl
  have hprod := mul_le_mul_of_nonneg_right hbound hz
  have hprod' : lossFrequency q (F.indices (E.indices n)+1) Fn.solution.value
      (S.radius (E.indices n)*u.1,(S.radius (E.indices n) • u.2.1,u.2.2))*
      Fn.hot (S.radius (E.indices n)*u.1,(S.radius (E.indices n) • u.2.1,u.2.2)) ≤
      (2*Real.pi*(‖u.2.2‖+1)*positiveFractionLoss s₀ η K α γ d₀ q E.fraction)*
        S.normalizedHot (E.indices n) u := by
    calc
      _ = (S.radius (E.indices n)*lossFrequency q (F.indices (E.indices n)+1) Fn.solution.value
        (S.radius (E.indices n)*u.1,(S.radius (E.indices n) • u.2.1,u.2.2)))*
          S.normalizedHot (E.indices n) u := by rw [← he]; ring
      _ ≤ _ := hprod
  simpa only [neg_mul, rescaledHotSource, Fn] using (neg_le_neg hprod').trans hlow

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot occupation measure in physical and characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotOccupation_eq_density (E : HotLimitExtraction S)
    (μ : Measure (ℝ × JetPrototype.Space)) [SFinite μ] :
    μ ⊗ₘ E.hotKernel = positiveDensityMeasure (μ.prod volume) E.cappedHot :=
  compProd_density_const μ volume E.cappedHot_measurable

theorem HotLimitExtraction.hotOccupation_cylinder (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 ≤ a) :
    coldCylinderVolume a A R ⊗ₘ E.hotKernel =
      positiveDensityMeasure ((coldCylinderVolume a A R).prod volume) E.hotLimit := by
  rw [E.hotOccupation_eq_density]
  apply withDensity_congr_ae
  have he : E.cappedHot =ᵐ[(coldCylinderVolume a A R).prod volume] E.hotLimit := by
    rw [coldCylinderVolume_eq_hot_restrict ha]
    exact (E.cappedHot_eq A R).filter_mono ae_restrict_le
  exact he.fun_comp ENNReal.ofReal

theorem HotLimitExtraction.hotOccupation_characteristic (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 ≤ a) :
    sourcePullback (coldCylinderVolume a A R ⊗ₘ E.hotKernel) =
      positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit) := by
  rw [E.hotOccupation_cylinder ha,coldCylinderVolume_eq,
    positiveDensityMeasure_restrict _ _ (coldCylinderSet_measurable a A R)]
  exact positiveDensityMeasure_map_symm hotCharacteristicEquiv
    hotCharacteristic_measurePreserving
    (E.hotLimit_measurable.indicator (coldCylinderSet_measurable a A R))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Survival along the actual rescaled hot characteristics -/

noncomputable section

open MeasureTheory Filter Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem normalizedHot_survival (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {A C : ℝ}
    (hA : S.radius n*A ≤ shrinkingHorizon F.horizonScale n)
    (hlow : ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 A →
      -(C*(‖u.2.2‖+1))*S.normalizedHot n u ≤ S.rescaledHotSource n u)
    {t : ℝ} (ht : t ∈ Icc 0 A) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-(C*(‖p.2‖+1))*t)*
        ((F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n) ≤
      S.normalizedHot n (t,JetBarrier.flight t p) := by
  have hT : S.radius n*t ≤ shrinkingHorizon F.horizonScale n :=
    (mul_le_mul_of_nonneg_left ht.2 (S.radius_pos hs₀ n).le).trans hA
  have hm := S.normalizedHot_mild hs₀ hsmax hη hηmax hK hd₀ hq n hT
  have hfm := S.normalizedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  obtain ⟨hgm,B,hB⟩ := S.rescaledHotForcing_properties hs₀ hsmax hη hηmax hK hd₀ hq n
  have hi : Measurable (fun p =>
      (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n) :=
    (((F.approximation n).hotInitial_measurable).comp
      (by unfold PositiveIntegral.scalePhase; fun_prop)).div_const _
  have hp := (FlightMeasure.spacetime_measurePreserving 0).quasiMeasurePreserving.ae hlow
  have hpp := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hp)
  apply PositiveIntegral.survival_characteristic ht.1 hi hfm hgm hB hm (fun p => C*(‖p.2‖+1))
  filter_upwards [hpp] with p hp
  filter_upwards [hp] with s hs hst
  rw [S.normalizedHot_netSource hs₀ n]
  simpa only [sub_zero,JetBarrier.flight,Prod.swap] using hs ⟨hst.1,hst.2.trans ht.2⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A fixed surviving profile below each sufficiently late actual hot shot -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hotDensity_ge_survivalProfile (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq₀ : 0 ≤ q) (hq : q < 2)
    (n : ℕ) {ell c C : ℝ} (hell : 0 < ell) (hc : 0 ≤ c)
    (hl : ell/2 ≤ S.coldFraction n) (hcoef : c ≤ (F.approximation n).coefficient)
    (hA : S.radius n*(1/2) ≤ shrinkingHorizon F.horizonScale n)
    (hlow : ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 (1/2) →
      -(C*(‖u.2.2‖+1))*S.normalizedHot n u ≤ S.rescaledHotSource n u) (R : ℝ) :
    survivalProfile q ell c C ≤ᵐ[hotWindowVolume (1/2) R] S.hotDensity n := by
  let μt : Measure ℝ := volume.restrict (Icc (0:ℝ) (1/2))
  let μx : Measure JetPrototype.Space := volume.restrict (Metric.closedBall 0 R)
  have hsp := survivalProfile_measurable q ell c C
  have hden := S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  have hprod : ∀ᵐ u ∂μt.prod (μx.prod volume),
      survivalProfile q ell c C ((u.1,u.2.1),u.2.2) ≤ S.hotDensity n ((u.1,u.2.1),u.2.2) := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_le hsp hden).preimage
      (by fun_prop))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hsurv := S.normalizedHot_survival hs₀ hsmax hη hηmax hK hd₀ hq n hA hlow ht
    have hback := (FlightMeasure.flight_measurePreserving (-t)).quasiMeasurePreserving.ae hsurv
    have hall : ∀ᵐ p ∂FlightMeasure.phaseVolume,
        survivalProfile q ell c C ((t,p.1),p.2) ≤ S.hotDensity n ((t,p.1),p.2) := by
      filter_upwards [hback] with p hp
      change Real.exp (-(C*(‖p.2‖+1))*t)*
        ((F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n)
          (JetBarrier.flight (-t) p))/S.radius n) ≤
        S.normalizedHot n (t,JetBarrier.flight t (JetBarrier.flight (-t) p)) at hp
      rw [JetFreeTransport.flight_neg] at hp
      by_cases hcore : ((t,p.1),p.2) ∈ survivalCore ell
      · have hseed := S.initial_core_lower hs₀ hsmax hη.le hq₀ n hell hc hl hcoef hcore.2.1 hcore.2.2
        have hlower := (mul_le_mul_of_nonneg_left hseed (Real.exp_pos _).le).trans hp
        have hphys : S.radius n*t ∈ Icc 0 (shrinkingHorizon F.horizonScale n) :=
          ⟨mul_nonneg (S.radius_pos hs₀ n).le ht.1,
            (mul_le_mul_of_nonneg_left ht.2 (S.radius_pos hs₀ n).le).trans hA⟩
        change _ ≤ S.extendedHot n (t,p)
        rw [extendedHot,indicator_of_mem (show (t,p) ∈ S.hotTimeDomain n from hphys),
          S.rescaledHot_eq_weighted,survivalProfile,indicator_of_mem hcore]
        exact mul_le_mul_of_nonneg_left hlower (H_nonneg q p.2)
      · rw [survivalProfile,indicator_of_notMem hcore]
        exact S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n _
    exact hall.filter_mono (ae_mono (Measure.prod_mono Measure.restrict_le_self le_rfl))
  exact (measurePreserving_prodAssoc μt μx (volume : Measure Velocity)).quasiMeasurePreserving.ae hprod

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The positive initial core survives the weak hot limit -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.survival_profile_lower (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hl : 0 < E.fraction)
    {c : ℝ} (hc : 0 < c)
    (hclim : Tendsto (fun n => (F.approximation (E.indices n)).coefficient) atTop (𝓝 c))
    (R : ℝ) :
    survivalProfile q E.fraction (c/2)
      (2*Real.pi*positiveFractionLoss s₀ η K α γ d₀ q E.fraction) ≤ᵐ[hotWindowVolume (1/2) R]
        E.hotLimit := by
  let C := 2*Real.pi*positiveFractionLoss s₀ η K α γ d₀ q E.fraction
  have hA : ENNReal.ofReal (1/2:ℝ) < E.horizon :=
    lt_of_lt_of_le (by norm_num) E.horizon_ge
  have hsource := E.eventually_proportional_loss hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax
    hsmall hq₂ hl (by norm_num : (1/2:ℝ) ≤ 1) hA
  have hfra := E.fraction_limit.eventually (lt_mem_nhds (show E.fraction/2 < E.fraction by linarith))
  have hcoef := hclim.eventually (lt_mem_nhds (show c/2 < c by linarith))
  have hslab := S.eventually_scaled_slab hs₀ E.horizon_limit hA
  have hbound : ∀ᶠ n in atTop, survivalProfile q E.fraction (c/2) C ≤ᵐ[hotWindowVolume (1/2) R]
      S.hotDensity (E.indices n) := by
    filter_upwards [hsource,hfra,hcoef,hslab] with n hsrc hfr hcf hsl
    apply S.hotDensity_ge_survivalProfile hs₀ hsmax hη hηmax hK hd₀.le (by linarith) hq₂
      (E.indices n) hl (by linarith) hfr.le hcf.le (hsl (1/2) ⟨by norm_num,le_rfl⟩).2 _ R
    filter_upwards [hsrc] with u hu ht
    convert hu ht using 1
    dsimp [C]
    ring
  exact (E.hotLimit_weak (1/2) R).ge_eventually
    (fun n => memLp_one_iff_integrable.mp
      ((S.hotDensity_uniformIntegrable hs₀ hsmax hη hηmax hK hd₀.le hq₂ (1/2) R).memLp (E.indices n)))
    (survivalProfile_measurable q E.fraction (c/2) C)
    (survivalProfile_nonneg hl.le (by linarith)) hbound

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Positive cold fraction gives a nonzero limiting hot solution -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.positive_fraction_nonvanishing (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hl : 0 < E.fraction) :
    ¬(∀ A > 0, A < 1 → ∀ R,
      E.hotLimit ∘ EuclideanFlight.hotChart =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0) := by
  intro hz
  obtain ⟨c,hc,φ,hφ,hclim⟩ := E.positive_coefficient_subsequence hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hl
  let E' := E.subsequence φ hφ
  have hclim' : Tendsto (fun n => (F.approximation (E'.indices n)).coefficient) atTop (𝓝 c) := hclim
  obtain ⟨R,hR⟩ := survivalCore_positive_measure hl
  have hb := E'.survival_profile_lower hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax
    hsmall hq₁ hq₂ hl hc.1 hclim' R
  have hze := hz (1/2) (by norm_num) (by norm_num) R
  have hzn : E'.hotLimit =ᵐ[hotWindowVolume (1/2) R] 0 := by
    have hp := (MeasurePreserving.symm EuclideanFlight.hotChart
      (EuclideanFlight.hotChart_measurePreserving (1/2) R)).quasiMeasurePreserving.ae hze
    filter_upwards [hp] with z hz
    change E.hotLimit z = 0
    simpa only [Function.comp_apply,MeasurableEquiv.apply_symm_apply,Pi.zero_apply] using hz
  obtain ⟨z,hzcore,hzb⟩ := exists_mem_of_measure_ne_zero_of_ae hR
    (ae_restrict_of_ae (hb.and hzn))
  have hp := survivalProfile_pos (q := q) (C := 2*Real.pi*positiveFractionLoss s₀ η K α γ d₀ q E'.fraction)
    hl (show 0 < c/2 by linarith [hc.1]) hzcore
  exact (not_le_of_gt hp) (hzb.1.trans_eq hzb.2)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual characteristic collision source acts on the actual hot density -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicGainKernel (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    Kernel CharacteristicPhase CharacteristicPhase :=
  transportedKernel hotCharacteristicEquiv (normalPhaseGainKernel
    (GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
      hK hα hγ η E.fraction))

instance HotLimitExtraction.characteristicGainKernel_sFinite (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    IsSFiniteKernel (E.characteristicGainKernel ha hK hα hγ) := by
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  unfold HotLimitExtraction.characteristicGainKernel
  infer_instance

theorem HotLimitExtraction.characteristicGain_eq_kernel (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    E.characteristicGainMeasure ha hK hα hγ A R =
      E.characteristicGainKernel ha hK hα hγ ∘ₘ
        positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit) := by
  rw [← E.hotOccupation_characteristic ha.le]
  exact (E.characteristicGain_eq_normal ha hK hα hγ).trans
    (transportedKernel_comp hotCharacteristicEquiv _ _).symm

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The characteristic loss source has an integrable time density -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicLossDensity (E : HotLimitExtraction S) (a A R : ℝ) :
    CharacteristicPhase → ℝ := cylinderPullback a A R (fun z => E.hotLimit z*
      GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)

theorem HotLimitExtraction.characteristicLossDensity_integrable (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) : Integrable (E.characteristicLossDensity a A R) volume :=
  cylinderPullback_integrable (E.actual_loss_cylinder_integrable ha haA hK hα hγ hq)

theorem HotLimitExtraction.characteristicLoss_cumulative (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {φ : Velocity × Velocity → ℝ}
    (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p) {B : ℝ} (hB : ∀ p, |φ p| ≤ B) (t : ℝ) :
    WeakTime.cumulative (WeakTime.timeSource
      (E.characteristicLossMeasure ha hK hα hγ A R) φ) t =
      ∫ s in Iic t, WeakTime.phaseProjection (E.characteristicLossDensity a A R) φ s := by
  let θ : ℝ → ℝ := (Iic t).indicator (fun _ => 1)
  have hθ : Measurable θ := measurable_const.indicator measurableSet_Iic
  have hθB (s : ℝ) : |θ s| ≤ 1 := by
    by_cases hs : s ∈ Iic t <;> simp [θ,hs]
  have hψ : Measurable (fun z : HotKineticPhase =>
      θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2) :=
    (hθ.comp (measurable_fst.comp hotCharacteristicEquiv.symm.measurable)).mul
      (hφ.comp (measurable_snd.comp hotCharacteristicEquiv.symm.measurable))
  have hψB (z : HotKineticPhase) :
      |θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hθB _) (hB _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)
  rw [WeakTime.timeSource_cumulative _ hφ hn]
  change (∫ u, θ u.1*φ u.2 ∂sourcePullback _) = _
  have hm : Measurable (fun u : CharacteristicPhase => θ u.1*φ u.2) :=
    (hθ.comp measurable_fst).mul (hφ.comp measurable_snd)
  rw [sourcePullback_integral _ hm,
    E.actual_loss_cylinder_integral ha haA hK hα hγ hq hψ hψB]
  rw [← cylinderPullback_integral a A R
    (fun z => E.hotLimit z*GeometricBackground.frequency E.phase η E.fraction K α γ
      z.1.1 z.1.2 z.2) (fun u => θ u.1*φ u.2)]
  exact WeakTime.cumulative_density_projection
    (E.characteristicLossDensity_integrable ha haA hK hα hγ hq) hφ hB t

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual characteristic loss measure has its physical density -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicLossDensity_nonneg (E : HotLimitExtraction S)
    (a A R : ℝ) (u : CharacteristicPhase) : 0 ≤ E.characteristicLossDensity a A R u := by
  change 0 ≤ (coldCylinderSet a A R).indicator (fun z => E.hotLimit z*
    GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)
      (hotCharacteristicEquiv u)
  apply indicator_nonneg _ _
  intro z _
  exact mul_nonneg (E.hotLimit_nonneg z) (GeometricBackground.frequency_nonneg ..)

theorem HotLimitExtraction.characteristicLoss_integral (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {ψ : CharacteristicPhase → ℝ} (hψ : Measurable ψ)
    {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ u, ψ u ∂E.characteristicLossMeasure ha hK hα hγ A R) =
      ∫ u, ψ u*E.characteristicLossDensity a A R u := by
  have hm : Measurable (fun z : HotKineticPhase => ψ (hotCharacteristicEquiv.symm z)) :=
    hψ.comp hotCharacteristicEquiv.symm.measurable
  change (∫ u, ψ u ∂sourcePullback _) = _
  rw [sourcePullback_integral _ hψ,
    E.actual_loss_cylinder_integral ha haA hK hα hγ hq hm (fun z => hB _)]
  exact (cylinderPullback_integral a A R _ ψ).symm

theorem HotLimitExtraction.characteristicLossMeasure_eq (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    E.characteristicLossMeasure ha hK hα hγ A R =
      positiveDensityMeasure volume (E.characteristicLossDensity a A R) := by
  let _ := E.incomingLossMeasure_finite (R := R) ha (ha.le.trans haA) hK hα hγ hq
  have : IsFiniteMeasure (E.characteristicLossMeasure ha hK hα hγ A R) := by
    unfold HotLimitExtraction.characteristicLossMeasure
    infer_instance
  have hi := E.characteristicLossDensity_integrable (R := R) ha haA hK hα hγ hq
  have hn := ae_of_all volume (E.characteristicLossDensity_nonneg a A R)
  let _ := positiveDensityMeasure_finite hi hn
  apply Compactness.finite_measure_eq_of_positive_smooth_tests
  intro ψ hψ hc _hψn
  obtain ⟨B,hB⟩ := hψ.continuous.bounded_above_of_compact_support hc
  rw [E.characteristicLoss_integral ha haA hK hα hγ hq hψ.continuous.measurable hB,
    positiveDensityMeasure_integral hi.aemeasurable hn]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Positive retained-source balance for the actual hot limit -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicFrequency (E : HotLimitExtraction S)
    (u : CharacteristicPhase) : ℝ :=
  GeometricBackground.frequency E.phase η E.fraction K α γ
    (hotCharacteristicEquiv u).1.1 (hotCharacteristicEquiv u).1.2 (hotCharacteristicEquiv u).2

theorem HotLimitExtraction.characteristicLossDensity_factor (E : HotLimitExtraction S)
    (a A R : ℝ) (u : CharacteristicPhase) :
    E.characteristicLossDensity a A R u =
      cylinderPullback a A R E.hotLimit u*E.characteristicFrequency u := by
  by_cases hu : hotCharacteristicEquiv u ∈ coldCylinderSet a A R
  · simp only [HotLimitExtraction.characteristicLossDensity,cylinderPullback,Function.comp_def,
      indicator_of_mem hu,HotLimitExtraction.characteristicFrequency]
  · simp only [HotLimitExtraction.characteristicLossDensity,cylinderPullback,Function.comp_def,
      indicator_of_notMem hu,zero_mul]

theorem HotPairExtraction.characteristic_damped_measure_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C)
    {β : Velocity × Velocity → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseSlice (WeakTime.timeWeightedDensity a A C
        (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))) t =
      WeakTime.phaseSlice (WeakTime.timeWeightedDensity a A C
        (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))) s+
      WeakTime.phaseIncrement
        (WeakTime.timeWeightedSource a A C (WeakTime.weightedPhaseSource
          (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) β)+
        positiveDensityMeasure volume (WeakTime.dampedResidual a A C
          (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))
          (WeakTime.phaseWeight β (E.toHotLimitExtraction.characteristicLossDensity a A R)))) s t := by
  obtain ⟨R,hR,hweak⟩ := E.common_characteristic_weak_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hβc
  refine ⟨R,hR,?_⟩
  let _ := E.toHotLimitExtraction.incomingGainMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  have : IsFiniteMeasure (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) := by
    unfold HotLimitExtraction.characteristicGainMeasure
    infer_instance
  have hi := (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le
    ((ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB) R).2.1
  have hLi := E.toHotLimitExtraction.characteristicLossDensity_integrable (R := R)
    ha haA.le hK hα hγ hq₂
  have hn (u : CharacteristicPhase) : 0 ≤ cylinderPullback a A R E.hotLimit u :=
    indicator_nonneg (fun z _ => E.toHotLimitExtraction.hotLimit_nonneg z) _
  apply WeakTime.ae_localized_damped_measure_balance haA hC (cylinderPullback_integrable hi)
    hLi (ae_of_all _ hn) _ hβ hβc hβn
  · apply ae_of_all
    intro u hu
    by_cases hz : β u.2 = 0
    · simp only [hz,zero_mul,mul_zero,le_refl]
    rw [E.toHotLimitExtraction.characteristicLossDensity_factor]
    have hb := hfrequency u hu (subset_tsupport β hz)
    have hp : 0 ≤ β u.2*cylinderPullback a A R E.hotLimit u := mul_nonneg (hβn _) (hn u)
    nlinarith only [mul_le_mul_of_nonneg_left hb hp]
  · intro φ hφ hc hφn hφβ θ hθ hθc hθs
    have hb := hweak φ hφ hc hφn hφβ θ hθ hθc hθs
    rw [E.toHotLimitExtraction.characteristicLossMeasure_eq ha haA.le hK hα hγ hq₂,
      positiveDensityMeasure_integral hLi.aemeasurable
        (ae_of_all _ (E.toHotLimitExtraction.characteristicLossDensity_nonneg a A R))] at hb
    exact hb

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual normal-angle hot source equals the active two-beam source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem hotCharacteristic_jump (z : CharacteristicPhase) (v : Velocity) :
    hotCharacteristicEquiv.symm ((hotCharacteristicEquiv z).1,v) =
      characteristicBeamJump z v := by
  apply hotCharacteristicEquiv.injective
  rw [MeasurableEquiv.apply_symm_apply]
  change ((z.1,spaceEquiv (z.2.1+z.1 • z.2.2)),v) =
    ((z.1,spaceEquiv ((z.2.1+z.1 • z.2.2-z.1 • v)+z.1 • v)),v)
  rw [sub_add_cancel]

end BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicGainKernel_lintegral_normal
    (E : HotLimitExtraction S) {a : ℝ} (ha : 0 < a)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (z : CharacteristicPhase)
    {f : CharacteristicPhase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂E.characteristicGainKernel ha hK hα hγ z) =
      ∫⁻ v, f (characteristicBeamJump z v)
        ∂normalGainKernel (GeometricBackground.slabKernel ha
          (zero_lt_one.trans_le E.phase_mem.1) hK hα hγ η E.fraction)
          ((hotCharacteristicEquiv z).1,z.2.2) := by
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  rw [HotLimitExtraction.characteristicGainKernel,transportedKernel_lintegral _ _ z hf,
    normalPhaseGainKernel_lintegral_gain _ _
      (f := fun y => f (hotCharacteristicEquiv.symm y)) (hf.comp hotCharacteristicEquiv.symm.measurable)]
  apply lintegral_congr
  intro v
  rw [hotCharacteristic_jump]

theorem HotLimitExtraction.characteristicGainKernel_eq_normal_beam
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (z : CharacteristicPhase)
    (ht : a ≤ z.1)
    (hactive : GeometricBackground.active E.phase η E.fraction
      (transverse (z.2.1+z.1 • z.2.2))) :
    E.characteristicGainKernel ha hK hα hγ z = ENNReal.ofReal (K/(4*r)) •
      beamNormalCharacteristicKernel
        (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
          hα.le hγ.le η r) z := by
  let b := GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
    hα.le hγ.le η r
  let L := GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  have he : L (hotCharacteristicEquiv z).1 =
      ENNReal.ofReal (K/(4*r)) • beamPartnerKernel b (characteristicBeamPoint z) := by
    rw [beamPartnerKernel_apply]
    change GeometricBackground.background E.phase η E.fraction K α γ
      (max a z.1) (spaceEquiv (z.2.1+z.1 • z.2.2)) = _
    rw [max_eq_right ht,spaceEquiv_apply]
    exact GeometricBackground.background_eq_beamMeasure
      (zero_lt_one.trans_le E.phase_mem.1) hK hα.le hγ.le hr (ha.le.trans ht)
      η E.fraction _ hactive
  apply Measure.ext_of_lintegral
  intro f hf
  rw [E.characteristicGainKernel_lintegral_normal ha hK hα hγ z hf,
    lintegral_smul_measure,beamNormalCharacteristicKernel_lintegral _ z hf]
  rw [normalGainKernel_eq_smul_of_measure_eq L (beamPartnerKernel b)
    (hotCharacteristicEquiv z).1 (characteristicBeamPoint z) z.2.2 _ he,
    lintegral_smul_measure,smul_eq_mul]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual localized positive Duhamel identity as an equality of measures -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_positive_measure_identity
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C)
    {β : Velocity × Velocity → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t =
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s+
      ENNReal.ofReal (Real.exp (-C*t)) • WeakTime.phaseIncrement
        (WeakTime.timeWeightedSource a A C (WeakTime.weightedPhaseSource
          (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) β)+
        positiveDensityMeasure volume (WeakTime.dampedResidual a A C
          (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))
          (WeakTime.phaseWeight β (E.toHotLimitExtraction.characteristicLossDensity a A R)))) s t := by
  obtain ⟨R,hR,hbalance⟩ := E.characteristic_damped_measure_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  refine ⟨R,hR,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst
  exact WeakTime.undamp_measure_balance _ _ hsa hta (ht hsa hta hst)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Time-restricted actual cap input in five gains at nonaxial endpoints -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_nonaxial_cutoff_five_gain (E : HotLimitExtraction S)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A T R₀ b₀ X : ℝ}
    (ha : 0 < a) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
    (hA : ENNReal.ofReal A < E.horizon)
    (hz : ∀ R, (E.hotLimit ∘ EuclideanFlight.hotChart)
      =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a T)
    (hposition : ∀ n, ‖WithLp.toLp 2 (states n).2.1‖ ≤ X)
    (hvelocity : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ velocityWindow R₀ b₀) :
    Tendsto (fun n => iterate a
      (positiveMainKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      ({z : Published.KineticPhase | z.1.1 ∈ Icc 0 A}.indicator
        (fun z => ENNReal.ofReal (S.boundedHotRatio (E.indices n) z))) 5 (toKinetic (states n)))
      atTop (𝓝 0) := by
  let f : ℕ → Published.KineticPhase → ℝ≥0∞ :=
    fun n z => ENNReal.ofReal (S.boundedHotRatio (E.indices n) z)
  let D := {z : Published.KineticPhase | z.1.1 ∈ Icc 0 A}
  let g := fun n => D.indicator (f n)
  have hD : MeasurableSet D := measurableSet_Icc.preimage measurable_fst.fst
  have hf (n) : Measurable (f n) :=
    (S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n)).ennreal_ofReal
  have hg (n) : Measurable (g n) := (hf n).indicator hD
  have hgB (n z) : g n z ≤ ENNReal.ofReal 2 :=
    (indicator_le_self _ _ z).trans
      (ENNReal.ofReal_le_ofReal (S.boundedHotRatio_bounds (E.indices n) z).2)
  have hL (C : Set Published.KineticPhase) (hC : IsCompact C) :
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0) := by
    exact EuclideanFlight.time_cutoff_compact_L1
      (fun n => S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n))
      (fun n z => (S.boundedHotRatio_bounds (E.indices n) z).1)
      (fun R V hV => E.zero_boundedHotRatio_L1 hs₀ hsmax hη hηmax hK hd₀.le hq₂ hA hV (hz R)) C hC
  have ht := selected_five_nonaxial_tendsto hMityagin hK hα hγ hq₁ hq₂ ha hR₀ hb₀
    hs₀ hsmax hη hηmax hd₀ hdmax (zero_lt_one.trans_le E.phase_mem.1)
    (fun n => S.radius (E.indices n)) (fun n => S.radius_pos hs₀ (E.indices n))
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop) E.phase_limit
    (fun n => F.indices (E.indices n)) t₀ x v hv states hstates htime hposition hvelocity
    ENNReal.ofReal_ne_top hg hgB hL
  have ht'' : Tendsto (fun n => (2:ℝ≥0∞)^5*iterate a
      (selectedFreeKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      (g n) 5 (toKinetic (states n))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht
      (Or.inr (by norm_num : (2:ℝ≥0∞)^5 ≠ ∞))
  apply ht''.congr'
  exact Eventually.of_forall (fun n => (congrFun
    (iterate_add_self a _ (hg n) 5) (toKinetic (states n))).symm)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A bounded attenuation rate on every compact characteristic phase test -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristic_loss_projection_bound (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) {a A : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hA : ENNReal.ofReal A < E.horizon) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {φ : Velocity × Velocity → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hn : ∀ p, 0 ≤ φ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, ∀ᵐ t ∂volume,
      WeakTime.phaseProjection (E.characteristicLossDensity a A R) φ t ≤
        C*WeakTime.phaseProjection (cylinderPullback a A R E.hotLimit) φ t := by
  obtain ⟨V,hVpos,hV⟩ := hc.isCompact.isBounded.exists_pos_norm_le
  let C := (GeometricBackground.lossCoefficient K α γ/a)*(V+1+α)
  have hcoef : 0 ≤ GeometricBackground.lossCoefficient K α γ/a :=
    div_nonneg (GeometricBackground.lossCoefficient_nonneg hK α γ) ha.le
  have hC : 0 ≤ C := mul_nonneg hcoef (by positivity)
  refine ⟨C,hC,?_⟩
  intro R
  have hp (u : CharacteristicPhase) :
      φ u.2*E.characteristicLossDensity a A R u ≤
        C*(φ u.2*cylinderPullback a A R E.hotLimit u) := by
    by_cases hzero : φ u.2 = 0
    · simp only [hzero,zero_mul,mul_zero,le_refl]
    have hv : ‖(hotCharacteristicEquiv u).2‖ ≤ V :=
      (norm_snd_le u.2).trans (hV _ (subset_tsupport φ hzero))
    let z := hotCharacteristicEquiv u
    change φ u.2*(coldCylinderSet a A R).indicator
        (fun z => E.hotLimit z*GeometricBackground.frequency E.phase η E.fraction K α γ
          z.1.1 z.1.2 z.2) z ≤
      C*(φ u.2*(coldCylinderSet a A R).indicator E.hotLimit z)
    by_cases hz : z ∈ coldCylinderSet a A R
    · rw [indicator_of_mem hz,indicator_of_mem hz]
      have hf := GeometricBackground.frequency_slab_bound (η := η)
        (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ ha hz.1.1.1 z.1.2 z.2
      have hfc : GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2 ≤ C :=
        hf.trans (mul_le_mul_of_nonneg_left (by dsimp only [z] at *; linarith only [hv]) hcoef)
      calc
        _ = (φ u.2*E.hotLimit z)*GeometricBackground.frequency E.phase η E.fraction K α γ
            z.1.1 z.1.2 z.2 := by ring
        _ ≤ (φ u.2*E.hotLimit z)*C :=
          mul_le_mul_of_nonneg_left hfc (mul_nonneg (hn _) (E.hotLimit_nonneg z))
        _ = _ := by ring
    · simp only [indicator_of_notMem hz,mul_zero,le_refl]
  obtain ⟨B,hB⟩ := hφ.bounded_above_of_compact_support hc
  have hm : AEStronglyMeasurable (fun u : CharacteristicPhase => φ u.2) volume :=
    (hφ.measurable.comp measurable_snd).aestronglyMeasurable
  have hl : Integrable (fun u : CharacteristicPhase => φ u.2*E.characteristicLossDensity a A R u)
      ((volume : Measure ℝ).prod volume) :=
    (E.characteristicLossDensity_integrable ha haA hK hα hγ hq).bdd_mul hm
      (ae_of_all _ (fun u => hB u.2))
  have hf : Integrable (fun u : CharacteristicPhase => φ u.2*cylinderPullback a A R E.hotLimit u)
      ((volume : Measure ℝ).prod volume) :=
    (cylinderPullback_integrable (E.physical_weak_cylinder S hs₀ ha.le hA R).2.1).bdd_mul hm
      (ae_of_all _ (fun u => hB u.2))
  filter_upwards [hl.prod_right_ae,hf.prod_right_ae] with t hlt hft
  have hi := integral_mono hlt (hft.const_mul C) (fun p => hp (t,p))
  simpa only [WeakTime.phaseProjection,integral_const_mul] using hi

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A one-dimensional weak balance for each actual compact phase test -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_weak_time_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon)
    {φ : Velocity × Velocity → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hn : ∀ p, 0 ≤ φ p) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport φ,
        hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      HasCompactSupport θ → tsupport θ ⊆ Ioo a A →
      (∫ t, deriv θ t*WeakTime.phaseProjection (cylinderPullback a A R E.hotLimit) φ t)+
        (∫ t, θ t ∂WeakTime.timeSource
          (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) φ)-
        (∫ t, θ t*WeakTime.phaseProjection
          (E.toHotLimitExtraction.characteristicLossDensity a A R) φ t) = 0 := by
  obtain ⟨R,Rₑ,hR,hcover,hloc⟩ := exists_timePhase_cylinder_cover a A hc
  refine ⟨R,hR,hcover,?_⟩
  intro θ hθ hθc hθs
  obtain ⟨C,hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  obtain ⟨D,hD⟩ := hθ.continuous.bounded_above_of_compact_support hθc
  obtain ⟨D',hD'⟩ := (hθ.continuous_deriv (by simp)).bounded_above_of_compact_support hθc.deriv
  have hA := (ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB
  have hi := cylinderPullback_integrable
    (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le hA R).2.1
  have hli := E.toHotLimitExtraction.characteristicLossDensity_integrable (R := R) ha haA.le hK hα hγ hq₂
  rw [WeakTime.phaseProjection_test_integral hi hφ.continuous.measurable hC
      (hθ.continuous_deriv (by simp)).measurable hD',
    WeakTime.phaseProjection_test_integral hli hφ.continuous.measurable hC
      hθ.continuous.measurable hD,
    WeakTime.timeSource_integral _ hφ.continuous.measurable hn hθ.continuous.measurable]
  change _+(∫ u, θ u.1*φ u.2 ∂((2 : ℝ≥0) • sourcePullback _))-_ = 0
  have hm : Measurable (fun u : CharacteristicPhase => θ u.1*φ u.2) :=
    (hθ.continuous.measurable.comp measurable_fst).mul (hφ.continuous.measurable.comp measurable_snd)
  rw [integral_smul_nnreal_measure,sourcePullback_integral _ hm]
  change _+2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
    ∂incomingGainMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))-_ = 0
  rw [cylinderPullback_integral]
  change _+_- (∫ u, (θ u.1*φ u.2)*cylinderPullback a A R
    (fun z => E.hotLimit z*GeometricBackground.frequency E.phase η E.fraction K α γ
      z.1.1 z.1.2 z.2) u) = 0
  rw [cylinderPullback_integral]
  have hψ : Measurable (fun z : HotKineticPhase =>
      θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2) :=
    hm.comp hotCharacteristicEquiv.symm.measurable
  have hψB (z : HotKineticPhase) :
      |θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2| ≤ D*C := by
    rw [abs_mul]
    exact mul_le_mul (hD _) (hC _) (abs_nonneg _) ((norm_nonneg (θ 0)).trans (hD 0))
  have hlocθ := hloc θ hθs
  have hb := E.characteristic_test_balance hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA.le hAB hB hR
    (timePhaseTest_contDiff hθ hφ) (timePhaseTest_compact hθc hc) hlocθ.1 hlocθ.2
  simp_rw [timeDerivative_timePhaseTest hθ hφ] at hb
  change (∫ z, (deriv θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+
    (2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingGainMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))-
    (∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingLossMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) = 0 at hb
  rw [E.toHotLimitExtraction.actual_loss_cylinder_integral ha haA.le hK hα hγ hq₂ hψ hψB] at hb
  linarith only [hb]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot time traces obey the expanding-box fourth-power cap -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotLimit_cap_global (E : HotLimitExtraction S) :
    ∀ᵐ z ∂volume, 0 ≤ z.1.1 → E.hotLimit z ≤ (z.1.1+E.fraction)*H q z.2 := by
  have hh (n : ℕ) : ∀ᵐ z ∂volume, z ∈ hotWindowSet (n+1) (n+1) →
      E.hotLimit z ≤ (z.1.1+E.fraction)*H q z.2 := by
    have hc := E.hotLimit_cap (n+1) (n+1)
    rw [hotWindowVolume_eq,ae_restrict_iff' (hotWindowSet_measurable _ _)] at hc
    exact hc
  filter_upwards [ae_all_iff.mpr hh] with z hz
  intro ht
  obtain ⟨n,hn⟩ := exists_nat_gt (max z.1.1 ‖z.1.2‖)
  apply hz n
  refine ⟨⟨⟨ht,?_⟩,?_⟩,mem_univ _⟩
  · have h := (le_max_left z.1.1 ‖z.1.2‖).trans_lt hn
    linarith
  · rw [Metric.mem_closedBall,dist_zero_right]
    have h := (le_max_right z.1.1 ‖z.1.2‖).trans_lt hn
    linarith

theorem HotLimitExtraction.characteristic_phase_cap (E : HotLimitExtraction S)
    (a A R : ℝ) {β : WeakTime.Phase → ℝ} (hβ₁ : ∀ p, β p ≤ 1) :
    ∀ᵐ t ∂volume, ∀ᵐ p ∂volume, 0 ≤ t →
      WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit) (t,p) ≤ (t+1)*H q p.2 := by
  have hg : ∀ᵐ u : CharacteristicPhase ∂volume, 0 ≤ u.1 →
      E.hotLimit (hotCharacteristicEquiv u) ≤ (u.1+E.fraction)*H q u.2.2 :=
    hotCharacteristic_measurePreserving.quasiMeasurePreserving.ae E.hotLimit_cap_global
  rw [Measure.volume_eq_prod] at hg
  filter_upwards [Measure.ae_ae_of_ae_prod hg] with t ht
  filter_upwards [ht] with p hp
  intro ht0
  have hn : 0 ≤ cylinderPullback a A R E.hotLimit (t,p) :=
    indicator_nonneg (fun z _ => E.hotLimit_nonneg z) _
  calc
    _ ≤ cylinderPullback a A R E.hotLimit (t,p) := by
      exact (mul_le_mul_of_nonneg_right (hβ₁ p) hn).trans_eq (one_mul _)
    _ ≤ E.hotLimit (hotCharacteristicEquiv (t,p)) := by
      by_cases hz : hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R
      · simp only [cylinderPullback,Function.comp_def,indicator_of_mem hz,le_refl]
      · simpa only [cylinderPullback,Function.comp_def,indicator_of_notMem hz] using
          E.hotLimit_nonneg (hotCharacteristicEquiv (t,p))
    _ ≤ (t+E.fraction)*H q p.2 := hp ht0
    _ ≤ (t+1)*H q p.2 :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl E.fraction_mem.2) (H_nonneg q p.2)

theorem HotLimitExtraction.characteristic_lateBox_cap (E : HotLimitExtraction S)
    (a A R : ℝ) {β : WeakTime.Phase → ℝ} (hβ : Measurable β) (hβ₁ : ∀ p, β p ≤ 1)
    {κ d : ℝ} (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hq : q < 2) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t
        ((flight t) ⁻¹' ReferenceGeometry.lateBox κ d t) ≤
      ENNReal.ofReal (ReferenceGeometry.lateBoxCapConstant q κ d*(1+t)^4) := by
  filter_upwards [E.characteristic_phase_cap a A R hβ₁] with t ht
  intro ht0
  apply density_movingBox_bound hq hκ hd ht0
  · exact hβ.mul
      (((E.hotLimit_measurable.indicator (coldCylinderSet_measurable a A R)).comp
        hotCharacteristicEquiv.measurable).comp (measurable_const.prodMk measurable_id))
  · exact ht.mono (fun p hp => hp ht0)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual nonaxial cap gain also vanishes at the limiting horizon -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_closed_nonaxial_five_gain (E : HotLimitExtraction S)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a T R₀ b₀ X : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
    (hTU : ENNReal.ofReal T ≤ E.horizon)
    (hz : ∀ A, 0 < A → A < T → ∀ R, (E.hotLimit ∘ EuclideanFlight.hotChart)
      =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a T)
    (hposition : ∀ n, ‖WithLp.toLp 2 (states n).2.1‖ ≤ X)
    (hvelocity : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ velocityWindow R₀ b₀) :
    Tendsto (fun n => iterate a
      (positiveMainKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      (fun z => ENNReal.ofReal (S.boundedHotRatio (E.indices n) z)) 5 (toKinetic (states n)))
      atTop (𝓝 0) := by
  let J := fun n => positiveMainKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n))
  let f := fun n (z : Published.KineticPhase) => ENNReal.ofReal (S.boundedHotRatio (E.indices n) z)
  have hf (n) : Measurable (f n) :=
    (S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n)).ennreal_ofReal
  have hC (n z) (hz : z.1.1 ∈ Icc a T) : J n z univ ≤
      ENNReal.ofReal ((2*JetCoreSheet.growthConstant K α γ q)/a) := by
    apply (positiveMainKernel_bound (S.radius_pos hs₀ (E.indices n)) hs₀ hsmax hη hηmax hK
      hα hγ hd₀ hdmax hq₁ hq₂ (F.indices (E.indices n)) z (ha.trans_le hz.1)).trans
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num)
      (JetCoreSheet.growthConstant_nonneg hK α γ q)) ha hz.1
  apply five_tendsto_of_time_cutoffs hT J ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hC hf
    (fun n z _ => ENNReal.ofReal_le_ofReal (S.boundedHotRatio_bounds (E.indices n) z).2)
    (fun n => toKinetic (states n)) htime
  intro δ hδ hδT
  have hApos : 0 < T-δ := sub_pos.mpr hδT
  have hAT : T-δ < T := sub_lt_self T hδ
  have hAU : ENNReal.ofReal (T-δ) < E.horizon :=
    ((ENNReal.ofReal_lt_ofReal_iff hT).mpr hAT).trans_le hTU
  have ht := E.zero_nonaxial_cutoff_five_gain hMityagin hs₀ hsmax hη hηmax hK hα hγ
    hd₀ hdmax hq₁ hq₂ ha hR₀ hb₀ hAU (hz (T-δ) hApos hAT)
    t₀ x v hv states hstates htime hposition hvelocity
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  have he (z : Published.KineticPhase) (hzt : z.1.1 ∈ Icc a T) :
      {y : Published.KineticPhase | y.1.1 ∈ Icc 0 (T-δ)}.indicator (f n) z =
        {y : Published.KineticPhase | y.1.1 ≤ T-δ}.indicator (f n) z := by
    by_cases hy : z.1.1 ≤ T-δ
    · rw [indicator_of_mem (show z ∈ {y : Published.KineticPhase | y.1.1 ∈ Icc 0 (T-δ)} from
        ⟨ha.le.trans hzt.1,hy⟩),indicator_of_mem
          (show z ∈ {y : Published.KineticPhase | y.1.1 ≤ T-δ} from hy)]
    · rw [indicator_of_notMem (show z ∉ {y : Published.KineticPhase | y.1.1 ∈ Icc 0 (T-δ)} from
        fun h => hy h.2),indicator_of_notMem
          (show z ∉ {y : Published.KineticPhase | y.1.1 ≤ T-δ} from hy)]
  exact le_antisymm (iterate_slab_mono (J n) (fun z hz => (he z hz).le) 5 _ (htime n))
    (iterate_slab_mono (J n) (fun z hz => (he z hz).ge) 5 _ (htime n))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Retaining full support coverage in the damped hot balance -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_characteristic_damped_measure_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C)
    {β : Velocity × Velocity → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseSlice (WeakTime.timeWeightedDensity a A C
        (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))) t =
      WeakTime.phaseSlice (WeakTime.timeWeightedDensity a A C
        (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))) s+
      WeakTime.phaseIncrement
        (WeakTime.timeWeightedSource a A C (WeakTime.weightedPhaseSource
          (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) β)+
        positiveDensityMeasure volume (WeakTime.dampedResidual a A C
          (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))
          (WeakTime.phaseWeight β (E.toHotLimitExtraction.characteristicLossDensity a A R)))) s t := by
  obtain ⟨R,hR,hcover,hweak⟩ := E.covered_characteristic_weak_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hβc
  refine ⟨R,hR,hcover,?_⟩
  let _ := E.toHotLimitExtraction.incomingGainMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  have : IsFiniteMeasure (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) := by
    unfold HotLimitExtraction.characteristicGainMeasure
    infer_instance
  have hi := (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le
    ((ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB) R).2.1
  have hLi := E.toHotLimitExtraction.characteristicLossDensity_integrable (R := R)
    ha haA.le hK hα hγ hq₂
  have hn (u : CharacteristicPhase) : 0 ≤ cylinderPullback a A R E.hotLimit u :=
    indicator_nonneg (fun z _ => E.toHotLimitExtraction.hotLimit_nonneg z) _
  apply WeakTime.ae_localized_damped_measure_balance haA hC (cylinderPullback_integrable hi)
    hLi (ae_of_all _ hn) _ hβ hβc hβn
  · apply ae_of_all
    intro u hu
    by_cases hz : β u.2 = 0
    · simp only [hz,zero_mul,mul_zero,le_refl]
    rw [E.toHotLimitExtraction.characteristicLossDensity_factor]
    have hb := hfrequency u hu (subset_tsupport β hz)
    have hp : 0 ≤ β u.2*cylinderPullback a A R E.hotLimit u := mul_nonneg (hβn _) (hn u)
    nlinarith only [mul_le_mul_of_nonneg_left hb hp]
  · intro φ hφ hc hφn hφβ θ hθ hθc hθs
    have hb := hweak φ hφ hc hφn hφβ θ hθ hθc hθs
    rw [E.toHotLimitExtraction.characteristicLossMeasure_eq ha haA.le hK hα hγ hq₂,
      positiveDensityMeasure_integral hLi.aemeasurable
        (ae_of_all _ (E.toHotLimitExtraction.characteristicLossDensity_nonneg a A R))] at hb
    exact hb

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
