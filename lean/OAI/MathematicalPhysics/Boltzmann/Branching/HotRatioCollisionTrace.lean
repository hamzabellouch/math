import OAI.MathematicalPhysics.Boltzmann.Approximation.CapActualLossDensity
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMixedPositiveBound
import OAI.MathematicalPhysics.Boltzmann.Branching.HotChartHomeomorph
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.MixedPhysicalMeasures
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseSliceLocalization
import OAI.MathematicalPhysics.Boltzmann.Branching.ZeroProfileParameters
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteHorizonRatio

namespace OAI

section

/-! # Finite limiting horizon transfers vanishing full mass to the hot scale -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.full_vanishing_implies_hot_box_vanishing (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : 0 ≤ q) (hqmax : q < 2)
    (hfinite : E.horizon < ⊤)
    (hfull : ∀ j, Tendsto (fun n => scaledBoxMass (shrinkingHorizon F.horizonScale n)
      (EuclideanFlight.density q (F.approximation n).solution.value) j) atTop (𝓝 0))
    {A R ε : ℝ} (hA : 0 ≤ A) (hAmax : A < 1) (hR : 0 ≤ R) (hε : 0 < ε) :
    Tendsto (fun n => ∫ z in awayKineticBox A R ε, S.euclideanHot (E.indices n) z)
      atTop (𝓝 0) := by
  obtain ⟨hc,hcmax,hrho⟩ := E.radius_horizon_ratio hs₀ hfinite
  let c := E.horizon.toReal⁻¹
  let ρ := fun n => S.radius (E.indices n)/shrinkingHorizon F.horizonScale (E.indices n)
  obtain ⟨j,hj2,hj,hjε⟩ := exists_separationBox_parameters hR hε
  have htime : ∀ᶠ n in atTop, ρ n*A ≤ 1 := by
    have hca : c*A < 1 := (mul_le_mul_of_nonneg_right hcmax hA).trans_lt (by simpa using hAmax)
    filter_upwards [(hrho.mul_const A).eventually (gt_mem_nhds hca)] with n hn
    exact hn.le
  have hspace : ∀ᶠ n in atTop, ρ n*R ≤ (j:ℝ)+1 := by
    filter_upwards [hrho.eventually (gt_mem_nhds (hcmax.trans_lt (by norm_num : (1:ℝ)<2)))] with n hn
    exact (mul_le_mul_of_nonneg_right hn.le hR).trans hj2
  have hlim := ((hrho.pow 5).inv₀ (pow_ne_zero 5 hc.ne')).mul
    ((hfull j).comp E.indices_strict.tendsto_atTop)
  have hlim' : Tendsto (fun n => ((ρ n)^5)⁻¹*scaledBoxMass
      (shrinkingHorizon F.horizonScale (E.indices n))
      (EuclideanFlight.density q (F.approximation (E.indices n)).solution.value) j) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def,ρ] using hlim
  apply squeeze_zero' _ _ hlim'
  · exact Filter.Eventually.of_forall (fun n => integral_nonneg
      (fun z => (S.euclideanHot_full_bound hs₀ hsmax hη hηmax hK hd₀ hqmax _ z).1))
  · filter_upwards [htime,hspace] with n hnt hnx
    exact (S.hot_box_mass_comparison hs₀ hsmax hη hηmax hK hd₀ hq hqmax (E.indices n)
      (shrinkingHorizon_pos F.horizonScale_pos _) hAmax.le hnt hnx hj hjε).2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Measurability and the physical fourth-power bound for the hot box mass -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem hotLateBoxMass_measurable {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    (hf : Measurable f) (κ d : ℝ) : Measurable (hotLateBoxMass f κ d) := by
  let S : Set (ℝ × WeakTime.Phase) := {z | flight z.1 z.2 ∈ lateBox κ d z.1}
  have hS : MeasurableSet S := by
    change MeasurableSet {z : ℝ × WeakTime.Phase |
      ‖z.2.1+z.1 • z.2.2-(κ*z.1) • firstAxis‖ < d*κ*z.1 ∧ ‖z.2.2‖ < 5}
    have hx : Measurable (fun z : ℝ × WeakTime.Phase =>
        ‖z.2.1+z.1 • z.2.2-(κ*z.1) • firstAxis‖) := by fun_prop
    have hr : Measurable (fun z : ℝ × WeakTime.Phase => d*κ*z.1) := by fun_prop
    have hv : Measurable (fun z : ℝ × WeakTime.Phase => ‖z.2.2‖) := by fun_prop
    exact (measurableSet_lt hx hr).inter (measurableSet_lt hv measurable_const)
  have hh : Measurable (S.indicator (fun z => ENNReal.ofReal (f (hotCharacteristicEquiv z)))) :=
    (hf.comp hotCharacteristicEquiv.measurable).ennreal_ofReal.indicator hS
  have he : hotLateBoxMass f κ d = fun t => ∫⁻ p, S.indicator
      (fun z => ENNReal.ofReal (f (hotCharacteristicEquiv z))) (t,p) := by
    funext t
    rw [hotLateBoxMass,hotPhaseSlice,positiveDensityMeasure,
      withDensity_apply _ ((lateBox_measurable κ d t).preimage (flight_measurePreserving t).measurable),
      ← lintegral_indicator ((lateBox_measurable κ d t).preimage (flight_measurePreserving t).measurable)]
    rfl
  rw [he]
  exact Measurable.lintegral_prod_right
    (f := fun t p => S.indicator (fun z => ENNReal.ofReal (f (hotCharacteristicEquiv z))) (t,p)) hh

theorem hotLateBoxMass_eq_physical {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    (hf : Measurable f) (κ d t : ℝ) :
    hotLateBoxMass f κ d t =
      positiveDensityMeasure volume (fun p : Velocity × Velocity => f (hotChart ((t,p.1),p.2)))
        (lateBox κ d t) := by
  unfold hotLateBoxMass hotPhaseSlice positiveDensityMeasure
  rw [withDensity_apply _ ((lateBox_measurable κ d t).preimage (flight_measurePreserving t).measurable),
    withDensity_apply _ (lateBox_measurable κ d t)]
  have hm : Measurable (fun p : Velocity × Velocity =>
      ENNReal.ofReal (f (hotChart ((t,p.1),p.2)))) :=
    ((hf.comp hotChart.measurable).comp
      (show Measurable (fun p : Velocity × Velocity => ((t,p.1),p.2)) by fun_prop)).ennreal_ofReal
  exact (flight_measurePreserving t).setLIntegral_comp_preimage (lateBox_measurable κ d t) hm

theorem hotLateBoxMass_bound {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    (hf : Measurable f) {q κ d t : ℝ} (hq : q < 2) (hκ : 0 ≤ κ) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hcap : ∀ᵐ p : Velocity × Velocity ∂volume,
      f (hotChart ((t,p.1),p.2)) ≤ (t+1)*VelocityWeight.H q p.2) :
    hotLateBoxMass f κ d t ≤ ENNReal.ofReal (lateBoxCapConstant q κ d*(1+t)^4) := by
  rw [hotLateBoxMass_eq_physical hf]
  exact density_lateBox_bound hq hκ hd ht hcap

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Polynomial control of the essential norm of the actual mild remainder -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem zero_seed_bound {T L S R M C B D δ : ℝ} {m : ℕ}
    (hT : 0 ≤ T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B) (hBD : B ≤ D) (hD : 0 ≤ D)
    (hδ : 0 < δ) (hsmall : C*D*T ≤ 1) (hm : M+2 ≤ (m+1 : ℕ))
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S)
    (hf : ∀ u, 0 ≤ f u ∧ f u ≤ R)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ 0)
    (hfix : ∀ u, f u = PositiveIntegral.value T L JetBarrier.flight f₀ g u)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤
        ZeroProfile.source M C B δ m u.1 (size (fun p => f (u.1,p)))+
          L*size (fun p => f (u.1,p))) :
    ∀ t ∈ Icc 0 T, size (fun p => f (t,p)) ≤ ZeroProfile.profile D m t := by
  let z (t : ℝ) := size (fun p => f (t,p))
  have habs (u) : |f u| ≤ R := by rw [abs_of_nonneg (hf u).1]; exact (hf u).2
  have hzc : Continuous z := continuous_size hT hL hS hR hgm hfm hg habs hfix
  have hden : ContinuousOn (fun t => M/(t+δ)) (Icc 0 T) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      (fun t ht => ne_of_gt (by linarith [ht.1]))
  have hwc : ContinuousOn (fun t => ZeroProfile.source M C B δ m t (z t)+L*z t) (Icc 0 T) :=
    (((hden.mul hzc.continuousOn).add ((hzc.continuousOn.pow 2).const_mul C)).add
      ((continuousOn_id.pow m).const_mul B)).add (hzc.continuousOn.const_mul L)
  apply ZeroProfile.le_profile hM hC hBD hD hδ hT hT₁ hL hR hsmall hm hzc.continuousOn
  · intro t _
    exact ⟨size_nonneg _,size_le hR (hfm.comp (measurable_const.prodMk measurable_id)) (fun p => habs (t,p))⟩
  · intro t ht
    have hw : IntervalIntegrable (fun r => ZeroProfile.source M C B δ m r (z r)+L*z r)
        volume 0 T := hwc.intervalIntegrable_of_Icc hT
    have hwn (r : ℝ) (hr : r ∈ Icc 0 T) :
        0 ≤ ZeroProfile.source M C B δ m r (z r)+L*z r := by
      have hz : 0 ≤ z r := size_nonneg _
      have hr0 : 0 ≤ r := hr.1
      have hd : 0 < r+δ := by linarith [hr.1]
      unfold ZeroProfile.source
      positivity
    simpa only [mul_zero,zero_add] using
      mild_size_le hT hL (by rfl : (0:ℝ) ≤ 0) ht hgm hfm hg hw hwn hinit hsource
        (fun u => (hf u).1) hfix

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # The actual weak hot limit tested on bounded off-axis boxes -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.euclidean_weak_awayBox (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    {A : ℝ} (hA : ENNReal.ofReal A < E.horizon) (R ε : ℝ) :
    Published.WeakL1Converges (volume.restrict (awayKineticBox A R ε))
      (fun n => S.euclideanHot (E.indices n)) (E.hotLimit ∘ EuclideanFlight.hotChart) := by
  obtain ⟨R',hR'⟩ := (isCompact_closedBall (0:Velocity) R).exists_bound_of_continuousOn
    EuclideanFlight.spaceEquiv_continuous.continuousOn
  have hc : awayKineticBox A R ε ⊆ (EuclideanFlight.hotBaseSet A R' ×ˢ (univ : Set Velocity)) := by
    intro z hz
    refine ⟨⟨hz.1.1.1,?_⟩,mem_univ _⟩
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hR' _ hz.1.1.2
  have hw := (E.euclidean_weak S hs₀ hsmax hη hηmax hK hd₀ hq hA R').restrict
    (measurableSet_awayKineticBox A R ε)
  rw [EuclideanFlight.hotBaseVolume_eq,← Measure.restrict_univ (μ := (volume : Measure Velocity)),
    Measure.prod_restrict,← Measure.volume_eq_prod,Measure.restrict_restrict_of_subset hc] at hw
  exact hw

theorem HotLimitExtraction.full_vanishing_implies_zero_box (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : 0 ≤ q) (hqmax : q < 2)
    (hfinite : E.horizon < ⊤)
    (hfull : ∀ j, Tendsto (fun n => scaledBoxMass (shrinkingHorizon F.horizonScale n)
      (EuclideanFlight.density q (F.approximation n).solution.value) j) atTop (𝓝 0))
    {A R ε : ℝ} (hA : 0 ≤ A) (hAmax : A < 1) (hR : 0 ≤ R) (hε : 0 < ε) :
    E.hotLimit ∘ EuclideanFlight.hotChart =ᵐ[volume.restrict (awayKineticBox A R ε)] 0 := by
  have hAU : ENNReal.ofReal A < E.horizon :=
    (show ENNReal.ofReal A < 1 by
      simpa only [ENNReal.ofReal_one] using
        (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hAmax).trans_le E.horizon_ge
  have hw := E.euclidean_weak_awayBox hs₀ hsmax hη hηmax hK hd₀ hqmax hAU R ε
  have ht := hw.2.2 (fun _ => 1) measurable_const ⟨1,by simp⟩
  simp only [one_mul] at ht
  have hz := E.full_vanishing_implies_hot_box_vanishing hs₀ hsmax hη hηmax hK hd₀ hq hqmax
    hfinite hfull hA hAmax hR hε
  apply (integral_eq_zero_iff_of_nonneg (fun z => E.hotLimit_nonneg _) hw.2.1).mp
  exact tendsto_nhds_unique ht hz

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Collision traces of the bounded hot representative -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem boundedHotRatio_collision_trace (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {t : ℝ}
    (ht : S.radius n*t ∈ Icc 0 (shrinkingHorizon F.horizonScale n)) (htmax : t ≤ 1) :
    ∀ᵐ p : Velocity × Velocity,
      mixedGainDensity (F.indices n+1) ((F.approximation n).dilatedCold (S.radius n))
        (fun z => H q z.2*S.boundedHotRatio n z) ((t,p.1),p.2) =
      mixedGainDensity (F.indices n+1) ((F.approximation n).dilatedCold (S.radius n))
        (S.euclideanHot n) ((t,p.1),p.2) ∧
      KineticCollisionNullSets.gain (F.indices n+1)
        (fun z => H q z.2*S.boundedHotRatio n z) ((t,p.1),p.2) =
      KineticCollisionNullSets.gain (F.indices n+1) (S.euclideanHot n) ((t,p.1),p.2) := by
  have he := S.boundedHotRatio_preserves_trace hs₀ hsmax hη hηmax hK hd₀ hq n ht htmax
  rw [Measure.volume_eq_prod] at he
  let c : Velocity × Velocity → ℝ := fun p =>
    (F.approximation n).dilatedCold (S.radius n) ((t,p.1),p.2)
  have hm := mixedGain_congr_ae (volume : Measure Velocity) (F.indices n+1)
    (Filter.EventuallyEq.refl (f := c) _)
    (show (fun p : Velocity × Velocity => H q p.2*S.boundedHotRatio n ((t,p.1),p.2))
      =ᵐ[(volume : Measure Velocity).prod volume]
      (fun p => S.euclideanHot n ((t,p.1),p.2)) from he)
  have hg := KineticCollisionNullSets.gain_congr (volume : Measure Velocity) he (F.indices n+1)
  rw [Measure.volume_eq_prod]
  filter_upwards [hm,hg] with p hp hq
  exact ⟨hp,hq⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
