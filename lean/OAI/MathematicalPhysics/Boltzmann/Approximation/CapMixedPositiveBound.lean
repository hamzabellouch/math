import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLimitTransport
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMixedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapNonlinearHotLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedLateBoxPhysicalBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.HotChartHomeomorph
import OAI.MathematicalPhysics.Boltzmann.Branching.MainPositiveRemainderBound
import OAI.MathematicalPhysics.Boltzmann.Branching.RescaledBoundedGain
import OAI.MathematicalPhysics.Boltzmann.Branching.RescaledColdMajorant
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedPairCompactness

namespace OAI

section

/-! # The actual cold density in the Euclidean dilation coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.dilatedCold {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (r : ℝ) (z : KineticPhase) : ℝ :=
  r*(H q z.2*F.coldTotal (r*z.1.1,(JetPeriodicDatum.spatialMap (r • z.1.2),z.2)))

theorem CapApproximation.dilatedCold_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) (r : ℝ) :
    Measurable (F.dilatedCold r) := by
  have hc := (F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).1
  have hx : Measurable (fun z : KineticPhase =>
      (r*z.1.1,(JetPeriodicDatum.spatialMap (r • z.1.2),z.2))) := by
    apply Measurable.prodMk (by fun_prop)
    exact ((JetPeriodicDatum.spatialMap_measurePreserving.measurable.comp
      (by fun_prop)).prodMk measurable_snd)
  exact measurable_const.mul (((ChartKernel.measurable_H q).comp measurable_snd).mul (hc.comp hx))

theorem CapApproximation.dilatedCold_nonneg {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (hr : 0 ≤ r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) (z : KineticPhase) :
    0 ≤ F.dilatedCold r z :=
  mul_nonneg hr (mul_nonneg (H_nonneg q z.2)
    ((F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).2 _).2.1)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The positive Duhamel gain uses the actual hot and atomic cold particles -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.damped_gain_hot_integral (E : HotLimitExtraction S)
    {a A R C s t : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) (hC : 0 ≤ C) (hs : a < s) (ht : t < A)
    {ψ β : WeakTime.Phase → ℝ} (hψ : Measurable ψ) (hβ : Measurable β)
    (hβn : ∀ p, 0 ≤ β p) {P B : ℝ} (hψB : ∀ p, |ψ p| ≤ P) (hβB : ∀ p, |β p| ≤ B) :
    (∫ p, ψ p ∂WeakTime.dampedSourceIncrement a A C s t
      (WeakTime.weightedPhaseSource (E.characteristicGainMeasure ha hK hα hγ A R) β)) =
    ∫ x, ∫ w, E.cappedHot (x,w)*
      (∫ v, ∫ ω, collisionKernel v w ω*
        (WeakTime.dampedPhaseTest C s t ψ β
          (hotCharacteristicEquiv.symm (x,scatterLeft v w ω))+
         WeakTime.dampedPhaseTest C s t ψ β
          (hotCharacteristicEquiv.symm (x,scatterRight v w ω))) ∂sphereArea
        ∂E.background (max a x.1) x.2) ∂volume ∂coldCylinderVolume a A R := by
  rw [WeakTime.dampedSourceIncrement_weighted_integral _ hs ht hψ hβ hβn]
  exact E.characteristicGain_hot_integral ha haA hK hα hγ hq
    (WeakTime.dampedPhaseTest_measurable C s t hψ hβ)
    (WeakTime.dampedPhaseTest_bound hC s t hψB hβB)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot collision equation in the coordinates of positive iteration -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem euclidean_hot_collision (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (n : ℕ) (z : KineticPhase) (hz : z.2 ∈ HotRepresentative.good q) :
    S.euclideanHotSource n z =
      2*mixedGainDensity (F.indices n+1) ((F.approximation n).dilatedCold (S.radius n))
        (S.euclideanHot n) z-
      S.euclideanHot n z*KineticCollisionNullSets.frequency (F.indices n+1)
        ((F.approximation n).dilatedCold (S.radius n)) z+
      (S.radius n)^2*collisionSource (F.indices n+1) (S.euclideanHot n) z+
      H q z.2*S.rescaledColdSource n (z.1.1,EuclideanFlight.phaseEquiv (z.1.2,z.2)) := by
  let τ : SpaceTime → ℝ × JetPrototype.Space := fun x => (x.1,JetPeriodicDatum.spatialMap x.2)
  have hc : (fun w : KineticPhase => S.rescaledColdDensity n (τ w.1,w.2)) =
      (F.approximation n).dilatedCold (S.radius n) := by
    funext w
    unfold rescaledColdDensity CapApproximation.dilatedCold τ
    change S.radius n*H q w.2*(F.approximation n).coldTotal _ = _
    rw [show S.radius n • JetPeriodicDatum.spatialMap w.1.2 =
      JetPeriodicDatum.spatialMap (S.radius n • w.1.2) from rfl]
    ring
  have hh : (fun w : KineticPhase => S.physicalHotDensity n (τ w.1,w.2)) =
      S.euclideanHot n := by
    funext w
    rw [euclideanHot_eq_rescaledHot,EuclideanFlight.phaseEquiv_apply]
    rfl
  have hi := S.rescaled_hot_collision hs₀ hsmax hη hηmax hK hd₀ hq n (τ z.1,z.2) hz
  rw [← mixedGain_base_comp (F.indices n+1) (S.rescaledColdDensity n)
      (S.physicalHotDensity n) τ z,
    ← cutoffFrequency_base_comp (F.indices n+1) (S.rescaledColdDensity n) τ z,
    ← collisionSource_base_comp (F.indices n+1) (S.physicalHotDensity n) τ z,hc,hh] at hi
  have hhpoint : S.physicalHotDensity n (τ z.1,z.2) = S.euclideanHot n z := congrFun hh z
  rw [hhpoint] at hi
  simpa only [euclideanHotSource,EuclideanFlight.phaseEquiv_apply,JetPeriodicDatum.phaseMap,τ] using hi

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # An upper bound for the actual normalized source after discarding losses -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem euclideanHotSource_le_gains (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (n : ℕ) (z : KineticPhase) (hz : z.2 ∈ HotRepresentative.good q) :
    S.euclideanHotSource n z ≤
      2*mixedGainDensity (F.indices n+1) ((F.approximation n).dilatedCold (S.radius n))
        (S.euclideanHot n) z+
      (S.radius n)^2*KineticCollisionNullSets.gain (F.indices n+1) (S.euclideanHot n) z+
      H q z.2*S.rescaledColdSource n (z.1.1,EuclideanFlight.phaseEquiv (z.1.2,z.2)) := by
  rw [S.euclidean_hot_collision hs₀ hsmax hη hηmax hK hd₀ hq n z hz]
  exact hot_source_le_gain _ _ _
    ((F.approximation n).dilatedCold_nonneg (S.radius_pos hs₀ n).le hs₀ hsmax hη hηmax
      hK hd₀ hq (shrinkingHorizon_pos F.horizonScale_pos n).le)
    (S.euclideanHot_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n) z

theorem normalizedHotSource_le_gains (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (n : ℕ) (z : KineticPhase) (hz : z.2 ∈ HotRepresentative.good q) :
    S.euclideanHotSource n z/H q z.2 ≤
      (2*mixedGainDensity (F.indices n+1) ((F.approximation n).dilatedCold (S.radius n))
        (S.euclideanHot n) z)/H q z.2+
      (S.radius n)^2*(KineticCollisionNullSets.gain (F.indices n+1) (S.euclideanHot n) z/H q z.2)+
      S.rescaledColdSource n (z.1.1,EuclideanFlight.phaseEquiv (z.1.2,z.2)) := by
  apply (div_le_div_of_nonneg_right
    (S.euclideanHotSource_le_gains hs₀ hsmax hη hηmax hK hd₀ hq n z hz) (H_nonneg q z.2)).trans_eq
  field_simp [(H_pos q z.2).ne']

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual mixed cutoff gain is controlled by the main positive action -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.mixed_gain_le_selected_action (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    (b : ℝ) {f : KineticPhase → ℝ} (hf : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hftwo : ∀ z, f z ≤ 2) :
    ∀ᵐ v : Velocity, ENNReal.ofReal (CollisionCompactness.mixedGainDensity b
      (F.dilatedCold r) (fun z => H q z.2*f z) (x,v)) ≤
      ENNReal.ofReal (H q v)*
        (ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N)
          (fun z => ENNReal.ofReal (f z)) (x,v)+
          2*(ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q)) := by
  have hc := F.dilatedCold_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ hT r
  have hcn := F.dilatedCold_nonneg hr.le hs₀ hsmax hη hηmax hK hd₀.le hq₂ hT
  have hg := F.rescaled_cold_gain_majorant_two hcarleman hr hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hdmax hsmall hq₁ hq₂ hT hTmax x ht hf.ennreal_ofReal
    (fun z => (ENNReal.ofReal_le_ofReal (hftwo z)).trans_eq (by norm_num))
  filter_upwards [hg,CollisionCompactness.normalized_mixed_cutoff_le_chart hcarleman b q
    hc hf hcn hfn x] with v hv hm
  exact hm.trans (mul_le_mul' le_rfl hv)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The normalized mixed source is bounded by the positive main kernel -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.normalized_mixed_gain_le_positive (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    (b : ℝ) {f : KineticPhase → ℝ} (hf : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hftwo : ∀ z, f z ≤ 2) :
    ∀ᵐ v : Velocity, ENNReal.ofReal ((2*CollisionCompactness.mixedGainDensity b
      (F.dilatedCold r) (fun z => H q z.2*f z) (x,v))/H q v) ≤
        ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N)
          (fun z => ENNReal.ofReal (f z)) (x,v)+
          4*(ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q) := by
  filter_upwards [F.mixed_gain_le_selected_action hcarleman hr hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hT hTmax x ht b hf hfn hftwo] with v hv
  rw [ENNReal.ofReal_div_of_pos (H_pos q v)]
  apply (ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr (H_pos q v)))
    ENNReal.ofReal_ne_top).mpr
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply (mul_le_mul' le_rfl hv).trans_eq
  rw [positiveMain_action]
  norm_num only [ENNReal.ofReal_ofNat]
  ring

theorem cold_gain_error_tendsto_zero {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (s₀ η K α d₀ q : ℝ) :
    Tendsto (fun n => 4*(ENNReal.ofReal (r n)*coldGainErrorConstant s₀ η K α d₀ q))
      atTop (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  have hm := ENNReal.Tendsto.mul_const h (Or.inr (coldGainErrorConstant_ne_top s₀ η K α d₀ q))
  have hh := ENNReal.Tendsto.const_mul hm (Or.inr (by norm_num : (4:ℝ≥0∞) ≠ ∞))
  simpa only [Function.comp_def,ENNReal.ofReal_zero,zero_mul,mul_zero] using hh

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
