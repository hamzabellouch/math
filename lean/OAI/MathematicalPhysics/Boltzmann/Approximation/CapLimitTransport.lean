import OAI.MathematicalPhysics.Boltzmann.Approximation.CapActualLossDensity
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotSourceIntegrability
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotTransportBalance
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMixedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapNonlinearHotLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.CentralRetainedLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicPhysicalGain
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicProductTest
import OAI.MathematicalPhysics.Boltzmann.Branching.HotChartHomeomorph
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion
import OAI.MathematicalPhysics.Boltzmann.Branching.IncomingLossRate
import OAI.MathematicalPhysics.Boltzmann.Branching.MixedPhysicalMeasures
import OAI.MathematicalPhysics.Boltzmann.Branching.ProjectedTimeBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.SeparatedMeasureTail
import OAI.MathematicalPhysics.Boltzmann.Branching.VanishingCutoffCollision
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdCentralVanishing

namespace OAI

section

/-! # The physical hot collision decomposition on each compact time cylinder -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_hot_collision_identity (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 ≤ a) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ᵐ z ∂(coldCylinderVolume a A R).prod volume,
      S.hotSourceDensity a A (κ n) z =
        2*mixedGainDensity (F.indices (κ n)+1) (S.rescaledColdDensity (κ n)) (S.hotDensity (κ n)) z-
          S.hotDensity (κ n) z*KineticCollisionNullSets.frequency (F.indices (κ n)+1)
            (S.rescaledColdDensity (κ n)) z+
          (S.radius (κ n))^2*collisionSource (F.indices (κ n)+1) (S.hotDensity (κ n)) z+
          H q z.2*S.rescaledColdSource (κ n) (z.1.1,(z.1.2,z.2)) := by
  filter_upwards [S.eventually_extendedHot_eq hs₀ hU hA] with n hn
  have ht : ∀ᵐ z ∂(coldCylinderVolume a A R).prod (volume : Measure Velocity),
      z.1.1 ∈ Icc a A :=
    Measure.quasiMeasurePreserving_fst.ae
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc))
  have hg : ∀ᵐ z ∂(coldCylinderVolume a A R).prod (volume : Measure Velocity),
      z.2 ∈ HotRepresentative.good q :=
    Measure.quasiMeasurePreserving_snd.ae (HotRepresentative.ae_good hcarleman hq₁ hq₂)
  filter_upwards [ht,hg] with z hz hzg
  have he (v : Velocity) : S.hotDensity (κ n) (z.1,v) = S.physicalHotDensity (κ n) (z.1,v) :=
    hn z.1.1 ⟨ha.trans hz.1,hz.2⟩ (z.1.2,v)
  have hi := S.rescaled_hot_collision hs₀ hsmax hη hηmax hK hd₀ hq₂ (κ n) z hzg
  rw [mixedGain_fiber_congr _ (fun _ => rfl) (fun v => (he v).symm) z.2,
    collisionSource_fiber_congr _ (fun v => (he v).symm) z.2,← he z.2] at hi
  rw [hotSourceDensity,indicator_of_mem
    (show z ∈ {z : HotKineticPhase | z.1.1 ∈ Icc a A} from hz)]
  exact hi

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # General compact kinetic tests for the actual loss measure limit -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.loss_measure_compact_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    (ψ : C(HotKineticPhase,ℝ)) (hc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ z, ψ z ∂S.physicalLossMeasure a A R (E.indices n)) atTop
      (𝓝 (∫ z, ψ z ∂incomingLossMeasure
        (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) := by
  let ν := incomingLossMeasure
    (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))
  let _ : IsFiniteMeasure ν :=
    E.toHotLimitExtraction.incomingLossMeasure_finite ha (ha.le.trans haA) hK hα hγ hq₂
  have hfin := (S.eventually_physicalCollisionMeasures_finite hs₀ hsmax hη hηmax hK hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ E.indices_strict E.horizon_limit
    (R := R) ha haA hA).mono (fun _ hn => hn.2)
  have hsep (u : (ℝ × JetPrototype.Space) →ᵇ ℝ) (v : Velocity →ᵇ ℝ) :
      Tendsto (fun n => ∫ z, u z.1*v z.2 ∂S.physicalLossMeasure a A R (E.indices n)) atTop
        (𝓝 (∫ z, u z.1*v z.2 ∂ν)) :=
    E.loss_measure_separated_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR u.continuous.measurable
      (fun x => u.norm_coe_le_norm x) v.continuous (fun x => v.norm_coe_le_norm x)
  obtain ⟨RX,hRX⟩ := (hc.isCompact.image continuous_fst).isBounded.subset_closedBall
    (0 : ℝ × JetPrototype.Space)
  obtain ⟨RV,hRV⟩ := (hc.isCompact.image continuous_snd).isBounded.subset_closedBall (0 : Velocity)
  apply SeparatedTests.compact_test_tendsto_of_eventually_finite _ ν hfin hsep ψ hc 0 0 RX RV
  intro z hz
  apply image_eq_zero_of_notMem_tsupport
  intro hzs
  exact hz ⟨hRX ⟨z,hzs,rfl⟩,hRV ⟨z,hzs,rfl⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Source identity with exactly the physical error controlled by compactness -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_hot_source_error_identity (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 ≤ a) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ᵐ z ∂(coldCylinderVolume a A R).prod volume,
      S.hotSourceDensity a A (κ n) z =
        2*mixedGainDensity (F.indices (κ n)+1) (S.rescaledColdDensity (κ n)) (S.hotDensity (κ n)) z-
          S.hotDensity (κ n) z*KineticCollisionNullSets.frequency (F.indices (κ n)+1)
            (S.rescaledColdDensity (κ n)) z+S.physicalCollisionError a A (κ n) z := by
  filter_upwards [S.eventually_hot_collision_identity hcarleman hs₀ hsmax hη hηmax hK hd₀
    hq₁ hq₂ hU (R := R) ha hA,S.eventually_extendedHot_eq hs₀ hU hA] with n hn hext
  have ht : ∀ᵐ z ∂(coldCylinderVolume a A R).prod (volume : Measure Velocity),
      z.1.1 ∈ Icc a A :=
    Measure.quasiMeasurePreserving_fst.ae
      (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc))
  filter_upwards [hn,ht] with z hz hzt
  have he (v : Velocity) : S.hotDensity (κ n) (z.1,v) = S.physicalHotDensity (κ n) (z.1,v) :=
    hext z.1.1 ⟨ha.trans hzt.1,hzt.2⟩ (z.1.2,v)
  rw [collisionSource_fiber_congr _ he z.2] at hz
  unfold physicalCollisionError coldSourceDensity
  rw [indicator_of_mem (show z ∈ {z : HotKineticPhase | z.1.1 ∈ Icc a A} from hzt)]
  simpa only [add_assoc] using hz

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Identification of the actual rescaled hot source against separated tests -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.hot_source_weak_limit
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ ∀ a A R : ℝ, ∀ ha : 0 < a, a ≤ A →
      ENNReal.ofReal A < E.horizon → 0 ≤ R →
      ∀ (θ : ℝ × JetPrototype.Space → ℝ), Measurable θ →
      ∀ B : ℝ, (∀ x, |θ x| ≤ B) →
      ∀ (φ : Velocity → ℝ), Continuous φ → ∀ C : ℝ, (∀ v, |φ v| ≤ C) →
      Tendsto (fun n => ∫ z, (θ z.1*φ z.2)*S.hotSourceDensity a A (E.indices (κ n)) z
        ∂(coldCylinderVolume a A R).prod volume) atTop
        (𝓝 (2*(∫ z, θ z.1*incomingGainTest φ z.2
          ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))-
          (∫ z, θ z.1*incomingLossTest φ z.2
          ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) := by
  obtain ⟨κ,hκ,herr⟩ := E.vanishing_physical_collision_error hDP hcarleman hGLPS hs₀ hsmax hη hηmax
    hK hα (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨κ,hκ,fun a A R ha haA hA hR θ hθ B hθB φ hφ C hφC => ?_⟩
  let ψ : HotKineticPhase → ℝ := fun z => θ z.1*φ z.2
  have hψ : Measurable ψ := (hθ.comp measurable_fst).mul (hφ.measurable.comp measurable_snd)
  have hB : 0 ≤ B := (abs_nonneg (θ (0,0))).trans (hθB _)
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφC _)
  have hψB (z) : |ψ z| ≤ B*C := by
    exact (abs_mul _ _).trans_le (mul_le_mul (hθB _) (hφC _) (abs_nonneg _) hB)
  have he := Compactness.bounded_test_integral_tendsto_zero
    (fun n => (S.physicalCollisionError_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ a A
      (E.indices (κ n))).aestronglyMeasurable)
    (herr a A R ha haA hA) hψ (mul_nonneg hB hC) hψB
  have hg := (E.mixed_physical_gain_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB hφ hφC).comp hκ.tendsto_atTop
  have hl := (E.mixed_physical_loss_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB hφ hφC).comp hκ.tendsto_atTop
  have ht := ((hg.const_mul 2).sub hl).add he
  simp only [add_zero] at ht
  apply ht.congr'
  have hei : ∀ᶠ n in atTop, Integrable (S.physicalCollisionError a A (E.indices (κ n)))
      ((coldCylinderVolume a A R).prod volume) :=
    ((herr a A R ha haA hA).eventually
      (eventually_lt_nhds (show (0 : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top))).mono
      (fun _ hn => memLp_one_iff_integrable.mp hn)
  filter_upwards [S.eventually_hot_source_error_identity hcarleman hs₀ hsmax hη hηmax hK
    hd₀.le hq₁ hq₂ (E.horizon_limit.comp hκ.tendsto_atTop) (R := R) ha.le hA,
    S.eventually_mixedPreRate_integrable hs₀ hsmax hη hηmax hK hα
      (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ (E.indices_strict.comp hκ)
      (E.horizon_limit.comp hκ.tendsto_atTop) (R := R) ha haA hA,hei] with n hn hpre hei
  have hp := hpre (S.collisionCutoff (E.indices (κ n)))
  have hgi := mixed_gain_test_integrable hp hψ hψB
  have hli := mixed_loss_test_integrable hp hψ hψB
  have heψ := hei.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hψB)
  dsimp only [Function.comp_def,ψ] at hgi hli heψ ⊢
  have hsum := integral_add ((hgi.const_mul 2).sub hli) heψ
  simp only [Pi.sub_apply] at hsum
  rw [← integral_const_mul,← integral_sub (hgi.const_mul 2) hli,← hsum]
  apply integral_congr_ae
  filter_upwards [hn] with z hz
  rw [hz]
  change _ = (θ z.1*φ z.2)*(2*mixedGainDensity (S.collisionCutoff (E.indices (κ n)))
    (S.rescaledColdDensity (E.indices (κ n))) (S.hotDensity (E.indices (κ n))) z-
    S.hotDensity (E.indices (κ n)) z*KineticCollisionNullSets.frequency
      (S.collisionCutoff (E.indices (κ n))) (S.rescaledColdDensity (E.indices (κ n))) z+
    S.physicalCollisionError a A (E.indices (κ n)) z)
  ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Separated-test convergence of the actual physical gain measures -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.gain_measure_separated_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    {B : ℝ} {θ : ℝ × JetPrototype.Space → ℝ} (hθ : Measurable θ) (hθB : ∀ x, |θ x| ≤ B)
    {φ : Velocity → ℝ} (hφ : Continuous φ) {C : ℝ} (hφC : ∀ v, |φ v| ≤ C) :
    Tendsto (fun n => ∫ z, θ z.1*φ z.2 ∂S.physicalGainMeasure a A R (E.indices n)) atTop
      (𝓝 (∫ z, θ z.1*φ z.2 ∂incomingGainMeasure
        (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) := by
  let μ := E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)
  let _ : SFinite μ := by dsimp [μ,HotLimitExtraction.mixedMeasure]; infer_instance
  have hi : Integrable incomingRate μ :=
    E.toHotLimitExtraction.incomingRate_integrable ha (ha.le.trans haA) hK hα hγ hq₂
  have hB : 0 ≤ B := (abs_nonneg (θ (0,0))).trans (hθB _)
  have ht := E.mixed_physical_gain_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB hφ hφC
  rw [← incomingGainMeasure_separated hi hθ hB hθB hφ.measurable hφC] at ht
  apply ht.congr'
  filter_upwards [S.eventually_mixedPreRate_integrable hs₀ hsmax hη hηmax hK hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ E.indices_strict E.horizon_limit
    (R := R) ha haA hA] with n hn
  have hc := fun p => (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n) p).1
  have hh := S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n)
  exact (mixedGainMeasure_integral hc hh (hn _) (fun z => θ z.1*φ z.2)).symm

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # General compact kinetic tests for the actual gain measure limit -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.gain_measure_compact_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    (ψ : C(HotKineticPhase,ℝ)) (hc : HasCompactSupport ψ) :
    Tendsto (fun n => ∫ z, ψ z ∂S.physicalGainMeasure a A R (E.indices n)) atTop
      (𝓝 (∫ z, ψ z ∂incomingGainMeasure
        (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) := by
  let ν := incomingGainMeasure
    (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))
  let _ : IsFiniteMeasure ν :=
    E.toHotLimitExtraction.incomingGainMeasure_finite ha (ha.le.trans haA) hK hα hγ hq₂
  have hfin := (S.eventually_physicalCollisionMeasures_finite hs₀ hsmax hη hηmax hK hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ E.indices_strict E.horizon_limit
    (R := R) ha haA hA).mono (fun _ hn => hn.1)
  have hsep (u : (ℝ × JetPrototype.Space) →ᵇ ℝ) (v : Velocity →ᵇ ℝ) :
      Tendsto (fun n => ∫ z, u z.1*v z.2 ∂S.physicalGainMeasure a A R (E.indices n)) atTop
        (𝓝 (∫ z, u z.1*v z.2 ∂ν)) :=
    E.gain_measure_separated_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR u.continuous.measurable
      (fun x => u.norm_coe_le_norm x) v.continuous (fun x => v.norm_coe_le_norm x)
  obtain ⟨RX,hRX⟩ := (hc.isCompact.image continuous_fst).isBounded.subset_closedBall
    (0 : ℝ × JetPrototype.Space)
  obtain ⟨RV,hRV⟩ := (hc.isCompact.image continuous_snd).isBounded.subset_closedBall (0 : Velocity)
  apply SeparatedTests.compact_test_tendsto_of_eventually_finite _ ν hfin hsep ψ hc 0 0 RX RV
  intro z hz
  apply image_eq_zero_of_notMem_tsupport
  intro hzs
  exact hz ⟨hRX ⟨z,hzs,rfl⟩,hRV ⟨z,hzs,rfl⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The linear hot transport equation for the actual extracted cap limit

Mixed cold-hot convergence identifies the collision source. Compactness and
Carleman hypotheses give the linear transport equation for the extracted limit.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.TransportCutoff BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.separated_transport_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B R Rₑ : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hR : 0 ≤ R)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A Rₑ)
    (hsC : ∀ z ∈ tsupport χ, EuclideanFlight.hotChart z ∈ coldCylinderSet a A R)
    {θ : ℝ × JetPrototype.Space → ℝ} (hθ : Measurable θ)
    {Cθ : ℝ} (hθB : ∀ x, |θ x| ≤ Cθ)
    {φ : Velocity → ℝ} (hφ : Continuous φ) {Cφ : ℝ} (hφB : ∀ v, |φ v| ≤ Cφ)
    (hsep : ∀ z, χ (EuclideanFlight.hotChart.symm z) = θ z.1*φ z.2) :
    (∫ z, transportDerivative χ (EuclideanFlight.hotChart.symm z)*E.hotLimit z
      ∂(coldCylinderVolume a A R).prod volume) +
      (2*(∫ z, θ z.1*incomingGainTest φ z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))-
        (∫ z, θ z.1*incomingLossTest φ z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) = 0 := by
  have hA : ENNReal.ofReal A < E.horizon :=
    (ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB
  obtain ⟨κ,hκ,hsource⟩ := E.hot_source_weak_limit hDP hcarleman hGLPS hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
  let μ := (coldCylinderVolume a A R).prod (volume : Measure Velocity)
  let D : HotKineticPhase → ℝ := fun z => transportDerivative χ (EuclideanFlight.hotChart.symm z)
  have hDm : Measurable D :=
    (transportDerivative_continuous hχ).measurable.comp EuclideanFlight.hotChart.symm.measurable
  obtain ⟨CD,hDb⟩ := (transportDerivative_continuous hχ).bounded_above_of_compact_support
    (transportDerivative_hasCompactSupport hc)
  have hDB (z) : |D z| ≤ CD := hDb _
  have hlimF := ((E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le hA R).2.2
    D hDm ⟨CD,hDB⟩).comp hκ.tendsto_atTop
  have hlimQ := hsource a A R ha haA hA hR θ hθ Cθ hθB φ hφ Cφ hφB
  have hlim := hlimF.add hlimQ
  have hψ : Measurable (fun z : HotKineticPhase => θ z.1*φ z.2) :=
    (hθ.comp measurable_fst).mul (hφ.measurable.comp measurable_snd)
  have hCθ : 0 ≤ Cθ := (abs_nonneg (θ (0,0))).trans (hθB _)
  have hψB (z : HotKineticPhase) : |θ z.1*φ z.2| ≤ Cθ*Cφ := by
    rw [abs_mul]
    exact mul_le_mul (hθB _) (hφB _) (abs_nonneg _) hCθ
  have he : (fun n => (∫ z, D z*S.physicalHotDensity (E.indices (κ n)) z ∂μ)+
      (∫ z, (θ z.1*φ z.2)*S.hotSourceDensity a A (E.indices (κ n)) z ∂μ)) =ᶠ[atTop]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hκ.tendsto_atTop.eventually
      (S.eventually_physicalHot_cylinder_integrable E.toHotLimitExtraction hs₀
        hsmax hη hηmax hK hd₀.le hq₂ ha.le hA R),
      S.eventually_hotSource_cylinder_integrable hcarleman hs₀ hsmax hη hηmax hK hα
        (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₁ hq₂
        (E.indices_strict.comp hκ) (E.horizon_limit.comp hκ.tendsto_atTop) ha haA hA R,
      S.eventually_hot_transport_balance hcarleman hs₀ hsmax hη hηmax hK hα
        (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₁ hq₂
        (E.indices_strict.comp hκ) (E.horizon_limit.comp hκ.tendsto_atTop)
        ha haA hAB hB hχ hc hs] with n hfi hqi hbal
    have hiF := hfi.bdd_mul hDm.aestronglyMeasurable (ae_of_all _ hDB)
    have hiQ := hqi.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hψB)
    dsimp only [μ,Function.comp_def] at hiQ ⊢
    rw [← integral_add hiF hiQ]
    have hb := S.hot_transport_cylinder_of_balance (E.indices (κ n)) hsC hbal
    simpa only [D,μ,hsep] using hb
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot source limit for every compact continuous kinetic test -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.hot_source_compact_limit
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ ∀ a A R : ℝ, ∀ ha : 0 < a, a ≤ A →
      ENNReal.ofReal A < E.horizon → 0 ≤ R →
      ∀ ψ : C(HotKineticPhase,ℝ), HasCompactSupport ψ →
      Tendsto (fun n => ∫ z, ψ z*S.hotSourceDensity a A (E.indices (κ n)) z
        ∂(coldCylinderVolume a A R).prod volume) atTop
        (𝓝 (2*(∫ z, ψ z ∂incomingGainMeasure
          (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))-
          (∫ z, ψ z ∂incomingLossMeasure
            (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))))) := by
  obtain ⟨κ,hκ,herr⟩ := E.vanishing_physical_collision_error hDP hcarleman hGLPS hs₀ hsmax hη hηmax
    hK hα (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨κ,hκ,fun a A R ha haA hA hR ψ hc => ?_⟩
  obtain ⟨B,hB⟩ := ψ.continuous.bounded_above_of_compact_support hc
  have hB0 : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hB _)
  have he := Compactness.bounded_test_integral_tendsto_zero
    (fun n => (S.physicalCollisionError_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ a A
      (E.indices (κ n))).aestronglyMeasurable)
    (herr a A R ha haA hA) ψ.continuous.measurable hB0 hB
  have hg := (E.gain_measure_compact_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR ψ hc).comp hκ.tendsto_atTop
  have hl := (E.loss_measure_compact_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR ψ hc).comp hκ.tendsto_atTop
  have ht := ((hg.const_mul 2).sub hl).add he
  simp only [add_zero] at ht
  apply ht.congr'
  have hei : ∀ᶠ n in atTop, Integrable (S.physicalCollisionError a A (E.indices (κ n)))
      ((coldCylinderVolume a A R).prod volume) :=
    ((herr a A R ha haA hA).eventually
      (eventually_lt_nhds (show (0 : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top))).mono
      (fun _ hn => memLp_one_iff_integrable.mp hn)
  filter_upwards [S.eventually_hot_source_error_identity hcarleman hs₀ hsmax hη hηmax hK
    hd₀.le hq₁ hq₂ (E.horizon_limit.comp hκ.tendsto_atTop) (R := R) ha.le hA,
    S.eventually_mixedPreRate_integrable hs₀ hsmax hη hηmax hK hα
      (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ (E.indices_strict.comp hκ)
      (E.horizon_limit.comp hκ.tendsto_atTop) (R := R) ha haA hA,hei] with n hn hpre hei
  dsimp only [Function.comp_def] at hpre
  have hp := hpre (S.collisionCutoff (E.indices (κ n)))
  have hcold := fun p => (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀.le hq₂
    (E.indices (κ n)) p).1
  have hhot := S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices (κ n))
  have hgi := mixed_gain_test_integrable hp ψ.continuous.measurable hB
  have hli := (mixedLossDensity_integrable hp).bdd_mul ψ.continuous.aestronglyMeasurable
    (ae_of_all _ hB)
  have heψ := hei.bdd_mul ψ.continuous.aestronglyMeasurable (ae_of_all _ hB)
  dsimp only [Function.comp_def,physicalGainMeasure,physicalLossMeasure]
  rw [mixedGainMeasure_integral hcold hhot hp ψ,mixedLossMeasure_integral hcold hhot hp ψ,
    ← integral_const_mul,← integral_sub (hgi.const_mul 2) hli]
  have hsub := (hgi.const_mul 2).sub hli
  change Integrable (fun z => (2 : ℝ)*(ψ z*_) - ψ z*_) _ at hsub
  rw [← integral_add hsub heψ]
  apply integral_congr_ae
  filter_upwards [hn,mixed_loss_ae_eq_frequency hp] with z hz hlz
  rw [hz,hlz]
  change _ = ψ z*(2*mixedGainDensity (S.collisionCutoff (E.indices (κ n)))
    (S.rescaledColdDensity (E.indices (κ n))) (S.hotDensity (E.indices (κ n))) z-
    S.hotDensity (E.indices (κ n)) z*KineticCollisionNullSets.frequency
      (S.collisionCutoff (E.indices (κ n))) (S.rescaledColdDensity (E.indices (κ n))) z+
    S.physicalCollisionError a A (E.indices (κ n)) z)
  ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual limiting hot equation for every smooth compact kinetic test

Mixed cold-hot convergence identifies the collision source. Compactness and
Carleman hypotheses give the transport equation for the extracted limit.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.TransportCutoff BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.transport_measure_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B R Rₑ : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hR : 0 ≤ R)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A Rₑ)
    (hsC : ∀ z ∈ tsupport χ, EuclideanFlight.hotChart z ∈ coldCylinderSet a A R)
    :
    (∫ z, transportDerivative χ (EuclideanFlight.hotChart.symm z)*E.hotLimit z
      ∂(coldCylinderVolume a A R).prod volume) +
      (2*(∫ z, χ (EuclideanFlight.hotChart.symm z) ∂incomingGainMeasure
        (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))-
        (∫ z, χ (EuclideanFlight.hotChart.symm z) ∂incomingLossMeasure
          (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) = 0 := by
  have hA : ENNReal.ofReal A < E.horizon :=
    (ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB
  obtain ⟨κ,hκ,hsource⟩ := E.hot_source_compact_limit hDP hcarleman hGLPS hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
  let μ := (coldCylinderVolume a A R).prod (volume : Measure Velocity)
  let D : HotKineticPhase → ℝ := fun z => transportDerivative χ (EuclideanFlight.hotChart.symm z)
  have hDm : Measurable D :=
    (transportDerivative_continuous hχ).measurable.comp EuclideanFlight.hotChart.symm.measurable
  obtain ⟨CD,hDb⟩ := (transportDerivative_continuous hχ).bounded_above_of_compact_support
    (transportDerivative_hasCompactSupport hc)
  have hDB (z) : |D z| ≤ CD := hDb _
  have hlimF := ((E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le hA R).2.2
    D hDm ⟨CD,hDB⟩).comp hκ.tendsto_atTop
  let ψ : C(HotKineticPhase,ℝ) := ⟨fun z => χ (EuclideanFlight.hotChart.symm z),
    hχ.continuous.comp EuclideanFlight.hotChart_symm_continuous⟩
  have hlimQ := hsource a A R ha haA hA hR ψ (EuclideanFlight.compact_test_hotChart hc)
  have hlim := hlimF.add hlimQ
  obtain ⟨Cψ,hψB⟩ := ψ.continuous.bounded_above_of_compact_support
    (EuclideanFlight.compact_test_hotChart hc)
  have he : (fun n => (∫ z, D z*S.physicalHotDensity (E.indices (κ n)) z ∂μ)+
      (∫ z, ψ z*S.hotSourceDensity a A (E.indices (κ n)) z ∂μ)) =ᶠ[atTop]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hκ.tendsto_atTop.eventually
      (S.eventually_physicalHot_cylinder_integrable E.toHotLimitExtraction hs₀
        hsmax hη hηmax hK hd₀.le hq₂ ha.le hA R),
      S.eventually_hotSource_cylinder_integrable hcarleman hs₀ hsmax hη hηmax hK hα
        (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₁ hq₂
        (E.indices_strict.comp hκ) (E.horizon_limit.comp hκ.tendsto_atTop) ha haA hA R,
      S.eventually_hot_transport_balance hcarleman hs₀ hsmax hη hηmax hK hα
        (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₁ hq₂
        (E.indices_strict.comp hκ) (E.horizon_limit.comp hκ.tendsto_atTop)
        ha haA hAB hB hχ hc hs] with n hfi hqi hbal
    have hiF := hfi.bdd_mul hDm.aestronglyMeasurable (ae_of_all _ hDB)
    have hiQ := hqi.bdd_mul ψ.continuous.aestronglyMeasurable (ae_of_all _ hψB)
    dsimp only [μ,Function.comp_def] at hiQ ⊢
    rw [← integral_add hiF hiQ]
    have hb := S.hot_transport_cylinder_of_balance (E.indices (κ n)) hsC hbal
    simpa only [D,μ,ψ,ContinuousMap.coe_mk] using hb
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Exact periodicity of the cap hot remainder and its bounded ratio -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.WeightedTranslation BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.hot_periodic {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (k : JetLattice.Lattice) :
    pull (displacement k) F.hot = F.hot := by
  funext u
  change F.solution.value (u.1,shift (displacement k) u.2)-
    (∑' i, rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N
      F.solution.value i (u.1,shift (displacement k) u.2)) = _
  have hs := congrFun (F.solution.periodic k) u
  have hc (i : JetLattice.Label) := congrFun (rebuilt_shift
    (s₀ := s₀) (η := η) (K := K) (α := α) (γ := γ) (d₀ := d₀) (q := q)
    (b := N+1) (L := damping q (N+1) F.amplitude) (T := T) (N := N)
    k (F.solution.periodic k) i) u
  change F.solution.value (u.1,shift (displacement k) u.2) = F.solution.value u at hs
  simp only [pull] at hc
  rw [hs]
  simp_rw [hc]
  exact congrArg (fun c => F.solution.value u-c)
    ((relabel k).tsum_eq (fun i => rebuilt s₀ η K α γ d₀ q (N+1)
      (damping q (N+1) F.amplitude) T N F.solution.value i u))

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem euclideanHot_div_weight (S : AttainedCapSequence F) (n : ℕ) (z : Published.KineticPhase) :
    S.euclideanHot n z/H q z.2 = (F.approximation n).hot
      (S.radius n*z.1.1,(S.radius n • JetPeriodicDatum.spatialMap z.1.2,z.2))/S.radius n := by
  rw [euclideanHot_eq_rescaledHot,rescaledHot_eq_weighted]
  simp only [EuclideanFlight.phaseEquiv_apply,JetPeriodicDatum.phaseMap]
  rw [mul_div_cancel_left₀ _ (H_pos q z.2).ne']
  rfl

theorem boundedHotRatio_periodic (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    (n : ℕ) (t : ℝ) (k : JetLattice.Lattice) (p : Velocity × Velocity) :
    S.boundedHotRatio n ((t,p.1-(S.radius n)⁻¹ • latticeVector k),p.2) =
      S.boundedHotRatio n ((t,p.1),p.2) := by
  unfold boundedHotRatio
  rw [euclideanHot_div_weight,euclideanHot_div_weight]
  have he : S.radius n • JetPeriodicDatum.spatialMap (p.1-(S.radius n)⁻¹ • latticeVector k) =
      S.radius n • JetPeriodicDatum.spatialMap p.1-displacement k := by
    apply Prod.ext
    · ext i
      change S.radius n*(p.1 i.castSucc-(S.radius n)⁻¹*(k i.castSucc:ℝ)) =
        S.radius n*p.1 i.castSucc-(k i.castSucc:ℝ)
      field_simp [(S.radius_pos hs₀ n).ne']
    · change S.radius n*(p.1 (Fin.last 2)-(S.radius n)⁻¹*(k (Fin.last 2):ℝ)) =
        S.radius n*p.1 (Fin.last 2)-(k (Fin.last 2):ℝ)
      field_simp [(S.radius_pos hs₀ n).ne']
  rw [he]
  have hp := congrFun ((F.approximation n).hot_periodic k)
    (S.radius n*t,(S.radius n • JetPeriodicDatum.spatialMap p.1,p.2))
  change (F.approximation n).hot
    (S.radius n*t,(S.radius n • JetPeriodicDatum.spatialMap p.1-displacement k,p.2)) = _ at hp
  rw [hp]

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual limiting transport equation with its loss attenuation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.TransportCutoff BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.attenuated_transport_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B R Rₑ : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hR : 0 ≤ R)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A Rₑ)
    (hsC : ∀ z ∈ tsupport χ, EuclideanFlight.hotChart z ∈ coldCylinderSet a A R)
    :
    (∫ z, (transportDerivative χ (EuclideanFlight.hotChart.symm z)-
      χ (EuclideanFlight.hotChart.symm z)*GeometricBackground.frequency
        E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)*E.hotLimit z
      ∂(coldCylinderVolume a A R).prod volume)+
      2*(∫ z, χ (EuclideanFlight.hotChart.symm z) ∂incomingGainMeasure
        (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) = 0 := by
  have hA : ENNReal.ofReal A < E.horizon :=
    (ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB
  have hb := E.transport_measure_balance hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hR hχ hc hs hsC
  let ψ : HotKineticPhase → ℝ := fun z => χ (EuclideanFlight.hotChart.symm z)
  have hψ : Measurable ψ := hχ.continuous.measurable.comp EuclideanFlight.hotChart.symm.measurable
  obtain ⟨Cψ,hψB⟩ := hχ.continuous.bounded_above_of_compact_support hc
  have hψBound (z) : |ψ z| ≤ Cψ := hψB _
  rw [E.toHotLimitExtraction.actual_loss_cylinder_integral ha haA hK hα hγ hq₂ hψ hψBound] at hb
  obtain ⟨CD,hDB⟩ := (transportDerivative_continuous hχ).bounded_above_of_compact_support
    (transportDerivative_hasCompactSupport hc)
  have hd := ((E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le hA R).2.1).bdd_mul
    ((transportDerivative_continuous hχ).measurable.comp
      EuclideanFlight.hotChart.symm.measurable).aestronglyMeasurable
    (ae_of_all _ (fun z => hDB (EuclideanFlight.hotChart.symm z)))
  dsimp only [Function.comp_def] at hd
  have hl := (E.toHotLimitExtraction.actual_loss_cylinder_integrable
    (R := R) ha haA hK hα hγ hq₂).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hψBound)
  have he : (∫ z, (transportDerivative χ (EuclideanFlight.hotChart.symm z)-
      ψ z*GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume) =
      (∫ z, transportDerivative χ (EuclideanFlight.hotChart.symm z)*E.hotLimit z
        ∂(coldCylinderVolume a A R).prod volume)-
      (∫ z, ψ z*(E.hotLimit z*GeometricBackground.frequency E.phase η E.fraction K α γ
        z.1.1 z.1.2 z.2) ∂(coldCylinderVolume a A R).prod volume) := by
    rw [← integral_sub hd hl]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by ring)
  change (∫ z, (transportDerivative χ (EuclideanFlight.hotChart.symm z)-
      ψ z*GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+_ = 0
  rw [he]
  linarith

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot transport equation with finite incoming gain and loss measures -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal
open BoltzmannNonuniqueness.TransportCutoff BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.separated_transport_measure_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B R Rₑ : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hR : 0 ≤ R)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A Rₑ)
    (hsC : ∀ z ∈ tsupport χ, EuclideanFlight.hotChart z ∈ coldCylinderSet a A R)
    {θ : ℝ × JetPrototype.Space → ℝ} (hθ : Measurable θ)
    {Cθ : ℝ} (hθB : ∀ x, |θ x| ≤ Cθ)
    {φ : Velocity → ℝ} (hφ : Continuous φ) {Cφ : ℝ} (hφB : ∀ v, |φ v| ≤ Cφ)
    (hsep : ∀ z, χ (EuclideanFlight.hotChart.symm z) = θ z.1*φ z.2) :
    (∫ z, transportDerivative χ (EuclideanFlight.hotChart.symm z)*E.hotLimit z
      ∂(coldCylinderVolume a A R).prod volume)+
      2*(∫ z, χ (EuclideanFlight.hotChart.symm z)
        ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ
          (coldCylinderVolume a A R)))-
      (∫ z, χ (EuclideanFlight.hotChart.symm z)
        ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ
          (coldCylinderVolume a A R))) = 0 := by
  let μ := E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)
  let _ : SFinite μ := by dsimp [μ,HotLimitExtraction.mixedMeasure]; infer_instance
  have hi : Integrable incomingRate μ :=
    E.toHotLimitExtraction.incomingRate_integrable ha (ha.le.trans haA) hK hα hγ hq₂
  have hCθ : 0 ≤ Cθ := (abs_nonneg (θ (0,0))).trans (hθB _)
  have hg := incomingGainMeasure_separated hi hθ hCθ hθB hφ.measurable hφB
  have hl := incomingLossMeasure_separated hi hθ hCθ hθB hφ.measurable hφB
  simp_rw [hsep]
  change _+2*(∫ z, θ z.1*φ z.2 ∂incomingGainMeasure μ)-
    (∫ z, θ z.1*φ z.2 ∂incomingLossMeasure μ) = 0
  rw [hg,hl]
  have hb := E.separated_transport_balance hDP hcarleman hGLPS hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hR hχ hc hs hsC
    hθ hθB hφ hφB hsep
  dsimp only [μ] at hg hl ⊢
  linarith

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot-limit equation tested in characteristic coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.TransportCutoff BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_test_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B R Rₑ : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hR : 0 ≤ R)
    {ψ : EuclideanFlight.CharacteristicPhase → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport (EuclideanFlight.testPullback ψ) ⊆ kineticWindow a A Rₑ)
    (hsC : ∀ z ∈ tsupport (EuclideanFlight.testPullback ψ),
      EuclideanFlight.hotChart z ∈ coldCylinderSet a A R) :
    (∫ z, EuclideanFlight.timeDerivative ψ
      (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))*E.hotLimit z
      ∂(coldCylinderVolume a A R).prod volume)+
      (2*(∫ z, ψ (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))
        ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ
          (coldCylinderVolume a A R)))-
      (∫ z, ψ (EuclideanFlight.characteristicEquiv.symm (EuclideanFlight.hotChart.symm z))
        ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ
          (coldCylinderVolume a A R)))) = 0 := by
  have hb := E.transport_measure_balance hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hR
    (EuclideanFlight.testPullback_contDiff hψ) (EuclideanFlight.testPullback_compact hc) hs hsC
  simp_rw [EuclideanFlight.transportDerivative_testPullback hψ] at hb
  exact hb

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Cumulative collision balance for the actual weak hot limit

Every smooth nonnegative compact phase test has an almost-everywhere time trace
given by a constant and the cumulative incoming gain minus incoming loss.
Both source measures are built from the actual mixed atomic-cold/hot measure.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicGainMeasure (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (A R : ℝ) :
    Measure CharacteristicPhase :=
  (2 : ℝ≥0) • sourcePullback
    (incomingGainMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))

def HotLimitExtraction.characteristicLossMeasure (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (A R : ℝ) :
    Measure CharacteristicPhase :=
  sourcePullback
    (incomingLossMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))

theorem HotPairExtraction.characteristic_cumulative_balance
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
    ∃ R : ℝ, 0 ≤ R ∧ ∃ c : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a A →
      WeakTime.phaseProjection (cylinderPullback a A R E.hotLimit) φ t =
        c+WeakTime.cumulative (WeakTime.timeSource
          (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) φ) t-
        WeakTime.cumulative (WeakTime.timeSource
          (E.toHotLimitExtraction.characteristicLossMeasure ha hK hα hγ A R) φ) t := by
  obtain ⟨R,Rₑ,hR,hloc⟩ := exists_timePhase_cylinder a A hc
  refine ⟨R,hR,?_⟩
  let μ := E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R
  let ν := E.toHotLimitExtraction.characteristicLossMeasure ha hK hα hγ A R
  let _ := E.toHotLimitExtraction.incomingGainMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  let _ := E.toHotLimitExtraction.incomingLossMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  have : IsFiniteMeasure μ := by dsimp [μ,HotLimitExtraction.characteristicGainMeasure]; infer_instance
  have : IsFiniteMeasure ν := by dsimp [ν,HotLimitExtraction.characteristicLossMeasure]; infer_instance
  obtain ⟨C,hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have hi := (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le
    ((ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB) R).2.1
  apply WeakTime.projected_cumulative_balance haA (cylinderPullback_integrable hi)
    hφ.continuous.measurable hn hC μ ν
  intro θ hθ hθc hθs
  have hlocθ := hloc θ hθs
  have hb := E.characteristic_test_balance hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA.le hAB hB hR
    (timePhaseTest_contDiff hθ hφ) (timePhaseTest_compact hθc hc) hlocθ.1 hlocθ.2
  simp_rw [timeDerivative_timePhaseTest hθ hφ] at hb
  rw [cylinderPullback_integral]
  have hm : Measurable (fun z : CharacteristicPhase => θ z.1*φ z.2) :=
    (hθ.continuous.measurable.comp measurable_fst).mul
      (hφ.continuous.measurable.comp measurable_snd)
  change _ + (∫ z, θ z.1*φ z.2 ∂((2 : ℝ≥0) • sourcePullback _))-
    (∫ z, θ z.1*φ z.2 ∂sourcePullback _) = 0
  rw [integral_smul_nnreal_measure,sourcePullback_integral _ hm,sourcePullback_integral _ hm]
  change _ + 2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
    ∂incomingGainMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) - _ = 0
  change (∫ z, (deriv θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+
    (2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingGainMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))-
    (∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingLossMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) = 0 at hb
  linarith only [hb]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual weak-balance cylinder also covers the full compact phase support -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_characteristic_weak_balance
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
    {β : Velocity × Velocity → ℝ} (hβc : HasCompactSupport β) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ φ : WeakTime.Phase → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ p, 0 ≤ φ p) →
      tsupport φ ⊆ tsupport β → ∀ θ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a A →
      (∫ z, (deriv θ z.1*φ z.2)*cylinderPullback a A R E.hotLimit z)+
      (∫ z, θ z.1*φ z.2 ∂E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R)-
      (∫ z, θ z.1*φ z.2 ∂E.toHotLimitExtraction.characteristicLossMeasure ha hK hα hγ A R) = 0 := by
  obtain ⟨R₀,Rₑ,hR₀,hloc⟩ := exists_timePhase_cylinder_for_support a A hβc
  obtain ⟨R₁,_hR₁,hcover⟩ := exists_phase_cylinder a A hβc
  let R := max R₀ R₁
  have hR : 0 ≤ R := hR₀.trans (le_max_left _ _)
  refine ⟨R,hR,?_,?_⟩
  · intro t ht p hp
    exact coldCylinderSet_mono_radius (le_max_right _ _) (hcover t ht p hp)
  intro φ hφ hc _hn hφβ θ hθ hθc hθs
  have hlocθ := hloc φ hφβ θ hθs
  have hcoverθ : ∀ z ∈ tsupport (testPullback (timePhaseTest θ φ)),
      hotChart z ∈ coldCylinderSet a A R := fun z hz =>
    coldCylinderSet_mono_radius (le_max_left _ _) (hlocθ.2 z hz)
  have hb := E.characteristic_test_balance hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA.le hAB hB hR
    (timePhaseTest_contDiff hθ hφ) (timePhaseTest_compact hθc hc) hlocθ.1 hcoverθ
  simp_rw [timeDerivative_timePhaseTest hθ hφ] at hb
  rw [cylinderPullback_integral]
  have hm : Measurable (fun z : CharacteristicPhase => θ z.1*φ z.2) :=
    (hθ.continuous.measurable.comp measurable_fst).mul
      (hφ.continuous.measurable.comp measurable_snd)
  change _ + (∫ z, θ z.1*φ z.2 ∂((2 : ℝ≥0) • sourcePullback _))-
    (∫ z, θ z.1*φ z.2 ∂sourcePullback _) = 0
  rw [integral_smul_nnreal_measure,sourcePullback_integral _ hm,sourcePullback_integral _ hm]
  change (∫ z, (deriv θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+
    (2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))))-
    (∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) = 0
  change (∫ z, (deriv θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+
    ((2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))))-
    (∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) = 0 at hb
  linarith only [hb]


end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual characteristic gain is the sum of both outgoing collision laws

This identity uses the physical normal-collision law for the mixed measure,
including its atomic cold partner. No density Carleman identity is used here.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicGain_test_integral (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {ψ : CharacteristicPhase → ℝ} (hψ : Measurable ψ)
    {B : ℝ} (hB : ∀ u, |ψ u| ≤ B) :
    (∫ u, ψ u ∂E.characteristicGainMeasure ha hK hα hγ A R) =
      ∫ z, ψ (hotCharacteristicEquiv.symm (incomingLeft z))+
        ψ (hotCharacteristicEquiv.symm (incomingRight z))
        ∂incomingCollisionMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)) := by
  let μ := E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)
  let _ : SFinite μ := by dsimp [μ,HotLimitExtraction.mixedMeasure]; infer_instance
  have hi : Integrable incomingRate μ := E.incomingRate_integrable ha (ha.le.trans haA) hK hα hγ hq
  let _ := incomingCollisionMeasure_finite hi
  have hm : Measurable (fun z : HotKineticPhase => ψ (hotCharacteristicEquiv.symm z)) :=
    hψ.comp hotCharacteristicEquiv.symm.measurable
  have hL : Integrable (fun z => ψ (hotCharacteristicEquiv.symm (incomingLeft z)))
      (incomingCollisionMeasure μ) :=
    (integrable_const B).mono' (hm.comp incomingLeft_measurable).aestronglyMeasurable
      (ae_of_all _ (fun z => hB _))
  have hR : Integrable (fun z => ψ (hotCharacteristicEquiv.symm (incomingRight z)))
      (incomingCollisionMeasure μ) :=
    (integrable_const B).mono' (hm.comp incomingRight_measurable).aestronglyMeasurable
      (ae_of_all _ (fun z => hB _))
  rw [HotLimitExtraction.characteristicGainMeasure,integral_smul_nnreal_measure,
    sourcePullback_integral _ hψ,incomingGainMeasure_integral hi hm (fun z => hB _)]
  change 2*((1/2 : ℝ)*_)=_
  rw [integral_add hL hR]
  ring

theorem HotLimitExtraction.characteristicGain_normal_integral (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {ψ : CharacteristicPhase → ℝ} (hψ : Measurable ψ)
    {B : ℝ} (hB : ∀ u, |ψ u| ≤ B) :
    (∫ u, ψ u ∂E.characteristicGainMeasure ha hK hα hγ A R) =
      ∫ p, ∫ ω, collisionKernel p.2.1 p.2.2 ω*
        (ψ (hotCharacteristicEquiv.symm (incomingLeft (p,ω)))+
          ψ (hotCharacteristicEquiv.symm (incomingRight (p,ω)))) ∂sphereArea
        ∂E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R) := by
  let μ := E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)
  let _ : SFinite μ := by dsimp [μ,HotLimitExtraction.mixedMeasure]; infer_instance
  rw [E.characteristicGain_test_integral ha haA hK hα hγ hq hψ hB]
  apply incomingCollisionMeasure_integral_prod
    (E.incomingRate_integrable ha (ha.le.trans haA) hK hα hγ hq)
  · exact ((hψ.comp hotCharacteristicEquiv.symm.measurable).comp incomingLeft_measurable).add
      ((hψ.comp hotCharacteristicEquiv.symm.measurable).comp incomingRight_measurable)
  · intro z
    exact (abs_add_le _ _).trans ((add_le_add (hB _) (hB _)).trans_eq (two_mul B).symm)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # One physical cylinder for the actual weak balance of all local phase tests -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.common_characteristic_weak_balance
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
    {β : Velocity × Velocity → ℝ} (hβc : HasCompactSupport β) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ φ : WeakTime.Phase → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ p, 0 ≤ φ p) →
      tsupport φ ⊆ tsupport β → ∀ θ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a A →
      (∫ z, (deriv θ z.1*φ z.2)*cylinderPullback a A R E.hotLimit z)+
      (∫ z, θ z.1*φ z.2 ∂E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R)-
      (∫ z, θ z.1*φ z.2 ∂E.toHotLimitExtraction.characteristicLossMeasure ha hK hα hγ A R) = 0 := by
  obtain ⟨R,Rₑ,hR,hloc⟩ := exists_timePhase_cylinder_for_support a A hβc
  refine ⟨R,hR,?_⟩
  intro φ hφ hc _hn hφβ θ hθ hθc hθs
  have hlocθ := hloc φ hφβ θ hθs
  have hb := E.characteristic_test_balance hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA.le hAB hB hR
    (timePhaseTest_contDiff hθ hφ) (timePhaseTest_compact hθc hc) hlocθ.1 hlocθ.2
  simp_rw [timeDerivative_timePhaseTest hθ hφ] at hb
  rw [cylinderPullback_integral]
  have hm : Measurable (fun z : CharacteristicPhase => θ z.1*φ z.2) :=
    (hθ.continuous.measurable.comp measurable_fst).mul
      (hφ.continuous.measurable.comp measurable_snd)
  change _ + (∫ z, θ z.1*φ z.2 ∂((2 : ℝ≥0) • sourcePullback _))-
    (∫ z, θ z.1*φ z.2 ∂sourcePullback _) = 0
  rw [integral_smul_nnreal_measure,sourcePullback_integral _ hm,sourcePullback_integral _ hm]
  change (∫ z, (deriv θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+
    (2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))))-
    (∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) = 0
  change (∫ z, (deriv θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+
    ((2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))))-
    (∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) = 0 at hb
  linarith only [hb]


end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual characteristic gain as a hot-particle and cold-partner integral -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicGain_hot_integral (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {ψ : CharacteristicPhase → ℝ} (hψ : Measurable ψ)
    {B : ℝ} (hB : ∀ u, |ψ u| ≤ B) :
    (∫ u, ψ u ∂E.characteristicGainMeasure ha hK hα hγ A R) =
      ∫ x, ∫ w, E.cappedHot (x,w)*
        (∫ v, ∫ ω, collisionKernel v w ω*
          (ψ (hotCharacteristicEquiv.symm (x,scatterLeft v w ω))+
            ψ (hotCharacteristicEquiv.symm (x,scatterRight v w ω))) ∂sphereArea
          ∂E.background (max a x.1) x.2) ∂volume ∂coldCylinderVolume a A R := by
  let μ := E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)
  let _ : SFinite μ := by dsimp [μ,HotLimitExtraction.mixedMeasure]; infer_instance
  let f : ((ℝ × JetPrototype.Space) × (Velocity × Velocity)) × Sphere → ℝ := fun z =>
    ψ (hotCharacteristicEquiv.symm (incomingLeft z))+
      ψ (hotCharacteristicEquiv.symm (incomingRight z))
  have hm : Measurable f :=
    ((hψ.comp hotCharacteristicEquiv.symm.measurable).comp incomingLeft_measurable).add
      ((hψ.comp hotCharacteristicEquiv.symm.measurable).comp incomingRight_measurable)
  have hb (z) : |f z| ≤ 2*B :=
    (abs_add_le _ _).trans ((add_le_add (hB _) (hB _)).trans_eq (two_mul B).symm)
  have hi := incomingCollision_weight_integrable
    (E.incomingRate_integrable (R := R) ha (ha.le.trans haA) hK hα hγ hq) hm hb
  have hF : Integrable (fun p => ∫ ω, collisionKernel p.2.1 p.2.2 ω*f (p,ω) ∂sphereArea) μ :=
    hi.integral_prod_left
  rw [E.characteristicGain_normal_integral ha haA hK hα hγ hq hψ hB]
  change (∫ p, (∫ ω, collisionKernel p.2.1 p.2.2 ω*f (p,ω) ∂sphereArea)
    ∂(coldCylinderVolume a A R ⊗ₘ E.mixedKernel ha hK hα hγ)) = _
  rw [Measure.integral_compProd hF]
  apply integral_congr_ae
  filter_upwards [(Measure.integrable_compProd_iff hF.aestronglyMeasurable).mp hF |>.1] with x hx
  let _ : IsFiniteMeasure (E.background (max a x.1) x.2) :=
    GeometricBackground.background_finite E.phase η E.fraction K α γ (max a x.1) x.2
  rw [E.mixedKernel_apply] at hx ⊢
  rw [integral_prod_symm _ hx,E.hotKernel_integral]
  rfl

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
