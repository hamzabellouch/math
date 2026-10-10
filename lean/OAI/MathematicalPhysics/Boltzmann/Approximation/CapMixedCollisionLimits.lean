import OAI.MathematicalPhysics.Boltzmann.Approximation.CapActualLossDensity
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLabelFreeLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdBounds
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapNonlinearHotLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveNonlinearLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.BackgroundBeamCloseness
import OAI.MathematicalPhysics.Boltzmann.Branching.HotCollisionDecomposition
import OAI.MathematicalPhysics.Boltzmann.Branching.IncomingLossRate
import OAI.MathematicalPhysics.Boltzmann.Branching.MixedPhysicalMeasures
import OAI.MathematicalPhysics.Boltzmann.Branching.RelativeCutoffConvergence
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedThermalChain
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianWeightedConvergence
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdCentralVanishing

namespace OAI

section

/-! # The actual cap family has a positive limit with its full collision terms -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_collision_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.gainDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.gainDensity g) ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.lossDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.lossDensity g) ∧
      Integrable (CollisionCompactness.pairDensity g)
        ((AnnularEnvelope.timePositionVolume F.time).prod volume) ∧ (∀ z, 0 ≤ g z) := by
  obtain ⟨φ,g,hφ,hg,hpair,hgn⟩ := F.exists_positive_nonlinear_limit hcarleman hGLPS hDP hq₁ hq₂
  have hfm n := torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfn n := torusPhysical_nonneg
    (fun z => ((F.approximation (φ n)).solution.value_bounds z).1) q
  have hf n := memLp_one_iff_integrable.mp (F.pairs_ui.memLp (φ n))
  have hterms := CollisionCompactness.weak_gainLoss hfm hfn hg.1 hpair hf
  exact ⟨φ,g,hφ,hg,hterms.1,hterms.2,hpair.2.1,hgn⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Full cold velocity averages converge weak-star to the atomic background -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.cold_spacetime_weakStar_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {a A R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Compactness.WeakStarLInfConverges (coldCylinderVolume a A R)
      (fun n => S.coldAverage (E.indices n) ψ)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
  let ρ := coldCylinderVolume a A R
  let M := escapedConstant s₀ η K α d₀*hotConstant q+JetEnvelopeGain.momentConstant K α γ/a
  let N := 2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))
  let C := |B*M|+|N*B|
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have ham (n) : Measurable (S.coldAverage (E.indices n) ψ) :=
    S.coldAverage_measurable hs₀ hsmax hη hηmax hK hd₀.le hq _ hψ.measurable
  have hbm : Measurable (fun z : ℝ × JetPrototype.Space => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) :=
    GeometricBackground.clamped_background_test_measurable (zero_lt_one.trans_le E.phase_mem.1)
      hK hα.le hγ.le η E.fraction hψ.measurable
  have htime : ∀ᵐ z ∂ρ, z.1 ∈ Icc a A :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hab : ∀ᶠ n in atTop, ∀ᵐ z ∂ρ, |S.coldAverage (E.indices n) ψ z| ≤ C := by
    filter_upwards [E.eventually_coldAverage_bound hs₀ hsmax hη hηmax hK hα
      (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq ha hA hB hψB] with n hn
    filter_upwards [htime] with z hz
    exact (hn z.1 hz z.2).trans ((le_abs_self (B*M)).trans (le_add_of_nonneg_right (abs_nonneg _)))
  have hbb : ∀ᵐ z ∂ρ, |∫ v, ψ v ∂E.background (max 0 z.1) z.2| ≤ C := by
    filter_upwards [htime] with z hz
    have ht : a ≤ max 0 z.1 := hz.1.trans (le_max_right _ _)
    exact (E.background_average_slab_bound hK hα hγ ha ht hψB z.2).trans
      ((le_abs_self (N*B)).trans (le_add_of_nonneg_left (abs_nonneg _)))
  apply Compactness.weakStar_of_exhaustion ham hbm hab hbb coldAxisCutoff coldAxisCutoff_measurable
    (coldAxisCutoff_exhausts a A R)
  intro m
  have hw : Published.WeakL1Converges (ρ.restrict (coldAxisCutoff m))
      (fun n => S.coldAverage (E.indices n) ψ)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
    change Published.WeakL1Converges ((coldCylinderVolume a A R).restrict (coldAxisCutoff m)) _ _
    rw [coldCylinderVolume_restrict_axis]
    apply E.cold_away_axis_weak_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq ha hA (by positivity) hR (coldTransverseAnnulus R m) (coldTransverseAnnulus_compact R m)
      (fun _ hx => hx.2) (fun y hy => ?_) (Icc (-R) R) isCompact_Icc
      (fun z hz => abs_le.mpr ⟨hz.1,hz.2⟩) hψ hψB
    simpa only [Metric.mem_closedBall,dist_zero_right] using hy.1
  exact hw.weakStar ham hC (hab.mono (fun _ hn => ae_restrict_of_ae hn)) (ae_restrict_of_ae hbb)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual collision error vanishes on the physical cold cylinders -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def physicalCollisionError (S : AttainedCapSequence F) (a A : ℝ) (n : ℕ)
    (z : HotKineticPhase) : ℝ :=
  (S.radius n)^2*CollisionCompactness.collisionSource (F.indices n+1) (S.physicalHotDensity n) z+
    S.coldSourceDensity a A n z

theorem physicalCollisionError_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (a A : ℝ) (n : ℕ) :
    Measurable (S.physicalCollisionError a A n) :=
  ((CollisionCompactness.collisionSource_measurable
    (S.physicalHotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n) _).const_mul _).add
    (S.coldSourceDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq a A n)

theorem HotPairExtraction.vanishing_physical_collision_error
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ a A R : ℝ, 0 < a → a ≤ A →
      ENNReal.ofReal A < E.horizon →
      Tendsto (fun n => eLpNorm (S.physicalCollisionError a A (E.indices (φ n))) 1
        ((coldCylinderVolume a A R).prod volume)) atTop (𝓝 0) := by
  obtain ⟨φ,hφ,herr⟩ := E.vanishing_collision_error hDP hcarleman hGLPS hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨φ,hφ,fun a A R ha haA hA => ?_⟩
  have hw : Tendsto (fun n => eLpNorm (S.physicalCollisionError a A (E.indices (φ n))) 1
      (hotWindowVolume A R)) atTop (𝓝 0) := by
    apply (herr a A R ha haA hA).congr'
    filter_upwards [] with n
    have he : (fun z => (S.radius (E.indices (φ n)))^2*
        CollisionCompactness.collisionSource (F.indices (E.indices (φ n))+1)
          (S.euclideanHot (E.indices (φ n))) z+
        S.coldSourceDensity a A (E.indices (φ n)) (EuclideanFlight.hotChart z)) =
        S.physicalCollisionError a A (E.indices (φ n)) ∘ EuclideanFlight.hotChart := by
      funext z
      rw [euclideanHot_eq_chart]
      rfl
    rw [he]
    exact eLpNorm_comp_measurePreserving
      (S.physicalCollisionError_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ a A _).aestronglyMeasurable
      (EuclideanFlight.hotChart_measurePreserving A R)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hw
    (fun _ => bot_le) (fun n => ?_)
  exact eLpNorm_mono_measure _ (Measure.prod_mono
    (coldCylinderVolume_le_hotBaseWindowVolume ha.le) le_rfl)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual cold-hot pair density on finite positive-time cylinders -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def mixedDensity (S : AttainedCapSequence F) (n : ℕ) (z : HotPairPhase) : ℝ :=
  S.rescaledColdDensity n (z.1,z.2.1)*S.hotDensity n (z.1,z.2.2)

theorem mixedDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.mixedDensity n) :=
  ((S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).comp
    (measurable_fst.prodMk measurable_snd.fst)).mul
    ((S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).comp
      (measurable_fst.prodMk measurable_snd.snd))

theorem mixedDensity_nonneg (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (z : HotPairPhase) :
    0 ≤ S.mixedDensity n z :=
  mul_nonneg (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n _).1
    (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n _)

theorem mixedDensity_integrable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {a A R : ℝ} (ha : 0 ≤ a) :
    Integrable (S.mixedDensity n) ((coldCylinderVolume a A R).prod volume) := by
  let ρ := coldCylinderVolume a A R
  let C := (S.radius n*(2*(F.approximation n).amplitude))*(A+1)
  have hi : Integrable (fun z : HotPairPhase => C*(H q z.2.1*H q z.2.2)) (ρ.prod volume) := by
    have hv := (integrable_H hq).mul_prod (integrable_H hq)
    rw [← Measure.volume_eq_prod] at hv
    exact (hv.comp_snd ρ).const_mul C
  have hb : ∀ᵐ z ∂ρ.prod (volume : Measure Velocity), S.hotDensity n z ≤ (A+1)*H q z.2 :=
    (S.hotDensity_bound hs₀ hsmax hη hηmax hK hd₀ hq n A R).filter_mono
      (ae_mono (Measure.prod_mono (coldCylinderVolume_le_hotBaseWindowVolume ha) le_rfl))
  apply hi.mono' (S.mixedDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    ((S.mixedDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).norm)
    ((((ChartKernel.measurable_H q).comp measurable_snd.fst).mul
      ((ChartKernel.measurable_H q).comp measurable_snd.snd)).const_mul C))).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod hb] with x hx
  have hw : ∀ᵐ p : Velocity × Velocity ∂(volume : Measure Velocity).prod volume,
      S.hotDensity n (x,p.2) ≤ (A+1)*H q p.2 := Measure.quasiMeasurePreserving_snd.ae hx
  rw [Measure.volume_eq_prod]
  filter_upwards [hw] with p hp
  rw [Real.norm_of_nonneg (S.mixedDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n _)]
  exact (mul_le_mul (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n _).2 hp
    (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n _) (by
      exact mul_nonneg (mul_nonneg (S.radius_pos hs₀ n).le (mul_nonneg (by norm_num)
        (F.approximation n).amplitude_pos.le)) (H_nonneg q p.1))).trans_eq (by dsimp only [C,Function.comp_apply,Pi.mul_apply]; ring)

def mixedPrelimitMeasure (S : AttainedCapSequence F) (n : ℕ)
    (ρ : Measure (ℝ × JetPrototype.Space)) : Measure HotPairPhase :=
  (ρ.prod volume).withDensity (fun z => ENNReal.ofReal (S.mixedDensity n z))

theorem mixedPrelimitMeasure_finite (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {a A R : ℝ} (ha : 0 ≤ a) :
    IsFiniteMeasure (S.mixedPrelimitMeasure n (coldCylinderVolume a A R)) := by
  apply isFiniteMeasure_withDensity
  have hi := S.mixedDensity_integrable hs₀ hsmax hη hηmax hK hd₀ hq n (A := A) (R := R) ha
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _
    (S.mixedDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n))).mp hi.hasFiniteIntegral).ne

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Mixed cold-hot velocity moments converge along the actual common sequence -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.mixed_average_weak_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    {B D : ℝ} {ψ χ : Velocity → ℝ}
    (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) (hχ : Measurable χ) (hχD : ∀ v, |χ v| ≤ D) :
    Published.WeakL1Converges (coldCylinderVolume a A R)
      (fun n x => S.coldAverage (E.indices n) ψ x*(∫ v, χ v*S.hotDensity (E.indices n) (x,v)))
      (fun x => (∫ v, ψ v ∂E.toHotLimitExtraction.background (max 0 x.1) x.2)*
        (∫ v, χ v*E.toHotLimitExtraction.cappedHot (x,v))) := by
  let ρ := coldCylinderVolume a A R
  let M := escapedConstant s₀ η K α d₀*hotConstant q+JetEnvelopeGain.momentConstant K α γ/a
  let N := 2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))
  let C := |B*M|+|N*B|
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hα1 : α ≤ 1 := hαmax.trans (by norm_num)
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hρ : ρ ≤ hotBaseWindowVolume A R := coldCylinderVolume_le_hotBaseWindowVolume ha.le
  have hcold := E.toHotLimitExtraction.cold_spacetime_weakStar_limit hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₂ ha hA hR hψ hψB
  have hstrong := E.strong_all_hot_averages hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hα1 hγ
    hd₀ hd₀max hsmall hq₁ hq₂ (ha.le.trans haA) hA R hχ hχD
  have hstrongρ : Tendsto (fun n => eLpNorm (fun x =>
      (∫ v, χ v*S.hotDensity (E.indices n) (x,v))-
      (∫ v, χ v*E.toHotLimitExtraction.cappedHot (x,v))) 1 ρ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrong
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hρ)
  have hhm (n) : Measurable (fun x => ∫ v, χ v*S.hotDensity (E.indices n) (x,v)) :=
    ((hχ.comp measurable_snd).mul
      (S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _)).stronglyMeasurable.integral_prod_right'.measurable
  have hgm : Measurable (fun x => ∫ v, χ v*E.toHotLimitExtraction.cappedHot (x,v)) :=
    ((hχ.comp measurable_snd).mul E.toHotLimitExtraction.cappedHot_measurable).stronglyMeasurable.integral_prod_right'.measurable
  have hgi : Integrable (fun x => ∫ v, χ v*E.toHotLimitExtraction.cappedHot (x,v)) ρ := by
    have hw := (E.toHotLimitExtraction.hotLimit_weak A R).congr_limit
      E.toHotLimitExtraction.cappedHot_measurable (E.toHotLimitExtraction.cappedHot_eq A R).symm
    have hi (n) := memLp_one_iff_integrable.mp
      ((S.hotDensity_uniformIntegrable hs₀ hsmax hη hηmax hK hd₀.le hq₂ A R).memLp (E.indices n))
    exact ((hw.marginal hi (hχ.comp measurable_snd) D (fun z => hχD z.2)).2.1).mono_measure hρ
  have htime : ∀ᵐ x ∂ρ, x.1 ∈ Icc a A :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hac : ∀ᶠ n in atTop, ∀ᵐ x ∂ρ, |S.coldAverage (E.indices n) ψ x| ≤ C := by
    filter_upwards [E.toHotLimitExtraction.eventually_coldAverage_bound hs₀ hsmax hη hηmax hK hα hα1 hγ
      hd₀ hd₀max hsmall hq₂ ha hA hB hψB] with n hn
    filter_upwards [htime] with x hx
    exact (hn x.1 hx x.2).trans ((le_abs_self (B*M)).trans (le_add_of_nonneg_right (abs_nonneg _)))
  have hbc : ∀ᵐ x ∂ρ, |∫ v, ψ v ∂E.toHotLimitExtraction.background (max 0 x.1) x.2| ≤ C := by
    filter_upwards [htime] with x hx
    exact (E.toHotLimitExtraction.background_average_slab_bound hK hα hγ ha
      (hx.1.trans (le_max_right _ _)) hψB x.2).trans
        ((le_abs_self (N*B)).trans (le_add_of_nonneg_left (abs_nonneg _)))
  exact hcold.strong_product
    (fun n => S.coldAverage_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _ hψ.measurable)
    hhm hgm hgi hstrongρ hC hac hbc

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform product Gaussian moments for the actual mixed measures -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem mixedPrelimitMeasure_gaussian_moment (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    (ρ : Measure (ℝ × JetPrototype.Space)) [SFinite ρ] :
    (∫⁻ z, ENNReal.ofReal (weight z.2.1*weight z.2.2) ∂S.mixedPrelimitMeasure n ρ) =
      ∫⁻ x, moment (fun v => S.rescaledColdDensity n (x,v))*moment (fun v => S.hotDensity n (x,v)) ∂ρ := by
  have hc := S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  have hh := S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  have hw : Measurable (fun v : Velocity => weight v) := by unfold weight; fun_prop
  have hwp : Measurable (fun z : HotPairPhase => ENNReal.ofReal (weight z.2.1*weight z.2.2)) :=
    ((hw.comp measurable_snd.fst).mul (hw.comp measurable_snd.snd)).ennreal_ofReal
  rw [mixedPrelimitMeasure,lintegral_withDensity_eq_lintegral_mul _
    (S.mixedDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).ennreal_ofReal hwp]
  have he (z : HotPairPhase) :
      ENNReal.ofReal (S.mixedDensity n z)*ENNReal.ofReal (weight z.2.1*weight z.2.2) =
      ENNReal.ofReal (weight z.2.1*S.rescaledColdDensity n (z.1,z.2.1))*
      ENNReal.ofReal (weight z.2.2*S.hotDensity n (z.1,z.2.2)) := by
    rw [← ENNReal.ofReal_mul (S.mixedDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n z),
      ← ENNReal.ofReal_mul (mul_nonneg (weight_pos _).le
        (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n _).1)]
    congr 1
    dsimp only [mixedDensity]
    ring
  simp_rw [Pi.mul_apply,he]
  have hm : Measurable (fun z : HotPairPhase =>
      ENNReal.ofReal (weight z.2.1*S.rescaledColdDensity n (z.1,z.2.1))*
      ENNReal.ofReal (weight z.2.2*S.hotDensity n (z.1,z.2.2))) :=
    (((hw.comp measurable_snd.fst).mul (hc.comp (measurable_fst.prodMk measurable_snd.fst))).ennreal_ofReal).mul
      (((hw.comp measurable_snd.snd).mul (hh.comp (measurable_fst.prodMk measurable_snd.snd))).ennreal_ofReal)
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro x
  change (∫⁻ y : Velocity × Velocity,
    ENNReal.ofReal (weight y.1*S.rescaledColdDensity n (x,y.1))*
      ENNReal.ofReal (weight y.2*S.hotDensity n (x,y.2))) = _
  rw [Measure.volume_eq_prod]
  exact lintegral_prod_mul
    (f := fun v => ENNReal.ofReal (weight v*S.rescaledColdDensity n (x,v)))
    (g := fun v => ENNReal.ofReal (weight v*S.hotDensity n (x,v)))
    ((hw.mul (hc.comp (measurable_const.prodMk measurable_id))).ennreal_ofReal.aemeasurable)
    ((hw.mul (hh.comp (measurable_const.prodMk measurable_id))).ennreal_ofReal.aemeasurable)

theorem eventually_mixedPrelimitMeasure_gaussian_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop,
      (∫⁻ z, ENNReal.ofReal (weight z.2.1*weight z.2.2)
        ∂S.mixedPrelimitMeasure (κ n) (coldCylinderVolume a A R)) ≤
      ENNReal.ofReal ((escapedConstant s₀ η K α d₀*hotConstant q+
        JetEnvelopeGain.momentConstant K α γ/a)*((A+1)*hotConstant q))*
        coldCylinderVolume a A R univ := by
  have hc := S.eventually_rescaledColdDensity_moment hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq hκ hU ha hA
  filter_upwards [hc] with n hn
  rw [S.mixedPrelimitMeasure_gaussian_moment hs₀ hsmax hη hηmax hK hd₀.le hq]
  have hb : ∀ᵐ z ∂(coldCylinderVolume a A R).prod (volume : Measure Velocity),
      S.hotDensity (κ n) z ≤ (A+1)*VelocityWeight.H q z.2 :=
    (S.hotDensity_bound hs₀ hsmax hη hηmax hK hd₀.le hq (κ n) A R).filter_mono
      (ae_mono (Measure.prod_mono (coldCylinderVolume_le_hotBaseWindowVolume ha.le) le_rfl))
  have ht : ∀ᵐ x ∂coldCylinderVolume a A R, x.1 ∈ Icc a A :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  calc
    _ ≤ ∫⁻ _x : ℝ × JetPrototype.Space,
        ENNReal.ofReal (escapedConstant s₀ η K α d₀*hotConstant q+
          JetEnvelopeGain.momentConstant K α γ/a)*ENNReal.ofReal ((A+1)*hotConstant q) ∂coldCylinderVolume a A R := by
      apply lintegral_mono_ae
      filter_upwards [ht,Measure.ae_ae_of_ae_prod hb] with x hx hxb
      exact mul_le_mul' (hn x.1 hx x.2)
        ((moment_mono_ae hxb).trans_eq (hot_moment hq (by linarith)))
    _ = _ := by
      rw [lintegral_const,← ENNReal.ofReal_mul]
      exact add_nonneg
        (mul_nonneg (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _) (hotConstant_nonneg q))
        (div_nonneg (JetEnvelopeGain.momentConstant_nonneg hK α γ) ha.le)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Tensor integrals of the actual mixed prelimit measure -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem mixedPrelimitMeasure_integral (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    (ρ : Measure (ℝ × JetPrototype.Space)) (f : HotPairPhase → ℝ) :
    (∫ z, f z ∂S.mixedPrelimitMeasure n ρ) = ∫ z, S.mixedDensity n z*f z ∂ρ.prod volume := by
  rw [mixedPrelimitMeasure,integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [ENNReal.toReal_ofReal (S.mixedDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n _),smul_eq_mul]
  · exact (S.mixedDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

theorem mixedPrelimitMeasure_tensor (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    (ρ : Measure (ℝ × JetPrototype.Space)) [SFinite ρ]
    (θ : ℝ × JetPrototype.Space → ℝ) (ψ χ : Velocity → ℝ)
    (hi : Integrable (fun z => S.mixedDensity n z*(θ z.1*(ψ z.2.1*χ z.2.2))) (ρ.prod volume)) :
    (∫ z, θ z.1*(ψ z.2.1*χ z.2.2) ∂S.mixedPrelimitMeasure n ρ) =
      ∫ x, θ x*(S.coldAverage n ψ x*(∫ v, χ v*S.hotDensity n (x,v))) ∂ρ := by
  rw [S.mixedPrelimitMeasure_integral hs₀ hsmax hη hηmax hK hd₀ hq n ρ,
    integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with x
  have he : (fun p : Velocity × Velocity => S.mixedDensity n (x,p)*(θ x*(ψ p.1*χ p.2))) =
      (fun p => θ x*((ψ p.1*S.rescaledColdDensity n (x,p.1))*(χ p.2*S.hotDensity n (x,p.2)))) := by
    funext p
    dsimp only [mixedDensity]
    ring
  rw [he,integral_const_mul,Measure.volume_eq_prod,
    integral_prod_mul (fun v => ψ v*S.rescaledColdDensity n (x,v))
      (fun v => χ v*S.hotDensity n (x,v))]
  rfl

theorem mixed_tensor_integrable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {a A R : ℝ} (ha : 0 ≤ a)
    {θ : ℝ × JetPrototype.Space → ℝ} {ψ χ : Velocity → ℝ}
    (hθ : Measurable θ) (hψ : Measurable ψ) (hχ : Measurable χ)
    {B C D : ℝ} (hθB : ∀ x, |θ x| ≤ B) (hψC : ∀ v, |ψ v| ≤ C) (hχD : ∀ v, |χ v| ≤ D) :
    Integrable (fun z => S.mixedDensity n z*(θ z.1*(ψ z.2.1*χ z.2.2)))
      ((coldCylinderVolume a A R).prod volume) := by
  have hm : Measurable (fun z : HotPairPhase => θ z.1*(ψ z.2.1*χ z.2.2)) :=
    (hθ.comp measurable_fst).mul ((hψ.comp measurable_snd.fst).mul (hχ.comp measurable_snd.snd))
  have hb (z : HotPairPhase) : |θ z.1*(ψ z.2.1*χ z.2.2)| ≤ |B| *(|C| *|D|) := by
    simp only [abs_mul]
    exact mul_le_mul ((hθB _).trans (le_abs_self B))
      (mul_le_mul ((hψC _).trans (le_abs_self C)) ((hχD _).trans (le_abs_self D))
        (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  exact ((S.mixedDensity_integrable hs₀ hsmax hη hηmax hK hd₀ hq n ha).bdd_mul
    hm.aestronglyMeasurable (ae_of_all _ hb)).congr (ae_of_all _ (fun z => mul_comm _ _))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual mixed measures converge on separated space-time and velocity tests -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.mixed_measure_tensor_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    {B C D : ℝ} {θ : ℝ × JetPrototype.Space → ℝ} {ψ χ : Velocity → ℝ}
    (hθ : Measurable θ) (hθB : ∀ x, |θ x| ≤ B)
    (hψ : Continuous ψ) (hψC : ∀ v, |ψ v| ≤ C) (hχ : Measurable χ) (hχD : ∀ v, |χ v| ≤ D) :
    Tendsto (fun n => ∫ z, θ z.1*(ψ z.2.1*χ z.2.2)
      ∂S.mixedPrelimitMeasure (E.indices n) (coldCylinderVolume a A R)) atTop
      (𝓝 (∫ z, θ z.1*(ψ z.2.1*χ z.2.2)
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  let ρ := coldCylinderVolume a A R
  have htime : ∀ᵐ x ∂ρ, a ≤ x.1 := (Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Icc)).mono (fun _ hx => hx.1)
  let _ : IsFiniteMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ ρ) :=
    E.toHotLimitExtraction.mixedMeasure_finite ha (ha.le.trans haA) hK hα hγ hq₂ ρ
      ((Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono (fun _ hx => hx.2))
  have htestm : Measurable (fun z : HotPairPhase => θ z.1*(ψ z.2.1*χ z.2.2)) :=
    (hθ.comp measurable_fst).mul ((hψ.measurable.comp measurable_snd.fst).mul (hχ.comp measurable_snd.snd))
  have hb (z : HotPairPhase) : |θ z.1*(ψ z.2.1*χ z.2.2)| ≤ |B| *(|C| *|D|) := by
    simp only [abs_mul]
    exact mul_le_mul ((hθB _).trans (le_abs_self B))
      (mul_le_mul ((hψC _).trans (le_abs_self C)) ((hχD _).trans (le_abs_self D))
        (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have htesti := Integrable.of_bound (μ := E.toHotLimitExtraction.mixedMeasure ha hK hα hγ ρ)
    htestm.aestronglyMeasurable _ (ae_of_all _ hb)
  have hleft (n) : (∫ z, θ z.1*(ψ z.2.1*χ z.2.2) ∂S.mixedPrelimitMeasure (E.indices n) ρ) =
      ∫ x, θ x*(S.coldAverage (E.indices n) ψ x*(∫ v, χ v*S.hotDensity (E.indices n) (x,v))) ∂ρ :=
    S.mixedPrelimitMeasure_tensor hs₀ hsmax hη hηmax hK hd₀.le hq₂ _ ρ θ ψ χ
      (S.mixed_tensor_integrable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _ ha.le hθ hψ.measurable hχ hθB hψC hχD)
  have hright : (∫ z, θ z.1*(ψ z.2.1*χ z.2.2)
      ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ ρ) =
      ∫ x, θ x*((∫ v, ψ v ∂E.toHotLimitExtraction.background (max 0 x.1) x.2)*
        (∫ v, χ v*E.toHotLimitExtraction.cappedHot (x,v))) ∂ρ := by
    rw [E.toHotLimitExtraction.mixedMeasure_tensor_on_slab ha hK hα hγ ρ htime θ ψ χ htesti]
    apply integral_congr_ae
    filter_upwards [htime] with x hx
    rw [max_eq_right (ha.le.trans hx)]
    congr 2
    apply integral_congr_ae
    exact ae_of_all _ (fun v => mul_comm _ _)
  dsimp only [ρ] at hleft hright
  simp_rw [hleft]
  rw [hright]
  exact (E.mixed_average_weak_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hψ hψC hχ hχD).2.2 θ hθ ⟨B,hθB⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual mixed measures converge for compact continuous velocity-pair tests -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.mixed_measure_compact_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    {B : ℝ} {θ : ℝ × JetPrototype.Space → ℝ} (hθ : Measurable θ) (hθB : ∀ x, |θ x| ≤ B)
    (k : C(Velocity × Velocity, ℝ)) (hk : HasCompactSupport k) :
    Tendsto (fun n => ∫ z, θ z.1*k z.2
      ∂S.mixedPrelimitMeasure (E.indices n) (coldCylinderVolume a A R)) atTop
      (𝓝 (∫ z, θ z.1*k z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  let ρ := coldCylinderVolume a A R
  let μ : ℕ → Measure HotPairPhase := fun n => S.mixedPrelimitMeasure (E.indices n) ρ
  let ν := E.toHotLimitExtraction.mixedMeasure ha hK hα hγ ρ
  let _ (n) : IsFiniteMeasure (μ n) := S.mixedPrelimitMeasure_finite
    hs₀ hsmax hη hηmax hK hd₀.le hq₂ _ ha.le
  let _ : IsFiniteMeasure ν := E.toHotLimitExtraction.mixedMeasure_finite
    ha (ha.le.trans haA) hK hα hγ hq₂ ρ
    ((Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono (fun _ hx => hx.2))
  have hm : Tendsto (fun n => (μ n).real univ) atTop (𝓝 (ν.real univ)) := by
    have ht := E.mixed_measure_tensor_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR
      (θ := fun _ => 1) (ψ := fun _ => 1) (χ := fun _ => 1)
      measurable_const (B := 1) (fun _ => by norm_num) continuous_const (C := 1)
      (fun _ => by norm_num) measurable_const (D := 1) (fun _ => by norm_num)
    simpa only [one_mul,integral_const,smul_eq_mul,mul_one,μ,ν,ρ] using ht
  have hμ : ∀ᶠ n in atTop, (μ n).real univ ≤ ν.real univ+1 :=
    (hm.eventually (gt_mem_nhds (lt_add_one (ν.real univ)))).mono (fun _ hn => hn.le)
  apply Compactness.weighted_supported_integral_tendsto_of_tensor_tests
    hθ hθB (C := ν.real univ+1) (by positivity) hμ _ k hk
  intro f g hf hg
  obtain ⟨C,hC⟩ := f.continuous.bounded_above_of_compact_support hf
  obtain ⟨D,hD⟩ := g.continuous.bounded_above_of_compact_support hg
  exact E.mixed_measure_tensor_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB f.continuous hC g.continuous.measurable hD

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual mixed-measure convergence for the full hard-sphere growth class -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.mixed_measure_linear_growth_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    {B : ℝ} {θ : ℝ × JetPrototype.Space → ℝ} (hθ : Measurable θ) (hθB : ∀ x, |θ x| ≤ B)
    (k : C(Velocity × Velocity, ℝ)) {L : ℝ} (hL : 0 ≤ L)
    (hk : ∀ p, |k p| ≤ L*(1+‖p.1‖+‖p.2‖)) :
    Tendsto (fun n => ∫ z, θ z.1*k z.2
      ∂S.mixedPrelimitMeasure (E.indices n) (coldCylinderVolume a A R)) atTop
      (𝓝 (∫ z, θ z.1*k z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  let ρ := coldCylinderVolume a A R
  let C : ℝ≥0∞ := ENNReal.ofReal ((escapedConstant s₀ η K α d₀*hotConstant q+
    JetEnvelopeGain.momentConstant K α γ/a)*((A+1)*hotConstant q))*ρ univ
  let D : ℝ≥0∞ := ENNReal.ofReal ((2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))*
    Real.exp ((1+α)^2/2))*((A+1)*hotConstant q))*ρ univ
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ρ univ)
  have hD : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ρ univ)
  have hm := S.eventually_mixedPrelimitMeasure_gaussian_bound hs₀ hsmax hη hηmax hK hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ E.indices_strict E.horizon_limit (R := R) ha haA hA
  have hn := E.toHotLimitExtraction.mixedMeasure_gaussian_bound ha (ha.le.trans haA)
    hK hα hγ hq₂ ρ
    ((Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
      (fun _ hx => hx.2))
  apply Compactness.gaussian_weighted_integral_tendsto
    (C := C.toReal) (D := D.toReal) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (by simpa only [ENNReal.ofReal_toReal hC] using hm)
    (by simpa only [ENNReal.ofReal_toReal hD] using hn) hθ hθB _ k hL hk
  intro g hg
  exact E.mixed_measure_compact_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB g hg

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Removal of the actual finite-cap relative-velocity cutoff -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def collisionCutoff (_S : AttainedCapSequence F) (n : ℕ) : ℝ := F.indices n+1

theorem collisionCutoff_tendsto (S : AttainedCapSequence F) :
    Tendsto S.collisionCutoff atTop atTop := by
  exact tendsto_atTop_add_const_right atTop (1 : ℝ)
    (tendsto_natCast_atTop_atTop.comp F.indices_tendsto)

theorem HotPairExtraction.mixed_relative_cutoff_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R : ℝ}
    (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < E.horizon) (hR : 0 ≤ R)
    {B : ℝ} {θ : ℝ × JetPrototype.Space → ℝ} (hθ : Measurable θ) (hθB : ∀ x, |θ x| ≤ B)
    (k : C(Velocity × Velocity, ℝ)) {L : ℝ} (hL : 0 ≤ L)
    (hk : ∀ p, |k p| ≤ L*(1+‖p.1‖+‖p.2‖)) :
    Tendsto (fun n => ∫ z, θ z.1*relativeCutoff (S.collisionCutoff (E.indices n)) k z.2
      ∂S.mixedPrelimitMeasure (E.indices n) (coldCylinderVolume a A R)) atTop
      (𝓝 (∫ z, θ z.1*k z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  let ρ := coldCylinderVolume a A R
  let C : ℝ≥0∞ := ENNReal.ofReal ((escapedConstant s₀ η K α d₀*hotConstant q+
    JetEnvelopeGain.momentConstant K α γ/a)*((A+1)*hotConstant q))*ρ univ
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ρ univ)
  have hm := S.eventually_mixedPrelimitMeasure_gaussian_bound hs₀ hsmax hη hηmax hK hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ E.indices_strict E.horizon_limit
    (R := R) ha haA hA
  apply relative_cutoff_integral_tendsto (M := C.toReal) ENNReal.toReal_nonneg
    (by simpa only [ENNReal.ofReal_toReal hC] using hm)
    (S.collisionCutoff_tendsto.comp E.indices_strict.tendsto_atTop) hθ hθB
    k.continuous.measurable hL hk
  exact E.mixed_measure_linear_growth_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB k hL hk

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Gain and loss tests pass to the actual cold--hot limit without velocity cutoffs -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.mixed_incoming_collision_limit
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
    Tendsto (fun n => ∫ z, θ z.1*incomingGainTest φ z.2
      ∂S.mixedPrelimitMeasure (E.indices n) (coldCylinderVolume a A R)) atTop
      (𝓝 (∫ z, θ z.1*incomingGainTest φ z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) ∧
    Tendsto (fun n => ∫ z, θ z.1*incomingLossTest φ z.2
      ∂S.mixedPrelimitMeasure (E.indices n) (coldCylinderVolume a A R)) atTop
      (𝓝 (∫ z, θ z.1*incomingLossTest φ z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφC 0)
  have hL : 0 ≤ 2*Real.pi*C := mul_nonneg (by positivity) hC
  constructor
  · exact E.mixed_measure_linear_growth_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB
      ⟨incomingGainTest φ,incomingGainTest_continuous hφ⟩ hL
      (fun p => (incomingTests_linear_growth hφC p).1)
  · exact E.mixed_measure_linear_growth_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB
      ⟨incomingLossTest φ,incomingLossTest_continuous hφ⟩ hL
      (fun p => (incomingTests_linear_growth hφC p).2)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual cold--hot collision rates are integrable on every positive-time cylinder -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_mixedPreRate_integrable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ b : ℝ,
      Integrable (mixedPreRate b (S.rescaledColdDensity (κ n)) (S.hotDensity (κ n)))
        (((coldCylinderVolume a A R).prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  filter_upwards [S.eventually_mixedPrelimitMeasure_gaussian_bound hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq hκ hU (R := R) ha haA hA] with n hn
  have hm := hn.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (measure_lt_top (coldCylinderVolume a A R) Set.univ))
  have hc := S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq (κ n)
  have hh := S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq (κ n)
  have hcn := fun p => (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀.le hq (κ n) p).1
  have hhn := S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq (κ n)
  have hp := mixed_pair_rate_integrable_of_gaussian hc hh hcn hhn hm
  exact fun b => mixedPreRate_integrable hc hh hcn hhn hp b

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The physical hot collision equation for the actual finite cap solution -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.physicalCold {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) : (ℝ × JetPrototype.Space) × Velocity → ℝ :=
  HotRepresentative.density q (GaussianLocal.state F.coldTotal)

def CapApproximation.physicalHot {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) : (ℝ × JetPrototype.Space) × Velocity → ℝ :=
  HotRepresentative.density q (GaussianLocal.state F.hot)

theorem CapApproximation.physical_hot_collision {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (z : (ℝ × JetPrototype.Space) × Velocity) (hz : z.2 ∈ HotRepresentative.good q) :
    VelocityWeight.H q z.2*F.hotNetSource (z.1.1,(z.1.2,z.2)) =
      2*mixedGainDensity (N+1) F.physicalCold F.physicalHot z-
        F.physicalHot z*KineticCollisionNullSets.frequency (N+1) F.physicalCold z+
        collisionSource (N+1) F.physicalHot z+
        VelocityWeight.H q z.2*F.coldSource (z.1.1,(z.1.2,z.2)) := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hcb (i : JetLattice.Label) (p : (ℝ × JetPrototype.Space) × Velocity) :
      0 ≤ GaussianLocal.state (F.cold i) p ∧
        GaussianLocal.state (F.cold i) p ≤ 2*F.amplitude := by
    refine ⟨hc.2.1 i _,?_⟩
    have hs := hc.2.2.1 {i} (p.1.1,(p.1.2,p.2))
    simp only [Finset.sum_singleton] at hs
    exact hs.trans (F.solution.value_bounds _).2
  exact HotRepresentative.physical_hot_collision_decomposition hq (by positivity)
    (WeightedLocalControl.damping q (N+1) F.amplitude)
    (fun i => GaussianLocal.measurable_state (hc.1 i))
    (GaussianLocal.measurable_state F.solution.measurable_value) hcb
    (fun p => F.solution.value_bounds (p.1.1,(p.1.2,p.2)))
    (fun s p => hc.2.2.1 s (p.1.1,(p.1.2,p.2))) z hz

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Positive finite measures for the physical cap approximants' collision terms -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def physicalGainMeasure (S : AttainedCapSequence F) (a A R : ℝ) (n : ℕ) :
    Measure HotKineticPhase :=
  mixedGainMeasure (coldCylinderVolume a A R) (S.collisionCutoff n)
    (S.rescaledColdDensity n) (S.hotDensity n)

def physicalLossMeasure (S : AttainedCapSequence F) (a A R : ℝ) (n : ℕ) :
    Measure HotKineticPhase :=
  mixedLossMeasure (coldCylinderVolume a A R) (S.collisionCutoff n)
    (S.rescaledColdDensity n) (S.hotDensity n)

theorem eventually_physicalCollisionMeasures_finite (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, IsFiniteMeasure (S.physicalGainMeasure a A R (κ n)) ∧
      IsFiniteMeasure (S.physicalLossMeasure a A R (κ n)) := by
  filter_upwards [S.eventually_mixedPreRate_integrable hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq hκ hU (R := R) ha haA hA] with n hn
  have hc := fun p => (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀.le hq (κ n) p).1
  have hh := S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq (κ n)
  exact ⟨mixedGainMeasure_finite hc hh (hn _),mixedLossMeasure_finite hc hh (hn _)⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weak limit of the actual hot density times the cold collision frequency -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.mixed_physical_loss_limit
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
    Tendsto (fun n => ∫ p, (θ p.1*φ p.2)*
      (S.hotDensity (E.indices n) p*KineticCollisionNullSets.frequency
        (S.collisionCutoff (E.indices n)) (S.rescaledColdDensity (E.indices n)) p)
      ∂(coldCylinderVolume a A R).prod volume) atTop
      (𝓝 (∫ z, θ z.1*incomingLossTest φ z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφC 0)
  have hB : 0 ≤ B := (abs_nonneg (θ (0,0))).trans (hθB (0,0))
  have hψ : Measurable (fun p : (ℝ × JetPrototype.Space) × Velocity => θ p.1*φ p.2) :=
    (hθ.comp measurable_fst).mul (hφ.measurable.comp measurable_snd)
  have hψB (p : (ℝ × JetPrototype.Space) × Velocity) : |θ p.1*φ p.2| ≤ B*C := by
    rw [abs_mul]
    exact mul_le_mul (hθB _) (hφC _) (abs_nonneg _) hB
  have hc := E.mixed_relative_cutoff_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB
    ⟨incomingLossTest φ,incomingLossTest_continuous hφ⟩
    (mul_nonneg (by positivity : 0 ≤ 2*Real.pi) hC)
    (fun p => (incomingTests_linear_growth hφC p).2)
  apply hc.congr'
  filter_upwards [S.eventually_mixedPreRate_integrable hs₀ hsmax hη hηmax hK hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ E.indices_strict E.horizon_limit
    (R := R) ha haA hA] with n hn
  have hr := hn (S.collisionCutoff (E.indices n))
  have hsp := mixedPreRate_swapped_integrable hr
  have hi : Integrable (fun z => (θ z.1.1*φ z.1.2.1)*
      mixedPreRate (S.collisionCutoff (E.indices n)) (S.hotDensity (E.indices n))
        (S.rescaledColdDensity (E.indices n)) z)
      (((coldCylinderVolume a A R).prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    apply hsp.bdd_mul
      (hψ.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      change ‖θ z.1.1*φ z.1.2.1‖ ≤ B*C
      simpa only [Real.norm_eq_abs] using hψB (z.1.1,z.1.2.1))
  have he := mixedLoss_test_incoming (S.collisionCutoff (E.indices n))
    (S.rescaledColdDensity (E.indices n)) (S.hotDensity (E.indices n)) θ φ hi
  have hphysical : (∫ p, (θ p.1*φ p.2)*mixedLossDensity (S.collisionCutoff (E.indices n))
        (S.rescaledColdDensity (E.indices n)) (S.hotDensity (E.indices n)) p
        ∂(coldCylinderVolume a A R).prod volume) =
      ∫ p, (θ p.1*φ p.2)*(S.hotDensity (E.indices n) p*KineticCollisionNullSets.frequency
        (S.collisionCutoff (E.indices n)) (S.rescaledColdDensity (E.indices n)) p)
        ∂(coldCylinderVolume a A R).prod volume := by
    apply integral_congr_ae
    filter_upwards [mixed_loss_ae_eq_frequency hr] with p hp
    rw [hp]
  rw [← hphysical,he,S.mixedPrelimitMeasure_integral hs₀ hsmax hη hηmax hK hd₀.le hq₂]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only [mixedDensity,relativeCutoff]
    simp only [ContinuousMap.coe_mk]
    ring)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weak limit of the actual symmetric mixed gain density -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.mixed_physical_gain_limit
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
    Tendsto (fun n => ∫ p, (θ p.1*φ p.2)*
      mixedGainDensity (S.collisionCutoff (E.indices n))
        (S.rescaledColdDensity (E.indices n)) (S.hotDensity (E.indices n)) p
      ∂(coldCylinderVolume a A R).prod volume) atTop
      (𝓝 (∫ z, θ z.1*incomingGainTest φ z.2
        ∂E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφC 0)
  have hB : 0 ≤ B := (abs_nonneg (θ (0,0))).trans (hθB (0,0))
  have hψ : Measurable (fun p : (ℝ × JetPrototype.Space) × Velocity => θ p.1*φ p.2) :=
    (hθ.comp measurable_fst).mul (hφ.measurable.comp measurable_snd)
  have hψB (p : (ℝ × JetPrototype.Space) × Velocity) : |θ p.1*φ p.2| ≤ B*C := by
    rw [abs_mul]
    exact mul_le_mul (hθB _) (hφC _) (abs_nonneg _) hB
  have hc := E.mixed_relative_cutoff_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB
    ⟨incomingGainTest φ,incomingGainTest_continuous hφ⟩
    (mul_nonneg (by positivity : 0 ≤ 2*Real.pi) hC)
    (fun p => (incomingTests_linear_growth hφC p).1)
  apply hc.congr'
  filter_upwards [S.eventually_mixedPreRate_integrable hs₀ hsmax hη hηmax hK hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ E.indices_strict E.horizon_limit
    (R := R) ha haA hA] with n hn
  have hr := hn (S.collisionCutoff (E.indices n))
  have he := mixedGain_test_incoming (S.collisionCutoff (E.indices n))
    (S.rescaledColdDensity (E.indices n)) (S.hotDensity (E.indices n)) θ φ
    (mixedPostRate_test_integrable hr hψ hψB)
    (mixedPostRate_test_integrable (mixedPreRate_swapped_integrable hr) hψ hψB)
    (mixedPreRate_sum_test_integrable hr hψ hψB)
  rw [he,S.mixedPrelimitMeasure_integral hs₀ hsmax hη hηmax hK hd₀.le hq₂]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only [mixedDensity,relativeCutoff]
    simp only [ContinuousMap.coe_mk]
    ring)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Exact mixed collision equation under the attained cap dilation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def collisionDilation (S : AttainedCapSequence F) (n : ℕ)
    (x : ℝ × JetPrototype.Space) : ℝ × JetPrototype.Space :=
  (S.radius n*x.1,S.radius n • x.2)

theorem rescaledColdDensity_eq_physical (S : AttainedCapSequence F) (n : ℕ) :
    S.rescaledColdDensity n = fun z => S.radius n*
      (F.approximation n).physicalCold (S.collisionDilation n z.1,z.2) := by
  funext z
  unfold rescaledColdDensity CapApproximation.physicalCold HotRepresentative.density
    GaussianLocal.state collisionDilation
  ring

theorem physicalHotDensity_eq_physical (S : AttainedCapSequence F) (n : ℕ) :
    S.physicalHotDensity n = fun z => (S.radius n)⁻¹*
      (F.approximation n).physicalHot (S.collisionDilation n z.1,z.2) := by
  funext z
  unfold physicalHotDensity rescaledHot CapApproximation.physicalHot HotRepresentative.density
    GaussianLocal.state collisionDilation
  ring

theorem rescaled_hot_collision (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (n : ℕ) (z : HotKineticPhase) (hz : z.2 ∈ HotRepresentative.good q) :
    H q z.2*S.rescaledHotSource n (z.1.1,(z.1.2,z.2)) =
      2*mixedGainDensity (F.indices n+1) (S.rescaledColdDensity n) (S.physicalHotDensity n) z-
        S.physicalHotDensity n z*KineticCollisionNullSets.frequency (F.indices n+1) (S.rescaledColdDensity n) z+
        (S.radius n)^2*collisionSource (F.indices n+1) (S.physicalHotDensity n) z+
        H q z.2*S.rescaledColdSource n (z.1.1,(z.1.2,z.2)) := by
  have hs :
      2*mixedGainDensity (F.indices n+1) (S.rescaledColdDensity n) (S.physicalHotDensity n) z-
        S.physicalHotDensity n z*KineticCollisionNullSets.frequency (F.indices n+1) (S.rescaledColdDensity n) z+
        (S.radius n)^2*collisionSource (F.indices n+1) (S.physicalHotDensity n) z =
      2*mixedGainDensity (F.indices n+1) (F.approximation n).physicalCold (F.approximation n).physicalHot
          (S.collisionDilation n z.1,z.2)-
        (F.approximation n).physicalHot (S.collisionDilation n z.1,z.2)*
          KineticCollisionNullSets.frequency (F.indices n+1) (F.approximation n).physicalCold
            (S.collisionDilation n z.1,z.2)+
        collisionSource (F.indices n+1) (F.approximation n).physicalHot (S.collisionDilation n z.1,z.2) := by
    rw [S.rescaledColdDensity_eq_physical,S.physicalHotDensity_eq_physical]
    simpa only [mixedGain_base_comp,cutoffFrequency_base_comp,collisionSource_base_comp] using
      mixed_source_rescale (F.indices n+1) (S.radius n) (S.radius_pos hs₀ n).ne'
        (fun p => (F.approximation n).physicalCold (S.collisionDilation n p.1,p.2))
        (fun p => (F.approximation n).physicalHot (S.collisionDilation n p.1,p.2)) z
  rw [hs]
  exact (F.approximation n).physical_hot_collision hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le (S.collisionDilation n z.1,z.2) hz

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Separated-test convergence of the actual physical loss measures -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.loss_measure_separated_limit
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
    Tendsto (fun n => ∫ z, θ z.1*φ z.2 ∂S.physicalLossMeasure a A R (E.indices n)) atTop
      (𝓝 (∫ z, θ z.1*φ z.2 ∂incomingLossMeasure
        (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) := by
  let μ := E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)
  let _ : SFinite μ := by dsimp [μ,HotLimitExtraction.mixedMeasure]; infer_instance
  have hi : Integrable incomingRate μ :=
    E.toHotLimitExtraction.incomingRate_integrable ha (ha.le.trans haA) hK hα hγ hq₂
  have hB : 0 ≤ B := (abs_nonneg (θ (0,0))).trans (hθB _)
  have ht := E.mixed_physical_loss_limit hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hA hR hθ hθB hφ hφC
  rw [← incomingLossMeasure_separated hi hθ hB hθB hφ.measurable hφC] at ht
  apply ht.congr'
  filter_upwards [S.eventually_mixedPreRate_integrable hs₀ hsmax hη hηmax hK hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ E.indices_strict E.horizon_limit
    (R := R) ha haA hA] with n hn
  have hc := fun p => (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n) p).1
  have hh := S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E.indices n)
  dsimp only [physicalLossMeasure]
  rw [mixedLossMeasure_integral hc hh (hn (S.collisionCutoff (E.indices n))) (fun z => θ z.1*φ z.2)]
  apply integral_congr_ae
  filter_upwards [mixed_loss_ae_eq_frequency (hn (S.collisionCutoff (E.indices n)))] with z hz
  rw [hz]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
