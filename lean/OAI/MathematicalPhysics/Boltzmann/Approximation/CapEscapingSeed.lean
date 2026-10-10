import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLimitTransport
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapCoefficientExtraction
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapCoveredDamping
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveEndpointHistory
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveRestrictedChain
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.BackgroundCappedLoss
import OAI.MathematicalPhysics.Boltzmann.Branching.CumulativeIntervalBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.GainMeasureLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion
import OAI.MathematicalPhysics.Boltzmann.Branching.HotWindowGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.SeedEscapeMeasure
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticEndpointCoordinates
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedNonaxialLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeSurvival
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalCharacteristicIdentity
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricDampedRetention

namespace OAI

section

/-! # A globally measurable extension of the actual slab collision frequency -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.characteristicSlabFrequency (E : HotLimitExtraction S)
    (a : ℝ) (u : CharacteristicPhase) : ℝ :=
  GeometricBackground.frequency E.phase η E.fraction K α γ
    (max a (hotCharacteristicEquiv u).1.1)
    (hotCharacteristicEquiv u).1.2 (hotCharacteristicEquiv u).2

theorem HotLimitExtraction.characteristicSlabFrequency_measurable (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    Measurable (E.characteristicSlabFrequency a) := by
  have hp : Measurable (fun z : HotKineticPhase => ((max a z.1.1,z.1.2),z.2)) := by fun_prop
  have hm := (GeometricBackground.clamped_frequency_measurable
    (zero_lt_one.trans_le E.phase_mem.1) hK hα hγ η E.fraction).comp
    (hp.comp hotCharacteristicEquiv.measurable)
  convert hm using 1
  funext u
  dsimp [Function.comp_def,HotLimitExtraction.characteristicSlabFrequency]
  rw [max_eq_right (ha.le.trans (le_max_left a _))]

theorem HotLimitExtraction.characteristicSlabFrequency_eq (E : HotLimitExtraction S)
    {a : ℝ} {u : CharacteristicPhase} (hu : a ≤ u.1) :
    E.characteristicSlabFrequency a u = E.characteristicFrequency u := by
  unfold HotLimitExtraction.characteristicSlabFrequency HotLimitExtraction.characteristicFrequency
  have ht : (hotCharacteristicEquiv u).1.1 = u.1 := rfl
  rw [ht,max_eq_right hu]

theorem HotLimitExtraction.characteristicLossDensity_slab_factor (E : HotLimitExtraction S)
    (a A R : ℝ) (u : CharacteristicPhase) :
    E.characteristicLossDensity a A R u =
      cylinderPullback a A R E.hotLimit u*E.characteristicSlabFrequency a u := by
  by_cases hu : hotCharacteristicEquiv u ∈ coldCylinderSet a A R
  · rw [E.characteristicLossDensity_factor,
      E.characteristicSlabFrequency_eq (show a ≤ u.1 from hu.1.1.1)]
  · simp only [HotLimitExtraction.characteristicLossDensity,cylinderPullback,Function.comp_def,
      indicator_of_notMem hu,zero_mul]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Concrete damping constants on compact characteristic phase sets -/

noncomputable section

open Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristic_frequency_compact_bound (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    {β : Velocity × Velocity → ℝ} (hc : HasCompactSupport β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : CharacteristicPhase,
      a ≤ u.1 → u.2 ∈ tsupport β → E.characteristicFrequency u ≤ C := by
  obtain ⟨V,hV,hb⟩ := hc.isCompact.isBounded.exists_pos_norm_le
  let C := (GeometricBackground.lossCoefficient K α γ/a)*(V+1+α)
  have hcoef : 0 ≤ GeometricBackground.lossCoefficient K α γ/a :=
    div_nonneg (GeometricBackground.lossCoefficient_nonneg hK α γ) ha.le
  refine ⟨C,mul_nonneg hcoef (by positivity),?_⟩
  intro u ht hu
  have hv : ‖(hotCharacteristicEquiv u).2‖ ≤ V := (norm_snd_le u.2).trans (hb _ hu)
  have hf := GeometricBackground.frequency_slab_bound (η := η)
    (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ ha ht
    (hotCharacteristicEquiv u).1.2 (hotCharacteristicEquiv u).2
  exact hf.trans (mul_le_mul_of_nonneg_left (by linarith only [hv]) hcoef)

theorem HotLimitExtraction.characteristic_frequency_near_clock (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) {r ε : ℝ}
    (hr : 0 < r) (hε : ε ≤ 1/4) (u : CharacteristicPhase) (ht : 0 ≤ u.1)
    (hv : ‖u.2.2‖ ≤ 6)
    (hnear : ReferenceGeometry.BeamNear
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1) hα hγ η r)
      ε (u.1,PlaneChart.join (hotCharacteristicEquiv u).1.2.1
        (hotCharacteristicEquiv u).1.2.2)) :
    E.characteristicFrequency u ≤ (K/(4*r))*(48*Real.pi) := by
  have hh := GeometricBackground.frequency_le_near_clock
    (zero_lt_one.trans_le E.phase_mem.1) hK hα hγ hr ht η E.fraction
    (PlaneChart.join (hotCharacteristicEquiv u).1.2.1 (hotCharacteristicEquiv u).1.2.2)
    u.2.2 hv hε hnear
  simp only [PlaneChart.transverse_join,PlaneChart.axial_join] at hh
  change GeometricBackground.frequency E.phase η E.fraction K α γ u.1
    ((hotCharacteristicEquiv u).1.2.1,(hotCharacteristicEquiv u).1.2.2) u.2.2 ≤ _
  exact hh

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot trace has one positive gain-and-retention source -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.retainedSource (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (A R C : ℝ) (β : WeakTime.Phase → ℝ) : Measure CharacteristicPhase :=
  WeakTime.weightedPhaseSource
    (E.characteristicGainKernel ha hK hα hγ ∘ₘ
      positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit)) β+
  positiveDensityMeasure volume (fun z => C*WeakTime.phaseWeight β
    (cylinderPullback a A R E.hotLimit) z-
      WeakTime.phaseWeight β (E.characteristicLossDensity a A R) z)

theorem HotPairExtraction.characteristic_combined_source_balance
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
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t =
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s+
      WeakTime.dampedSourceIncrement a A C s t
        (E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β) := by
  obtain ⟨R,hR,hbalance⟩ := E.characteristic_damped_measure_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  have hFi := (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le
    ((ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB) R).2.1
  have hF := (WeakTime.phaseWeight_integrable hβ.continuous hβc
    (cylinderPullback_integrable hFi)).aemeasurable
  have hL := (WeakTime.phaseWeight_integrable hβ.continuous hβc
    (E.toHotLimitExtraction.characteristicLossDensity_integrable (R := R)
      ha haA.le hK hα hγ hq₂)).aemeasurable
  refine ⟨R,hR,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst
  have h := WeakTime.undamp_combined_source_balance _ hsa hta hF hL (ht hsa hta hst)
  rw [E.toHotLimitExtraction.characteristicGain_eq_kernel ha hK hα hγ] at h
  exact h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Retaining full support coverage in the combined positive source balance -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_characteristic_combined_source_balance
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
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t =
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s+
      WeakTime.dampedSourceIncrement a A C s t
        (E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β) := by
  obtain ⟨R,hR,hcover,hbalance⟩ := E.covered_characteristic_damped_measure_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  have hFi := (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le
    ((ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB) R).2.1
  have hF := (WeakTime.phaseWeight_integrable hβ.continuous hβc
    (cylinderPullback_integrable hFi)).aemeasurable
  have hL := (WeakTime.phaseWeight_integrable hβ.continuous hβc
    (E.toHotLimitExtraction.characteristicLossDensity_integrable (R := R)
      ha haA.le hK hα hγ hq₂)).aemeasurable
  refine ⟨R,hR,hcover,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst
  have h := WeakTime.undamp_combined_source_balance _ hsa hta hF hL (ht hsa hta hst)
  rw [E.toHotLimitExtraction.characteristicGain_eq_kernel ha hK hα hγ] at h
  exact h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The cap fifth gain vanishes along every convergent nonaxial endpoint sequence -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_convergent_nonaxial_five_gain (E : HotLimitExtraction S)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hTU : ENNReal.ofReal T ≤ E.horizon)
    (hz : ∀ A, 0 < A → A < T → ∀ R, (E.hotLimit ∘ EuclideanFlight.hotChart)
      =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0)
    {z : ℕ → Published.KineticPhase} {z₀ : Published.KineticPhase}
    (hlim : Tendsto z atTop (𝓝 z₀)) (hv₀ : transverse z₀.2 ≠ 0)
    (htime : ∀ n, (z n).1.1 ∈ Icc a T) :
    Tendsto (fun n => iterate a
      (positiveMainKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      (fun y => ENNReal.ofReal (S.boundedHotRatio (E.indices n) y)) 5 (z n)) atTop (𝓝 0) := by
  obtain ⟨X,_,hX⟩ := (Metric.isBounded_range_of_tendsto _ hlim.fst_nhds.snd_nhds).exists_pos_norm_le
  obtain ⟨R,b,hR,hb,hw⟩ := eventually_velocityWindow hlim.snd_nhds hv₀
  obtain ⟨N,hN⟩ := eventually_atTop.1 hw
  let φ : ℕ → ℕ := fun n => n+N
  have hφ : StrictMono φ := fun i j h => Nat.add_lt_add_right h N
  have hstates : Tendsto (fun n => toKinetic.symm (z (φ n))) atTop
      (𝓝 (z₀.1.1,WithLp.ofLp z₀.1.2,WithLp.ofLp z₀.2)) :=
    (fromKinetic_continuous.continuousAt.tendsto.comp hlim).comp hφ.tendsto_atTop
  have h := (E.subsequence φ hφ).zero_closed_nonaxial_five_gain hMityagin hs₀ hsmax hη hηmax
    hK hα hγ hd₀ hdmax hq₁ hq₂ ha hT hR hb hTU hz z₀.1.1 (WithLp.ofLp z₀.1.2)
    (WithLp.ofLp z₀.2) (nonaxial_of_transverse_ne_zero hv₀)
    (fun n => toKinetic.symm (z (φ n))) hstates (fun n => htime (φ n))
    (fun n => hX _ (mem_range_self (φ n))) (fun n => hN (φ n) (Nat.le_add_left N n))
  have he (n) : toKinetic (toKinetic.symm (z (φ n))) = z (φ n) := toKinetic.apply_symm_apply _
  simp only [he] at h
  exact (tendsto_add_atTop_iff_nat N).1 h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Positive survival of the actual hot-limit characteristic trace -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_survival
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
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      Real.exp (C*(s-t))*WeakTime.phaseProjection (cylinderPullback a A R E.hotLimit) φ s ≤
        WeakTime.phaseProjection (cylinderPullback a A R E.hotLimit) φ t := by
  have hA := (ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB
  obtain ⟨C,hC,hbound⟩ := E.toHotLimitExtraction.characteristic_loss_projection_bound
    hs₀ ha haA.le hA hK hα hγ hq₂ hφ.continuous hc hn
  obtain ⟨R,hR,_,hweak⟩ := E.characteristic_weak_time_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hφ hc hn
  refine ⟨R,C,hR,hC,?_⟩
  let μ := E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R
  let _ := E.toHotLimitExtraction.incomingGainMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  have : IsFiniteMeasure μ := by dsimp [μ,HotLimitExtraction.characteristicGainMeasure]; infer_instance
  obtain ⟨D,hD⟩ := hφ.continuous.bounded_above_of_compact_support hc
  let _ := WeakTime.timeSource_finite μ hφ.continuous.measurable hn hD
  apply WeakTime.ae_survival_of_weak_balance haA hC
    (WeakTime.phaseProjection_integrable
      (cylinderPullback_integrable
        (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le hA R).2.1)
      hφ.continuous.measurable hD)
    (WeakTime.phaseProjection_integrable
      (E.toHotLimitExtraction.characteristicLossDensity_integrable ha haA.le hK hα hγ hq₂)
      hφ.continuous.measurable hD)
    (WeakTime.timeSource μ φ) ((hbound R).mono (fun _ ht _ => ht)) hweak

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Exact positive gain increments for the actual hot-limit trace -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_interval_balance
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
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseProjection (cylinderPullback a A R E.hotLimit) φ t+
        (∫ r in s..t, WeakTime.phaseProjection
          (E.toHotLimitExtraction.characteristicLossDensity a A R) φ r) =
      WeakTime.phaseProjection (cylinderPullback a A R E.hotLimit) φ s+
        (WeakTime.timeSource
          (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) φ).real (Ioc s t) := by
  obtain ⟨R,hR,c,hcumulative⟩ := E.characteristic_cumulative_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hφ hc hn
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
  let _ := WeakTime.timeSource_finite μ hφ.continuous.measurable hn hC
  let _ := WeakTime.timeSource_finite ν hφ.continuous.measurable hn hC
  apply WeakTime.ae_interval_balance (WeakTime.timeSource μ φ) (WeakTime.timeSource ν φ)
    (WeakTime.phaseProjection_integrable
      (E.toHotLimitExtraction.characteristicLossDensity_integrable ha haA.le hK hα hγ hq₂)
      hφ.continuous.measurable hC)
    (fun t => E.toHotLimitExtraction.characteristicLoss_cumulative ha haA.le hK hα hγ hq₂
      hφ.continuous.measurable hn hC t) hcumulative

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Every central-cell cap endpoint has vanishing fifth gain under a zero hot limit -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_central_five_gain (E : HotLimitExtraction S)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hTU : ENNReal.ofReal T ≤ E.horizon)
    (hz : ∀ A, 0 < A → A < T → ∀ R, (E.hotLimit ∘ EuclideanFlight.hotChart)
      =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0)
    (z : ℕ → Published.KineticPhase) (htime : ∀ n, (z n).1.1 ∈ Icc a T)
    (hcentral : ∀ n, S.radius (E.indices n) • (z n).1.2 ∈ TorusChart.cube) :
    Tendsto (fun n => iterate a
      (positiveMainKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      (fun y => ENNReal.ofReal (S.boundedHotRatio (E.indices n) y)) 5 (z n)) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨σ,hσ,hnsσ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨τ,hτ,hcases⟩ := kinetic_endpoint_subsequence (fun n => z (ns (σ n)))
    (fun n => htime (ns (σ n)))
  let φ : ℕ → ℕ := ns ∘ σ ∘ τ
  have hφ : StrictMono φ := hnsσ.comp hτ
  let E' := E.subsequence φ hφ
  let r : ℕ → ℝ := fun n => S.radius (E'.indices n)
  let N : ℕ → ℕ := fun n => F.indices (E'.indices n)
  let y : ℕ → Published.KineticPhase := z ∘ φ
  let f := fun n w => ENNReal.ofReal (S.boundedHotRatio (E'.indices n) w)
  have hr (n) : 0 < r n := S.radius_pos hs₀ _
  have ht (n) : (y n).1.1 ∈ Icc a T := htime (φ n)
  have hf (n w) (_ : w.1.1 ∈ Icc a T) : f n w ≤ ENNReal.ofReal 2 :=
    ENNReal.ofReal_le_ofReal (S.boundedHotRatio_bounds _ _).2
  suffices h : Tendsto (fun n => iterate a (positiveMainKernel (r n) s₀ η K α γ d₀ q (N n))
      (f n) 5 (y n)) atTop (𝓝 0) by
    exact ⟨σ ∘ τ,h⟩
  rcases hcases with hv | ⟨⟨V,hV,hvb⟩,hspatial⟩
  · exact positive_five_large_velocity_tendsto hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax
      hd₀ hdmax r hr N y ht hv ENNReal.ofReal_ne_top hf
  · rcases hspatial with hx | hx | ⟨y₀,hlim⟩
    · have hfar (R : ℝ) : ∀ᶠ n in atTop, ∀ k : JetLattice.Lattice,
          R ≤ ‖transverse ((y n).1.2-(r n)⁻¹ • latticeVector k)‖ := by
        filter_upwards [hx.eventually_ge_atTop R] with n hn k
        exact hn.trans (TorusChart.central_transverse_nearest (hr n) (hcentral (φ n)) k)
      exact positive_five_transverse_escape_tendsto hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax
        hd₀ hdmax r hr N y ht hvb hfar ENNReal.ofReal_ne_top hf
    · have hfar (R : ℝ) : ∀ᶠ n in atTop, ∀ k : JetLattice.Lattice,
          R ≤ |axial ((y n).1.2-(r n)⁻¹ • latticeVector k)| := by
        filter_upwards [hx.eventually_ge_atTop R] with n hn k
        exact hn.trans (TorusChart.central_axial_nearest (hr n) (hcentral (φ n)) k)
      exact positive_five_axial_escape_tendsto hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax
        hd₀ hdmax r hr N y ht hvb hfar ENNReal.ofReal_ne_top hf
    · by_cases hv₀ : transverse y₀.2 = 0
      · have htrans : Tendsto (fun n => ‖transverse (y n).2‖) atTop (𝓝 0) := by
          have hcont : Continuous (fun v : Velocity => ‖transverse v‖) := by
            unfold transverse
            fun_prop
          simpa only [y,φ,Function.comp_def,hv₀,norm_zero] using hcont.continuousAt.tendsto.comp hlim.snd_nhds
        exact positive_axial_gain_tendsto hK hα hγ hq₁ hq₂ ha hs₀ hsmax hη hηmax
          hd₀ hdmax hV (by norm_num) r (fun n => (y n).1.1) N (fun n => (y n).1.2)
          (fun n => (y n).2) f hr
          ((S.radius_tendsto_zero hs₀).comp E'.indices_strict.tendsto_atTop) ht hvb htrans hf 3
      · exact E'.zero_convergent_nonaxial_five_gain hMityagin hs₀ hsmax hη hηmax hK hα hγ
          hd₀ hdmax hq₁ hq₂ ha hT hTU hz hlim hv₀ ht

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Free-flight survival for compact portions of the actual hot density -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_free_flight_survival
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
    {β : Velocity × Velocity → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight β
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β
          (E.hotLimit ∘ hotCharacteristicEquiv)) t := by
  obtain ⟨R,_hR,hcover,hweak⟩ := E.covered_characteristic_weak_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hβc
  obtain ⟨C,hC,hfreq⟩ := E.toHotLimitExtraction.characteristic_frequency_compact_bound
    ha hK hα hγ hβc
  have hfrequency (u : CharacteristicPhase) (hu : u.1 ∈ Ioo a A)
      (hp : u.2 ∈ tsupport β) : E.toHotLimitExtraction.characteristicFrequency u ≤ C :=
    hfreq u hu.1.le hp
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
  have hbound : ∀ᵐ u : CharacteristicPhase ∂volume, u.1 ∈ Ioo a A →
      β u.2*E.toHotLimitExtraction.characteristicLossDensity a A R u ≤
        C*(β u.2*cylinderPullback a A R E.hotLimit u) := by
    apply ae_of_all
    intro u hu
    by_cases hz : β u.2 = 0
    · simp only [hz,zero_mul,mul_zero,le_refl]
    rw [E.toHotLimitExtraction.characteristicLossDensity_factor]
    have hb := hfrequency u hu (subset_tsupport β hz)
    have hp : 0 ≤ β u.2*cylinderPullback a A R E.hotLimit u := mul_nonneg (hβn _) (hn u)
    nlinarith only [mul_le_mul_of_nonneg_left hb hp]
  have hbalance := WeakTime.ae_localized_damped_measure_balance haA hC
    (cylinderPullback_integrable hi) hLi (ae_of_all _ hn)
    (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) hβ hβc hβn hbound
    (by
      intro φ hφ hc hφn hφβ θ hθ hθc hθs
      have hb := hweak φ hφ hc hφn hφβ θ hθ hθc hθs
      rw [E.toHotLimitExtraction.characteristicLossMeasure_eq ha haA.le hK hα hγ hq₂,
        positiveDensityMeasure_integral hLi.aemeasurable
          (ae_of_all _ (E.toHotLimitExtraction.characteristicLossDensity_nonneg a A R))] at hb
      exact hb)
  have hF := (WeakTime.phaseWeight_integrable hβ.continuous hβc
    (cylinderPullback_integrable hi)).aemeasurable
  have hL := (WeakTime.phaseWeight_integrable hβ.continuous hβc hLi).aemeasurable
  have heq (t : ℝ) (ht : t ∈ Ioo a A) :
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t =
      WeakTime.phaseSlice (WeakTime.phaseWeight β (E.hotLimit ∘ hotCharacteristicEquiv)) t := by
    unfold WeakTime.phaseSlice positiveDensityMeasure
    congr 1
    funext p
    unfold WeakTime.phaseWeight
    by_cases hp : β p = 0
    · simp only [hp,zero_mul]
    · have hz := hcover t ⟨ht.1.le,ht.2.le⟩ p (subset_tsupport β hp)
      simp only [cylinderPullback,Function.comp_def,indicator_of_mem hz]
  refine ⟨C,hC,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst
  have hh := WeakTime.undamp_combined_source_balance _ hsa hta hF hL (ht hsa hta hst)
  rw [heq s hsa,heq t hta] at hh
  rw [hh]
  exact le_add_of_nonneg_right bot_le

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The zero-cold-fraction case of cap nonvanishing -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_fraction_nonvanishing (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hl : E.fraction = 0) :
    ¬ (∀ A, 0 < A → A < 1 → ∀ R, (E.hotLimit ∘ EuclideanFlight.hotChart)
      =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0) := by
  intro hz
  let G := 2*JetCoreSheet.growthConstant K α γ q
  have hsmallA := (finite_remainder_tendsto G 5).eventually
    (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, a ∈ Ioo 0 1 :=
    Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)
  obtain ⟨a,ha,haSmall⟩ := (hpos.and hsmallA).exists
  let L := ∑ j ∈ Finset.range 5, (G*Real.log (1/a))^j
  have htlim : Tendsto (fun n => S.time (E.indices n)/S.radius (E.indices n)) atTop (𝓝 (1:ℝ)) := by
    simp_rw [S.normalized_time hs₀]
    simpa only [hl,sub_zero] using E.fraction_limit.const_sub 1
  have hres := S.eventually_attained_boundedHotRatio_log_residual hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ E.indices_strict ha.1
  obtain ⟨N,hN⟩ := eventually_atTop.1
    (hres.and (htlim.eventually (lt_mem_nhds ha.2)))
  let φ : ℕ → ℕ := fun n => n+N
  have hφ : StrictMono φ := fun i j h => Nat.add_lt_add_right h N
  let E' := E.subsequence φ hφ
  let B := (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
    JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (2 : ℕ))
  let t := fun n => S.time (E'.indices n)/S.radius (E'.indices n)
  let J := fun n => positiveMainKernel (S.radius (E'.indices n)) s₀ η K α γ d₀ q
    (F.indices (E'.indices n))
  let f := fun n y => ENNReal.ofReal (S.boundedHotRatio (E'.indices n) y)
  let c := fun n => ENNReal.ofReal (a+S.coldFraction (E'.indices n))+S.positiveSourceError B 1 (E'.indices n)
  have ht (n) : t n ∈ Icc a 1 :=
    ⟨(hN (φ n) (Nat.le_add_left N n)).2.le,(S.attained_time_mem hs₀ _).2⟩
  have hw (n) : ∃ p : Velocity × Velocity,
      f n ((t n,p.1),p.2) ≤ c n*ENNReal.ofReal L+iterate a (J n) (f n) 5 ((t n,p.1),p.2) ∧
      S.radius (E'.indices n) • p.1 ∈ TorusChart.cube ∧
      1/2 < S.boundedHotRatio (E'.indices n) ((t n,p.1),p.2) := by
    apply S.exists_central_cap_witness hs₀ hsmax hη hηmax hK hd₀.le hq₂ (E'.indices n)
    exact (hN (φ n) (Nat.le_add_left N n)).1 5 (t n) ⟨(ht n).1,le_rfl⟩
  choose p hp hcentral hlarge using hw
  let z := fun n => ((t n,(p n).1),(p n).2)
  have hgain := E'.zero_central_five_gain hMityagin hs₀ hsmax hη hηmax hK hα hγ hd₀ hdmax
    hq₁ hq₂ ha.1 (by norm_num : (0:ℝ) < 1) (by simpa only [ENNReal.ofReal_one] using E'.horizon_ge) hz z ht hcentral
  have hc : Tendsto c atTop (𝓝 (ENNReal.ofReal a)) := by
    have hh := S.positiveResidualConstant_tendsto hs₀ a B 1 0 E'.indices_strict
      (by
        have he : E'.fraction = 0 := hl
        simpa only [he] using E'.fraction_limit)
    simpa only [add_zero] using hh
  have hsum : Tendsto (fun n => c n*ENNReal.ofReal L+iterate a (J n) (f n) 5 (z n))
      atTop (𝓝 (ENNReal.ofReal a*ENNReal.ofReal L)) := by
    simpa only [add_zero] using
      (ENNReal.Tendsto.mul_const hc (Or.inr ENNReal.ofReal_ne_top)).add hgain
  have hle : ENNReal.ofReal (1/2:ℝ) ≤ ENNReal.ofReal a*ENNReal.ofReal L :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hsum (fun n =>
      (ENNReal.ofReal_le_ofReal (hlarge n).le).trans (hp n))
  rw [← ENNReal.ofReal_mul ha.1.le] at hle
  have hlt : ENNReal.ofReal (a*L) < ENNReal.ofReal (1/2:ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1/2)).mpr haSmall
  exact (not_lt_of_ge hle) hlt

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Five actual cap gains vanish at nonaxial endpoints below the limiting horizon -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.zero_nonaxial_five_gain (E : HotLimitExtraction S)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {a A R₀ b₀ X : ℝ}
    (ha : 0 < a) (hR₀ : 0 < R₀) (hb₀ : 0 < b₀)
    (hA : ENNReal.ofReal A < E.horizon)
    (hz : ∀ R, (E.hotLimit ∘ EuclideanFlight.hotChart)
      =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a A)
    (hposition : ∀ n, ‖WithLp.toLp 2 (states n).2.1‖ ≤ X)
    (hvelocity : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ velocityWindow R₀ b₀) :
    Tendsto (fun n => iterate a
      (positiveMainKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      (fun z => ENNReal.ofReal (S.boundedHotRatio (E.indices n) z)) 5 (toKinetic (states n)))
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
  have heq (n) : iterate a
      (selectedFreeKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      (g n) 5 (toKinetic (states n)) = iterate a
      (selectedFreeKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      (f n) 5 (toKinetic (states n)) := by
    have he (z : Published.KineticPhase) (hz : z.1.1 ∈ Icc a A) : g n z = f n z :=
      indicator_of_mem (show z ∈ D from ⟨ha.le.trans hz.1,hz.2⟩) _
    exact le_antisymm (iterate_slab_mono _ (fun z hz => (he z hz).le) 5 _ (htime n))
      (iterate_slab_mono _ (fun z hz => (he z hz).ge) 5 _ (htime n))
  have ht' := ht.congr' (Eventually.of_forall heq)
  have ht'' : Tendsto (fun n => (2:ℝ≥0∞)^5*iterate a
      (selectedFreeKernel (S.radius (E.indices n)) s₀ η K α γ d₀ q (F.indices (E.indices n)))
      (f n) 5 (toKinetic (states n))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht'
      (Or.inr (by norm_num : (2:ℝ≥0∞)^5 ≠ ∞))
  apply ht''.congr'
  exact Eventually.of_forall (fun n => (congrFun
    (iterate_add_self a _ (hf n) 5) (toKinetic (states n))).symm)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual dilated hot limit is nonzero -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.nonvanishing (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ¬(∀ A > 0, A < 1 → ∀ R,
      E.hotLimit ∘ EuclideanFlight.hotChart =ᵐ[(EuclideanFlight.hotBaseVolume A R).prod volume] 0) := by
  by_cases hl : E.fraction = 0
  · exact E.zero_fraction_nonvanishing hcarleman hMityagin hs₀ hsmax hη hηmax hK hα hαmax
      hγ hd₀ hdmax hsmall hq₁ hq₂ hl
  · exact E.positive_fraction_nonvanishing hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hdmax hsmall hq₁ hq₂ (lt_of_le_of_ne E.fraction_mem.1 (Ne.symm hl))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual nonzero hot limit supplies a bounded nonaxial time-slice seed -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.occupation_ne_zero_of_nonvanishing (E : HotLimitExtraction S)
    (hnv : ¬(∀ A > 0, A < 1 → ∀ R,
      E.hotLimit ∘ hotChart =ᵐ[(hotBaseVolume A R).prod volume] 0)) :
    (positiveDensityMeasure volume (E.hotLimit ∘ hotCharacteristicEquiv)).restrict
      (Prod.fst ⁻¹' Ioc (0:ℝ) 1) ≠ 0 := by
  intro hz
  have hs : MeasurableSet (Prod.fst ⁻¹' Ioc (0:ℝ) 1 : Set CharacteristicPhase) :=
    measurable_fst measurableSet_Ioc
  have hF : Measurable (E.hotLimit ∘ hotCharacteristicEquiv) :=
    E.hotLimit_measurable.comp hotCharacteristicEquiv.measurable
  unfold positiveDensityMeasure at hz
  rw [restrict_withDensity hs] at hz
  have hd := (withDensity_eq_zero_iff hF.ennreal_ofReal.aemeasurable).mp hz
  have hc : ∀ᵐ u : CharacteristicPhase ∂volume,
      u.1 ∈ Ioc (0:ℝ) 1 → E.hotLimit (hotCharacteristicEquiv u) = 0 := by
    have hzero : ∀ᵐ u ∂volume.restrict (Prod.fst ⁻¹' Ioc (0:ℝ) 1),
        E.hotLimit (hotCharacteristicEquiv u) = 0 := by
      filter_upwards [hd] with u hu
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp hu) (E.hotLimit_nonneg _)
    exact (ae_restrict_iff' hs).mp hzero
  have hpull := hotCharacteristic_measurePreserving.symm.quasiMeasurePreserving.ae hc
  have hphysical : ∀ᵐ z : HotKineticPhase ∂volume,
      z.1.1 ∈ Ioc (0:ℝ) 1 → E.hotLimit z = 0 := by
    filter_upwards [hpull] with z hz
    intro ht
    have he : (hotCharacteristicEquiv.symm z).1 = z.1.1 := rfl
    simpa only [MeasurableEquiv.apply_symm_apply] using hz (he ▸ ht)
  have htime : ∀ᵐ z : HotKineticPhase ∂volume, z.1.1 ≠ 0 := by
    have hchar : ∀ᵐ u : CharacteristicPhase ∂volume, u.1 ≠ 0 := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae (volume.ae_ne (0:ℝ))
    exact hotCharacteristic_measurePreserving.symm.quasiMeasurePreserving.ae hchar
  apply hnv
  intro A _hA hA1 R
  have hvol : hotWindowVolume A R ≤ volume := by
    rw [hotWindowVolume_eq]
    exact Measure.restrict_le_self
  have hw : E.hotLimit =ᵐ[hotWindowVolume A R] 0 := by
    have hm : ∀ᵐ z ∂hotWindowVolume A R, z ∈ hotWindowSet A R := by
      rw [hotWindowVolume_eq]
      exact ae_restrict_mem (hotWindowSet_measurable A R)
    filter_upwards [hphysical.filter_mono (ae_mono hvol),htime.filter_mono (ae_mono hvol),hm]
      with z hz ht0 hzw
    exact hz ⟨lt_of_le_of_ne hzw.1.1.1 (Ne.symm ht0),hzw.1.1.2.trans hA1.le⟩
  exact (hotChart_measurePreserving A R).quasiMeasurePreserving.ae hw

theorem HotLimitExtraction.exists_positive_seed (E : HotLimitExtraction S)
    (hcarleman : Published.GPV2009CarlemanInput)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G) :
    ∃ t ∈ Ioc (0:ℝ) 1, t ∈ G ∧ ∃ n : ℕ,
      0 < WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) t (seedPortion n) := by
  apply WeakTime.exists_positive_seed_slice
    (E.hotLimit_measurable.comp hotCharacteristicEquiv.measurable) 0 1
  · exact E.occupation_ne_zero_of_nonvanishing
      (E.nonvanishing hcarleman hMityagin hs₀ hsmax hη hηmax hK hα hαmax hγ
        hd₀ hdmax hsmall hq₁ hq₂)
  · exact hG

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # One bounded nonaxial seed survives at almost every later finite time -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.persisting_seed (E : HotPairExtraction S)
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hU : E.horizon = ⊤) :
    ∃ s ∈ Ioc (0:ℝ) 1, ∃ n : ℕ, ∀ᵐ t ∂volume, s ≤ t →
      0 < WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) t (seedPortion n) := by
  let start (m : ℕ) : ℝ := 1/((m : ℝ)+2)
  have hstart (m : ℕ) : 0 < start m ∧ start m ≤ 1 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    exact ⟨by dsimp [start]; positivity,
      (div_le_iff₀ (show 0 < (m : ℝ)+2 by positivity)).mpr (by linarith)⟩
  have hsurvival (n m N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo (start m) ((N : ℝ)+2) → t ∈ Ioo (start m) ((N : ℝ)+2) → s ≤ t →
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) t := by
    apply E.characteristic_free_flight_survival hDP hcarleman hGLPS
      hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ (hstart m).1
      (B := (N : ℝ)+3)
    · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith [(hstart m).2]
    · linarith
    · rw [hU]
      exact ENNReal.ofReal_lt_top
    · exact seedPhaseCutoff_smooth n
    · exact seedPhaseCutoff_compact n
    · exact fun p => (seedPhaseCutoff_mem n p).1
  choose C hC htrace using hsurvival
  have hgood : ∀ᵐ s ∂volume, ∀ n m N : ℕ, ∀ᵐ t ∂volume,
      s ∈ Ioo (start m) ((N : ℝ)+2) → t ∈ Ioo (start m) ((N : ℝ)+2) → s ≤ t →
      ENNReal.ofReal (Real.exp (C n m N*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) t :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun m => ae_all_iff.mpr fun N => htrace n m N
  obtain ⟨s,hs,hsg,n,hn⟩ := E.toHotLimitExtraction.exists_positive_seed hcarleman hMityagin
    hs₀ hsmax hη hηmax hK hα (hαmax.trans (by norm_num)) hγ hd₀ hdmax hsmall hq₁ hq₂ hgood
  obtain ⟨m,hm⟩ := exists_nat_gt (1/s)
  have hms : start m < s := by
    have hm' := (div_lt_iff₀ hs.1).mp hm
    apply (div_lt_iff₀ (show 0 < (m : ℝ)+2 by positivity)).mpr
    nlinarith [hs.1]
  refine ⟨s,hs,n,?_⟩
  filter_upwards [ae_all_iff.mpr (fun N => hsg n m N)] with t ht
  intro hst
  obtain ⟨N,hN⟩ := exists_nat_gt t
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hi := ht N ⟨hms,by linarith [hs.2]⟩ ⟨hms.trans_le hst,by linarith⟩ hst
  have hle := hi.trans (phaseSlice_weight_le
    (fun z => E.toHotLimitExtraction.hotLimit_nonneg (hotCharacteristicEquiv z))
    (fun p => (seedPhaseCutoff_mem n p).2) t)
  have hh := hle (seedPortion n)
  rw [Measure.smul_apply,smul_eq_mul,phaseSlice_weight_apply_eq (seedPortion_measurable n)
    (fun p hp => seedPhaseCutoff_one hp)] at hh
  have hp : 0 < ENNReal.ofReal (Real.exp (C n m N*(s-t)))*
      WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) s (seedPortion n) :=
    pos_iff_ne_zero.mpr (mul_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) (ne_of_gt hn))
  exact hp.trans_le hh

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual hot-limit survival along free characteristics, without a spatial cutoff -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.free_characteristic_survival
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      Real.exp (C*(s-t))*(∫ p, φ p*E.hotLimit (hotCharacteristicEquiv (s,p))) ≤
        ∫ p, φ p*E.hotLimit (hotCharacteristicEquiv (t,p)) := by
  have hA := (ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB
  obtain ⟨C,hC,hbound⟩ := E.toHotLimitExtraction.characteristic_loss_projection_bound
    hs₀ ha haA.le hA hK hα hγ hq₂ hφ.continuous hc hn
  obtain ⟨R,_,hcover,hweak⟩ := E.characteristic_weak_time_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hφ hc hn
  let μ := E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R
  let _ := E.toHotLimitExtraction.incomingGainMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  have : IsFiniteMeasure μ := by dsimp [μ,HotLimitExtraction.characteristicGainMeasure]; infer_instance
  obtain ⟨D,hD⟩ := hφ.continuous.bounded_above_of_compact_support hc
  let _ := WeakTime.timeSource_finite μ hφ.continuous.measurable hn hD
  have hsurv := WeakTime.ae_survival_of_weak_balance haA hC
    (WeakTime.phaseProjection_integrable
      (cylinderPullback_integrable
        (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le hA R).2.1)
      hφ.continuous.measurable hD)
    (WeakTime.phaseProjection_integrable
      (E.toHotLimitExtraction.characteristicLossDensity_integrable ha haA.le hK hα hγ hq₂)
      hφ.continuous.measurable hD)
    (WeakTime.timeSource μ φ) ((hbound R).mono (fun _ ht _ => ht)) hweak

  refine ⟨C,hC,?_⟩
  have heq (t : ℝ) (ht : t ∈ Ioo a A) :
      WeakTime.phaseProjection (cylinderPullback a A R E.hotLimit) φ t =
        ∫ p, φ p*E.hotLimit (hotCharacteristicEquiv (t,p)) :=
    cylinder_phase_integral_eq (hcover t ⟨ht.1.le,ht.2.le⟩)
  filter_upwards [hsurv] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst
  have h := ht hsa hta hst
  rw [heq s hsa,heq t hta] at h
  exact h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual gain and self-retention source is a positive collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.retainedKernel (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (C : ℝ) (β : WeakTime.Phase → ℝ) : Kernel CharacteristicPhase CharacteristicPhase :=
  positiveSourceKernel (E.characteristicGainKernel ha hK hα hγ)
    (fun z => β z.2) (fun z => C-E.characteristicSlabFrequency a z)

instance HotLimitExtraction.retainedKernel_sFinite (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (C : ℝ) (β : WeakTime.Phase → ℝ) :
    IsSFiniteKernel (E.retainedKernel ha hK hα hγ C β) := by
  unfold HotLimitExtraction.retainedKernel
  infer_instance

theorem HotLimitExtraction.retainedSource_eq_kernel (E : HotLimitExtraction S)
    {a A R C : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    {β : WeakTime.Phase → ℝ} (hβ : Measurable β) :
    E.retainedSource ha hK hα hγ A R C β =
      E.retainedKernel ha hK hα hγ C β ∘ₘ
        positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit) := by
  have hF : Measurable (cylinderPullback a A R E.hotLimit) :=
    (E.hotLimit_measurable.indicator (coldCylinderSet_measurable a A R)).comp
      hotCharacteristicEquiv.measurable
  have hn (z : CharacteristicPhase) : 0 ≤ cylinderPullback a A R E.hotLimit z :=
    indicator_nonneg (fun x _ => E.hotLimit_nonneg x) _
  rw [HotLimitExtraction.retainedKernel,positiveSourceKernel_comp_density _ _
    (b := fun z => β z.2) (r := fun z => C-E.characteristicSlabFrequency a z) hF hn
    (hβ.comp measurable_snd)
    (measurable_const.sub (E.characteristicSlabFrequency_measurable ha hK hα.le hγ.le))]
  unfold HotLimitExtraction.retainedSource WeakTime.weightedPhaseSource
  congr 1
  congr 1
  funext z
  rw [WeakTime.phaseWeight,WeakTime.phaseWeight,E.characteristicLossDensity_slab_factor]
  ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual retained source equals the active normal-angle beam source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicSlabFrequency_eq_beam
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (z : CharacteristicPhase)
    (ht : a ≤ z.1)
    (hactive : GeometricBackground.active E.phase η E.fraction
      (transverse (z.2.1+z.1 • z.2.2))) :
    E.characteristicSlabFrequency a z = (K/(4*r))*characteristicBeamFrequency
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
        hα.le hγ.le η r) z := by
  change GeometricBackground.frequency E.phase η E.fraction K α γ
    (max a z.1) (spaceEquiv (z.2.1+z.1 • z.2.2)) z.2.2 = _
  rw [max_eq_right ht,spaceEquiv_apply]
  exact GeometricBackground.frequency_eq_beamFrequency (zero_lt_one.trans_le E.phase_mem.1)
    hK hα.le hγ.le hr (ha.le.trans ht) η E.fraction _ _ hactive

theorem HotLimitExtraction.retainedKernel_eq_normal_beam
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (C : ℝ) (z : CharacteristicPhase)
    (ht : a ≤ z.1)
    (hactive : GeometricBackground.active E.phase η E.fraction
      (transverse (z.2.1+z.1 • z.2.2))) :
    E.retainedKernel ha hK hα hγ C (fun _ => 1) z =
      beamNormalRetainedKernel
        (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
          hα.le hγ.le η r) (K/(4*r)) C z := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [HotLimitExtraction.retainedKernel,positiveSourceKernel_one_lintegral _
    (r := fun u => C-E.characteristicSlabFrequency a u)
    (measurable_const.sub (E.characteristicSlabFrequency_measurable ha hK hα.le hγ.le)) z hf,
    beamNormalRetainedKernel_lintegral _ _ _ z hf,
    E.characteristicGainKernel_eq_normal_beam ha hr hK hα hγ z ht hactive,
    lintegral_smul_measure,smul_eq_mul,
    E.characteristicSlabFrequency_eq_beam ha hr hK hα hγ z ht hactive]

theorem HotLimitExtraction.retainedKernel_eq_normal_beam_ae
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (C : ℝ) :
    ∀ᵐ z : CharacteristicPhase ∂volume, a ≤ z.1 →
      0 < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      Real.exp η*E.fraction < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      E.retainedKernel ha hK hα hγ C (fun _ => 1) z =
        beamNormalRetainedKernel
          (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
            hα.le hγ.le η r) (K/(4*r)) C z := by
  filter_upwards [GeometricBackground.active_ae_characteristic
    (zero_lt_one.trans_le E.phase_mem.1) hη E.fraction] with z hz ht hp hc
  exact E.retainedKernel_eq_normal_beam ha hr hK hα hγ C z ht (hz hp hc)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Localized hot occupation supplies a positive retained collision source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.localizedOccupation_le (E : HotLimitExtraction S)
    (a A R : ℝ) {β : WeakTime.Phase → ℝ} (hβ : ∀ p, β p ≤ 1) :
    positiveDensityMeasure volume (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) ≤
      positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit) := by
  apply withDensity_mono
  apply ae_of_all
  intro z
  apply ENNReal.ofReal_le_ofReal
  have hn : 0 ≤ cylinderPullback a A R E.hotLimit z :=
    indicator_nonneg (fun x _ => E.hotLimit_nonneg x) _
  exact (mul_le_mul_of_nonneg_right (hβ z.2) hn).trans_eq (one_mul _)

theorem HotLimitExtraction.retainedSource_dominates_localized (E : HotLimitExtraction S)
    {a A R C : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    {β : WeakTime.Phase → ℝ} (hβ : Measurable β) (hβ₁ : ∀ p, β p ≤ 1) :
    E.retainedKernel ha hK hα hγ C β ∘ₘ
      positiveDensityMeasure volume (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) ≤
        E.retainedSource ha hK hα hγ A R C β := by
  rw [E.retainedSource_eq_kernel ha hK hα hγ hβ]
  exact PositiveMeasureHistories.comp_mono_measure _ (E.localizedOccupation_le a A R hβ₁)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot density reaches bounded regions beyond the cold hole -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.escaping_seed (E : HotPairExtraction S)
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hU : E.horizon = ⊤) :
    ∃ n : ℕ, ∀ L : ℝ, ∃ T : ℝ, 0 < T ∧ ∀ᵐ t ∂volume, T ≤ t →
      0 < (WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) t).map (flight t)
        (seedEscapeRegion n L t) := by
  obtain ⟨s,_hs,n,hseed⟩ := E.persisting_seed hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hU
  exact ⟨n,seed_mass_escapes _ hseed⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
