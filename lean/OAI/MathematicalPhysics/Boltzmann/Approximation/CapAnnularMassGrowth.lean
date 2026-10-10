import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLimitTransport
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapCoveredDamping
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapEscapingSeed
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveEndpointHistory
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.AeKernelHistoryOrder
import OAI.MathematicalPhysics.Boltzmann.Branching.AeLocalizedHotMassGrowth
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedEntryPortion
import OAI.MathematicalPhysics.Boltzmann.Branching.CommonStartGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.HotRatioCollisionTrace
import OAI.MathematicalPhysics.Boltzmann.Branching.LateBoxAccessMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseSliceLocalization
import OAI.MathematicalPhysics.Boltzmann.Branching.SeedEscapeMeasure
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteEntryPhaseBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedHotMassGrowth
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularCharacteristicCutoff
import OAI.MathematicalPhysics.Boltzmann.Jets.AnnularEnvelopes
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricLocalizedEntry

namespace OAI

section

/-! # The actual hot occupation measure satisfies the positive renewal equation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_occupation_equation
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C b : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C) (hb : b < A)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, s ∈ Ioo a b →
      (positiveDensityMeasure volume (WeakTime.phaseWeight β
        (cylinderPullback a A R E.hotLimit))).restrict (Prod.fst ⁻¹' Ioc s b) =
      WeakTime.residenceKernel C b ∘ₘ
        (WeakTime.phaseSeed s (WeakTime.phaseSlice
          (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)+
          (E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β).restrict
            (Prod.fst ⁻¹' Ioc s b)) := by
  obtain ⟨R,hR,hbalance⟩ := E.characteristic_combined_source_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  have hF : Measurable (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) :=
    (hβ.continuous.measurable.comp measurable_snd).mul
      ((E.toHotLimitExtraction.hotLimit_measurable.indicator
        (coldCylinderSet_measurable a A R)).comp hotCharacteristicEquiv.measurable)
  let _ : SFinite (E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β) := by
    rw [E.toHotLimitExtraction.retainedSource_eq_kernel ha hK hα hγ hβ.continuous.measurable]
    unfold positiveDensityMeasure
    infer_instance
  refine ⟨R,hR,?_⟩
  filter_upwards [hbalance] with s hs
  intro hsa
  let _ : SFinite (WeakTime.phaseSlice
      (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s) := by
    unfold WeakTime.phaseSlice positiveDensityMeasure
    infer_instance
  apply WeakTime.occupation_eq_residence hF _ _ hsa.1 hb
  filter_upwards [hs] with t ht
  intro hst
  exact ht ⟨hsa.1,hsa.2.trans hb⟩ ⟨hsa.1.trans hst.1,hst.2.trans_lt hb⟩ hst.1.le

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Every finite positive collision history is dominated by the actual hot occupation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.localHistoryKernel (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (C s b : ℝ) (β : WeakTime.Phase → ℝ) : Kernel CharacteristicPhase CharacteristicPhase :=
  ((E.retainedKernel ha hK hα hγ C β).restrict
    (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s b))) ∘ₖ WeakTime.residenceKernel C b

theorem HotPairExtraction.characteristic_finite_occupation_histories
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C b : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C) (hb : b < A)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, s ∈ Ioo a b → ∀ n : ℕ,
      WeakTime.residenceKernel C b ∘ₘ
        (∑ j ∈ Finset.range n,
          ((E.toHotLimitExtraction.localHistoryKernel ha hK hα hγ C s b β)^j) ∘ₘ
            WeakTime.phaseSeed s (WeakTime.phaseSlice
              (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)) ≤
      (positiveDensityMeasure volume (WeakTime.phaseWeight β
        (cylinderPullback a A R E.hotLimit))).restrict (Prod.fst ⁻¹' Ioc s b) := by
  obtain ⟨R,hR,heq⟩ := E.characteristic_occupation_equation hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hb hβ hβc hβn hfrequency
  refine ⟨R,hR,?_⟩
  filter_upwards [heq] with s hs
  intro hsa n
  exact PositiveMeasureHistories.finite_occupation_histories
    (E.toHotLimitExtraction.retainedKernel ha hK hα hγ C β) (WeakTime.residenceKernel C b)
    (measurable_fst measurableSet_Ioc) (hs hsa)
    (E.toHotLimitExtraction.retainedSource_dominates_localized ha hK hα hγ
      hβ.continuous.measurable hβ₁) n

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual hot time slices dominate every finite positive collision history -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_finite_endpoint_histories
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
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t → ∀ n : ℕ,
      WeakTime.phaseEndpointKernel C t ∘ₘ
        (∑ j ∈ Finset.range n,
          ((E.toHotLimitExtraction.localHistoryKernel ha hK hα hγ C s t β)^j) ∘ₘ
            WeakTime.phaseSeed s (WeakTime.phaseSlice
              (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)) ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t := by
  obtain ⟨R,hR,hbalance⟩ := E.characteristic_combined_source_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  let Fh := WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)
  let J := E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β
  have hF : Measurable Fh := (hβ.continuous.measurable.comp measurable_snd).mul
    ((E.toHotLimitExtraction.hotLimit_measurable.indicator
      (coldCylinderSet_measurable a A R)).comp hotCharacteristicEquiv.measurable)
  let _ : SFinite J := by
    dsimp [J]
    rw [E.toHotLimitExtraction.retainedSource_eq_kernel ha hK hα hγ hβ.continuous.measurable]
    unfold positiveDensityMeasure
    infer_instance
  refine ⟨R,hR,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst n
  let _ : SFinite (WeakTime.phaseSlice Fh s) := by
    unfold WeakTime.phaseSlice positiveDensityMeasure
    infer_instance
  have hocc : (positiveDensityMeasure volume Fh).restrict (Prod.fst ⁻¹' Ioc s t) =
      WeakTime.residenceKernel C t ∘ₘ
        (WeakTime.phaseSeed s (WeakTime.phaseSlice Fh s)+J.restrict (Prod.fst ⁻¹' Ioc s t)) := by
    apply WeakTime.occupation_eq_residence hF _ J hsa.1 hta.2
    filter_upwards [hs] with r hr
    intro hsr
    exact hr hsa ⟨hsa.1.trans hsr.1,hsr.2.trans_lt hta.2⟩ hsr.1.le
  exact WeakTime.endpoint_finite_histories
    (E.toHotLimitExtraction.retainedKernel ha hK hα hγ C β) (WeakTime.residenceKernel C t)
    (positiveDensityMeasure volume Fh) J (WeakTime.phaseSlice Fh s) (WeakTime.phaseSlice Fh t)
    hsa.1 hta.2 hocc
    (E.toHotLimitExtraction.retainedSource_dominates_localized ha hK hα hγ
      hβ.continuous.measurable hβ₁) (ht hsa hta hst) n

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot trace balances as localized phase measures -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_localized_measure_balance
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
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t+
        WeakTime.phaseIncrement (WeakTime.weightedPhaseSource
          (E.toHotLimitExtraction.characteristicLossMeasure ha hK hα hγ A R) β) s t =
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s+
        WeakTime.phaseIncrement (WeakTime.weightedPhaseSource
          (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) β) s t := by
  obtain ⟨R,hR,hweak⟩ := E.common_characteristic_weak_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hβc
  refine ⟨R,hR,?_⟩
  let μ := E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R
  let ν := E.toHotLimitExtraction.characteristicLossMeasure ha hK hα hγ A R
  let _ := E.toHotLimitExtraction.incomingGainMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  let _ := E.toHotLimitExtraction.incomingLossMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  have : IsFiniteMeasure μ := by dsimp [μ,HotLimitExtraction.characteristicGainMeasure]; infer_instance
  have : IsFiniteMeasure ν := by dsimp [ν,HotLimitExtraction.characteristicLossMeasure]; infer_instance
  have hi := (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le
    ((ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB) R).2.1
  have hn : ∀ᵐ z ∂volume, 0 ≤ cylinderPullback a A R E.hotLimit z := by
    apply ae_of_all
    intro z
    change 0 ≤ (coldCylinderSet a A R).indicator E.hotLimit (hotCharacteristicEquiv z)
    exact indicator_nonneg (fun p _ => E.toHotLimitExtraction.hotLimit_nonneg p) _
  apply WeakTime.ae_localized_measure_interval_balance haA (cylinderPullback_integrable hi)
    hn μ ν hβ hβc hβn
  exact hweak

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Local normal-angle beam histories lie below the actual hot source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.localizedNormalBeam_le_retained_ae
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (C : ℝ)
    {β : WeakTime.Phase → ℝ} (hβ : Measurable β)
    {B : Set CharacteristicPhase} (hB : MeasurableSet B)
    (hcore : ∀ z ∈ B, β z.2 = 1) :
    ∀ᵐ z ∂volume, localizedNormalBeamKernel
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
        hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hB z ≤
      E.retainedKernel ha hK hα hγ C β z := by
  classical
  have hle := positiveSourceKernel_restrict_le (E.characteristicGainKernel ha hK hα hγ)
    (b := fun z => β z.2) (r := fun z => C-E.characteristicSlabFrequency a z)
    (hβ.comp measurable_snd)
    (measurable_const.sub (E.characteristicSlabFrequency_measurable ha hK hα.le hγ.le))
    hB hcore
  filter_upwards [E.retainedKernel_eq_normal_beam_ae ha hr hη hK hα hγ C] with z hz
  unfold localizedNormalBeamKernel
  rw [Kernel.piecewise_apply]
  by_cases hd : z ∈ coldCharacteristicDomain a η E.fraction
  · rw [ite_eq_left hd,Kernel.restrict_apply,
      ← hz hd.1 hd.2.1 hd.2.2,← Kernel.restrict_apply]
    exact hle z
  · rw [ite_eq_right hd]
    exact bot_le

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual hot time slices dominate almost-everywhere smaller collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_comparison_endpoint_histories
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
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    (Jc : Kernel CharacteristicPhase CharacteristicPhase)
    (hJc : ∀ᵐ z ∂volume, Jc z ≤ E.toHotLimitExtraction.retainedKernel ha hK hα hγ C β z) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t → ∀ n : ℕ,
      WeakTime.phaseEndpointKernel C t ∘ₘ
        (∑ j ∈ Finset.range n,
          ((((Jc.restrict (measurable_fst measurableSet_Ioc :
            MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ WeakTime.residenceKernel C t)^j)) ∘ₘ
            WeakTime.phaseSeed s (WeakTime.phaseSlice
              (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)) ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t := by
  obtain ⟨R,hR,hbalance⟩ := E.characteristic_combined_source_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  let Fh := WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)
  let J := E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β
  have hF : Measurable Fh := (hβ.continuous.measurable.comp measurable_snd).mul
    ((E.toHotLimitExtraction.hotLimit_measurable.indicator
      (coldCylinderSet_measurable a A R)).comp hotCharacteristicEquiv.measurable)
  let _ : SFinite J := by
    dsimp [J]
    rw [E.toHotLimitExtraction.retainedSource_eq_kernel ha hK hα hγ hβ.continuous.measurable]
    unfold positiveDensityMeasure
    infer_instance
  have hcomp : Jc ∘ₘ positiveDensityMeasure volume Fh ≤
      E.toHotLimitExtraction.retainedKernel ha hK hα hγ C β ∘ₘ
        positiveDensityMeasure volume Fh := by
    apply KernelHistoryOrder.measure_comp_mono_ae _ le_rfl
    exact (withDensity_absolutelyContinuous volume _).ae_le hJc
  have hsource : Jc ∘ₘ positiveDensityMeasure volume Fh ≤ J := hcomp.trans
    (E.toHotLimitExtraction.retainedSource_dominates_localized ha hK hα hγ
      hβ.continuous.measurable hβ₁)
  refine ⟨R,hR,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst n
  let _ : SFinite (WeakTime.phaseSlice Fh s) := by
    unfold WeakTime.phaseSlice positiveDensityMeasure
    infer_instance
  have hocc : (positiveDensityMeasure volume Fh).restrict (Prod.fst ⁻¹' Ioc s t) =
      WeakTime.residenceKernel C t ∘ₘ
        (WeakTime.phaseSeed s (WeakTime.phaseSlice Fh s)+J.restrict (Prod.fst ⁻¹' Ioc s t)) := by
    apply WeakTime.occupation_eq_residence hF _ J hsa.1 hta.2
    filter_upwards [hs] with r hr
    intro hsr
    exact hr hsa ⟨hsa.1.trans hsr.1,hsr.2.trans_lt hta.2⟩ hsr.1.le
  exact WeakTime.endpoint_finite_histories
    Jc (WeakTime.residenceKernel C t)
    (positiveDensityMeasure volume Fh) J (WeakTime.phaseSlice Fh s) (WeakTime.phaseSlice Fh t)
    hsa.1 hta.2 hocc
    hsource (ht hsa hta hst) n

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Retaining full support coverage in the finite positive endpoint histories -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_comparison_endpoint_histories
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
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    (Jc : Kernel CharacteristicPhase CharacteristicPhase)
    (hJc : ∀ᵐ z ∂volume, Jc z ≤ E.toHotLimitExtraction.retainedKernel ha hK hα hγ C β z) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t → ∀ n : ℕ,
      WeakTime.phaseEndpointKernel C t ∘ₘ
        (∑ j ∈ Finset.range n,
          ((((Jc.restrict (measurable_fst measurableSet_Ioc :
            MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ WeakTime.residenceKernel C t)^j)) ∘ₘ
            WeakTime.phaseSeed s (WeakTime.phaseSlice
              (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)) ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t := by
  obtain ⟨R,hR,hcover,hbalance⟩ := E.covered_characteristic_combined_source_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  let Fh := WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)
  let J := E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β
  have hF : Measurable Fh := (hβ.continuous.measurable.comp measurable_snd).mul
    ((E.toHotLimitExtraction.hotLimit_measurable.indicator
      (coldCylinderSet_measurable a A R)).comp hotCharacteristicEquiv.measurable)
  let _ : SFinite J := by
    dsimp [J]
    rw [E.toHotLimitExtraction.retainedSource_eq_kernel ha hK hα hγ hβ.continuous.measurable]
    unfold positiveDensityMeasure
    infer_instance
  have hcomp : Jc ∘ₘ positiveDensityMeasure volume Fh ≤
      E.toHotLimitExtraction.retainedKernel ha hK hα hγ C β ∘ₘ
        positiveDensityMeasure volume Fh := by
    apply KernelHistoryOrder.measure_comp_mono_ae _ le_rfl
    exact (withDensity_absolutelyContinuous volume _).ae_le hJc
  have hsource : Jc ∘ₘ positiveDensityMeasure volume Fh ≤ J := hcomp.trans
    (E.toHotLimitExtraction.retainedSource_dominates_localized ha hK hα hγ
      hβ.continuous.measurable hβ₁)
  refine ⟨R,hR,hcover,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst n
  let _ : SFinite (WeakTime.phaseSlice Fh s) := by
    unfold WeakTime.phaseSlice positiveDensityMeasure
    infer_instance
  have hocc : (positiveDensityMeasure volume Fh).restrict (Prod.fst ⁻¹' Ioc s t) =
      WeakTime.residenceKernel C t ∘ₘ
        (WeakTime.phaseSeed s (WeakTime.phaseSlice Fh s)+J.restrict (Prod.fst ⁻¹' Ioc s t)) := by
    apply WeakTime.occupation_eq_residence hF _ J hsa.1 hta.2
    filter_upwards [hs] with r hr
    intro hsr
    exact hr hsa ⟨hsa.1.trans hsr.1,hsr.2.trans_lt hta.2⟩ hsr.1.le
  exact WeakTime.endpoint_finite_histories
    Jc (WeakTime.residenceKernel C t)
    (positiveDensityMeasure volume Fh) J (WeakTime.phaseSlice Fh s) (WeakTime.phaseSlice Fh t)
    hsa.1 hta.2 hocc
    hsource (ht hsa hta hst) n

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual hot time slices dominate the localized atomic normal-angle histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.localized_normal_endpoint_histories
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
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    {r : ℝ} (hr : 0 < r) {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hcore : ∀ z ∈ Ω, β z.2 = 1) :
    let Jc := localizedNormalBeamKernel
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
        hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hΩ;
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t → ∀ n : ℕ,
      WeakTime.phaseEndpointKernel C t ∘ₘ
        (∑ j ∈ Finset.range n,
          ((((Jc.restrict (measurable_fst measurableSet_Ioc :
            MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ WeakTime.residenceKernel C t)^j)) ∘ₘ
            WeakTime.phaseSeed s (WeakTime.phaseSlice
              (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)) ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t := by
  exact E.characteristic_comparison_endpoint_histories hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hβ₁ hfrequency _
    (E.toHotLimitExtraction.localizedNormalBeam_le_retained_ae ha hr hη hK hα hγ C
      hβ.continuous.measurable hΩ hcore)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual unlocalized hot box mass has a finite fourth-power cap -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotLateBoxMass_cap (E : HotLimitExtraction S)
    {κ d : ℝ} (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hq : q < 2) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      hotLateBoxMass E.hotLimit κ d t ≤ ENNReal.ofReal (lateBoxCapConstant q κ d*(1+t)^4) := by
  have hg : ∀ᵐ u : CharacteristicPhase ∂volume, 0 ≤ u.1 →
      E.hotLimit (hotCharacteristicEquiv u) ≤ (u.1+E.fraction)*H q u.2.2 :=
    hotCharacteristic_measurePreserving.quasiMeasurePreserving.ae E.hotLimit_cap_global
  rw [Measure.volume_eq_prod] at hg
  filter_upwards [Measure.ae_ae_of_ae_prod hg] with t ht
  intro ht0
  apply density_movingBox_bound hq hκ hd ht0
  · exact E.hotLimit_measurable.comp
      (hotCharacteristicEquiv.measurable.comp (measurable_const.prodMk measurable_id))
  · filter_upwards [ht] with p hp
    exact (hp ht0).trans (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl E.fraction_mem.2) (H_nonneg q p.2))

theorem HotLimitExtraction.hotLateBoxMass_finite (E : HotLimitExtraction S)
    {κ d : ℝ} (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hq : q < 2) :
    ∀ᵐ t ∂volume, 0 ≤ t → hotLateBoxMass E.hotLimit κ d t ≠ ⊤ := by
  filter_upwards [E.hotLateBoxMass_cap hκ hd hq] with t ht
  intro ht0
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (ht ht0)

theorem HotLimitExtraction.hotLateBoxMass_real_cap (E : HotLimitExtraction S)
    {κ d : ℝ} (hκ : 0 ≤ κ) (hd : 0 ≤ d) (hq : q < 2) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (hotLateBoxMass E.hotLimit κ d t).toReal ≤ lateBoxCapConstant q κ d*(1+t)^4 := by
  filter_upwards [E.hotLateBoxMass_cap hκ hd hq] with t ht
  intro ht0
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (ht ht0)
  rwa [ENNReal.toReal_ofReal (mul_nonneg (lateBoxCapConstant_nonneg hκ hd) (by positivity))] at hh

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Retaining full support coverage in the finite positive endpoint histories -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_normal_endpoint_histories
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
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    {r : ℝ} (hr : 0 < r) {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hcore : ∀ z ∈ Ω, β z.2 = 1) :
    let Jc := localizedNormalBeamKernel
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
        hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hΩ;
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t → ∀ n : ℕ,
      WeakTime.phaseEndpointKernel C t ∘ₘ
        (∑ j ∈ Finset.range n,
          ((((Jc.restrict (measurable_fst measurableSet_Ioc :
            MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ WeakTime.residenceKernel C t)^j)) ∘ₘ
            WeakTime.phaseSeed s (WeakTime.phaseSlice
              (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)) ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t := by
  exact E.covered_comparison_endpoint_histories hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hβ₁ hfrequency _
    (E.toHotLimitExtraction.localizedNormalBeam_le_retained_ae ha hr hη hK hα hγ C
      hβ.continuous.measurable hΩ hcore)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A positive finite localized history produces positive actual hot mass -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.positive_history_transfer
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a U V C r : ℝ} (ha : 0 < a) (haU : a < U) (hUV : U < V)
    (hV : ENNReal.ofReal V < E.horizon) (hC : 0 ≤ C) (hr : 0 < r)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a U → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω) (hcore : ∀ z ∈ Ω, β z.2 = 1)
    (A B : ℝ → Set WeakTime.Phase) (hA : ∀ t, MeasurableSet (A t))
    (hB : ∀ s, MeasurableSet (B s))
    (hstart : ∀ s ∈ Ioo a U, ∀ p ∈ B s, β p = 1)
    (N : ℕ) (P : ℝ → ℝ → Prop)
    (horder : ∀ s ∈ Ioo a U, ∀ t ∈ Ioo a U, P s t → s ≤ t)
    (hpoint : ∀ s ∈ Ioo a U, ∀ t ∈ Ioo a U, P s t → ∀ p ∈ B s,
      0 < (WeakTime.phaseEndpointKernel C t ∘ₖ
        ((((localizedNormalBeamKernel
          (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
            hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ
            WeakTime.residenceKernel C t)^N)) (s,p) (A t)) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a U → t ∈ Ioo a U → P s t →
      0 < hotPhaseSlice E.hotLimit s (B s) → 0 < hotPhaseSlice E.hotLimit t (A t) := by
  obtain ⟨R,_hR,hcover,hist⟩ := E.covered_normal_endpoint_histories hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haU hUV hV hC hβ hβc hβn hβ₁ hfrequency hr hΩ hcore
  filter_upwards [hist] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hp hm
  apply covered_hot_positive_history E.toHotLimitExtraction.hotLimit_nonneg hβ₁
    a U R s t (hA t) (hB s) (hstart s hsa) (hcover s ⟨hsa.1.le,hsa.2.le⟩)
    _ C N hm (ht hsa hta (horder s hsa t hta hp) (N+1))
  exact hpoint s hsa t hta hp

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Three actual collisions transfer any escaped hot seed into the entry velocities -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.entry_window
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {κ ρ ε a U V : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (ha : 0 < a) (haU : a < U) (hUV : U < V) (hV : ENNReal.ofReal V < E.horizon)
    (n : ℕ) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a U → t ∈ Ioo a U →
      0 < t-s → ((n:ℝ)+6)*(t-s) ≤ 1 →
      0 < hotPhaseSlice E.hotLimit s
        (flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) →
      0 < hotPhaseSlice E.hotLimit t (flight t ⁻¹' velocityPhaseBall κ ρ) := by
  have hU : 0 < U := ha.trans haU
  have hl : 0 ≤ E.fraction := E.fraction_mem.1
  let X := (n:ℝ)*(1+U)
  let M := X+(2*U+1)*((n:ℝ)+6)
  obtain ⟨β,hβ,hβc,hβn,hβ₁,hβone⟩ := exists_phaseBall_cutoff M
  let Ω := phaseBallCore M
  have hΩ : MeasurableSet Ω := phaseBallCore_measurable M
  obtain ⟨C,hC,hfreq⟩ := E.toHotLimitExtraction.characteristic_frequency_compact_bound
    ha hK.le hα hγ hβc
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hxbound (s : ℝ) (hs : s ∈ Ioo a U) (p : WeakTime.Phase)
      (hp : p ∈ flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) :
      ‖(flight s p).1‖ ≤ X := by
    apply hp.2.1.trans
    exact mul_le_mul_of_nonneg_left (by linarith [hs.2] : 1+s ≤ 1+U) (Nat.cast_nonneg n)
  have hstart (s : ℝ) (hs : s ∈ Ioo a U) (p : WeakTime.Phase)
      (hp : p ∈ flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) : β p = 1 := by
    apply hβone
    have hb := finiteFlightCone_window_core (N := 3) (n := 3) (s := s) (t := s) (U := U)
      (ha.le.trans hs.1.le) hs.2.le (Nat.cast_nonneg n) hX (hxbound s hs p hp)
      (finiteFlightCone_initial (N := 3) (h := s-s) (by linarith)
        (flight s p).1 (flight s p).2 hp.2.2)
    norm_num only [Nat.cast_ofNat,sub_self,show (2:ℝ)*3=6 by norm_num] at hb
    have he := flightCharacteristic_from_phase s 0 p
    simp only [add_zero] at he
    change flightCharacteristicEquiv s (0,p.1+s • p.2,p.2) = (s,p) at he
    change flightCharacteristicEquiv s (0,p.1+s • p.2,p.2) ∈ phaseBallCore M at hb
    rw [he] at hb
    exact hb
  have hscale : K/(4*(K/4)) = (1:ℝ) := by field_simp
  have hCeq : ((Real.toNNReal C : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C hC
  have hh := E.positive_history_transfer hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK.le
    hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haU hUV hV hC
    (r := K/4) (by positivity) hβ hβc hβn hβ₁
    (fun u hu hp => hfreq u hu.1.le hp) hΩ (fun z hz => hβone z.2 hz)
    (fun t => flight t ⁻¹' velocityPhaseBall κ ρ)
    (fun s => flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s)
    (fun t => (flight_measurePreserving t).measurable (velocityPhaseBall_measurable κ ρ))
    (fun s => (flight_measurePreserving s).measurable (seedEscapeRegion_measurable n _ s))
    hstart 3 (fun s t => 0 < t-s ∧ ((n:ℝ)+6)*(t-s) ≤ 1)
    (fun s _ t _ h => by linarith [h.1]) (by
      intro s hs t ht hst p hp
      rw [hscale]
      have hcore : ∀ j ≤ 3, ∀ z, finiteFlightCone 3 j (t-s) (n:ℝ) (flight s p).1 z →
          flightCharacteristicEquiv (s+(t-s)) z ∈ Ω := by
        intro j _hj z hz
        have he : s+(t-s) = t := by ring
        rw [he]
        simpa only [Nat.cast_ofNat,show (2:ℝ)*3=6 by norm_num] using
          finiteFlightCone_window_core (ha.le.trans hs.1.le) ht.2.le
            (Nat.cast_nonneg n) hX (hxbound s hs p hp) hz
      have hl := GeometricBackground.localized_three_entry_positive
        (zero_lt_one.trans_le E.phase_mem.1) hη hα.le hγ.le (by positivity : 0 < K/4)
        hαε hε hεmax hκ hκmax hρ hερ hst.1
        (by positivity : 0 < Real.exp η*E.fraction+1) (Nat.cast_nonneg n)
        (ha.le.trans hs.1.le) hst.2 hs.1.le E.fraction_mem.1 (by linarith)
        (flight s p).1 (flight s p).2 (by linarith [hp.1]) hp.2.2 haccess
        (Real.toNNReal C) hΩ hcore
      have he : s+(t-s) = t := by ring
      rw [hCeq,he] at hl
      have hep := flightCharacteristic_from_phase s (t-s) p
      rw [he] at hep
      change flightCharacteristicEquiv t (t-s,(flight s p).1,(flight s p).2) = (s,p) at hep
      rw [hep] at hl
      exact hl)
  filter_upwards [hh] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst hshort hm
  exact ht hsa hta ⟨hst,hshort⟩ hm

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The nonzero actual hot solution acquires the entry velocities at a good finite time -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.exists_actual_entry
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hH : E.horizon = ⊤)
    {κ ρ ε : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G) :
    ∃ t : ℝ, 0 < t ∧ t ∈ G ∧ 0 < hotPhaseSlice E.hotLimit t (velocityPhaseBall κ ρ) := by
  obtain ⟨n,hn⟩ := E.escaping_seed hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK.le hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hH
  obtain ⟨T,hT,hseed⟩ := hn (Real.exp η*E.fraction+2)
  let a := max T 1
  let U := a+1
  have ha : 0 < a := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have haU : a < U := by dsimp [U]; linarith
  have hgrowth := E.entry_window hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hκmax hρ hε hεmax hαε hερ haccess
    ha haU (show U < U+1 by linarith) (by rw [hH]; exact ENNReal.ofReal_lt_top) n
  have hpos : (volume : Measure ℝ) (Ioo a U) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr haU))
  obtain ⟨s,hs,hsgrowth,hsseed⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae (hgrowth.and hseed))
  have hm : 0 < hotPhaseSlice E.hotLimit s
      (flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) := by
    have hh := hsseed ((le_max_left _ _).trans hs.1.le)
    rw [Measure.map_apply (flight_measurePreserving s).measurable
      (seedEscapeRegion_measurable n _ s)] at hh
    exact hh
  let b := min U (s+1/((n:ℝ)+6))
  have hden : 0 < (n:ℝ)+6 := by positivity
  have hsb : s < b := lt_min hs.2 (by linarith [one_div_pos.mpr hden])
  have hp : (volume : Measure ℝ) (Ioo s b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hsb))
  obtain ⟨t,ht,htgrowth,htG⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp (ae_restrict_of_ae (hsgrowth.and hG))
  have htU : t < U := ht.2.trans_le (min_le_left _ _)
  have hshort : ((n:ℝ)+6)*(t-s) ≤ 1 := by
    have hh : t-s < 1/((n:ℝ)+6) := by linarith [ht.2.trans_le (min_le_right _ _)]
    have hh' := (lt_div_iff₀ hden).mp hh
    nlinarith
  exact ⟨t,ha.trans (hs.1.trans ht.1),htG,
    htgrowth hs ⟨hs.1.trans ht.1,htU⟩ (sub_pos.mpr ht.1) hshort hm⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A bounded portion of actual entry mass survives on every later finite time window -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.persisting_entry
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hH : E.horizon = ⊤)
    {κ ρ ε : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))) :
    ∃ s : ℝ, 0 < s ∧ ∃ n : ℕ, ∀ᵐ t ∂volume, s ≤ t →
      0 < hotPhaseSlice E.hotLimit t (entryPhasePortion κ ρ n) := by
  let start (m : ℕ) : ℝ := 1/((m:ℝ)+2)
  have hstart (m : ℕ) : 0 < start m ∧ start m ≤ 1 := by
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
    exact ⟨by dsimp [start]; positivity,
      (div_le_iff₀ (show 0 < (m:ℝ)+2 by positivity)).mpr (by linarith)⟩
  have hsurvival (n m N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo (start m) ((N:ℝ)+2) → t ∈ Ioo (start m) ((N:ℝ)+2) → s ≤ t →
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) t := by
    apply E.characteristic_free_flight_survival hDP hcarleman hGLPS
      hs₀ hsmax hη hηmax hK.le hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ (hstart m).1
      (B := (N:ℝ)+3)
    · have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
      linarith [(hstart m).2]
    · linarith
    · rw [hH]; exact ENNReal.ofReal_lt_top
    · exact seedPhaseCutoff_smooth n
    · exact seedPhaseCutoff_compact n
    · exact fun p => (seedPhaseCutoff_mem n p).1
  choose C hC htrace using hsurvival
  have hgood : ∀ᵐ s ∂volume, ∀ n m N : ℕ, ∀ᵐ t ∂volume,
      s ∈ Ioo (start m) ((N:ℝ)+2) → t ∈ Ioo (start m) ((N:ℝ)+2) → s ≤ t →
      ENNReal.ofReal (Real.exp (C n m N*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) t :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun m => ae_all_iff.mpr fun N => htrace n m N
  obtain ⟨s,hs,hsg,hentry⟩ := E.exists_actual_entry hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hH
    hκ hκmax hρ hε hεmax hαε hερ haccess hgood
  obtain ⟨n,hn⟩ := exists_positive_entryPortion _ hentry
  obtain ⟨m,hm⟩ := exists_nat_gt (1/s)
  have hms : start m < s := by
    have hm' := (div_lt_iff₀ hs).mp hm
    apply (div_lt_iff₀ (show 0 < (m:ℝ)+2 by positivity)).mpr
    nlinarith
  refine ⟨s,hs,n,?_⟩
  filter_upwards [ae_all_iff.mpr (fun N => hsg n m N)] with t ht
  intro hst
  obtain ⟨N,hN⟩ := exists_nat_gt t
  have hi := ht N ⟨hms,by linarith⟩ ⟨hms.trans_le hst,by linarith⟩ hst
  have hle := hi.trans (phaseSlice_weight_le
    (fun z => E.toHotLimitExtraction.hotLimit_nonneg (hotCharacteristicEquiv z))
    (fun p => (seedPhaseCutoff_mem n p).2) t)
  have hh := hle (entryPhasePortion κ ρ n)
  rw [Measure.smul_apply,smul_eq_mul,phaseSlice_weight_apply_eq (entryPhasePortion_measurable κ ρ n)
    (fun p hp => entryPhasePortion_cutoff hp)] at hh
  have hp : 0 < ENNReal.ofReal (Real.exp (C n m N*(s-t)))*
      hotPhaseSlice E.hotLimit s (entryPhasePortion κ ρ n) :=
    pos_iff_ne_zero.mpr (mul_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) (ne_of_gt hn))
  exact hp.trans_le hh

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A fixed-window transfer of proved finite blocks to the actual hot mass -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.window_mass_growth_from_blocks
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C r κ d : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C) (hr : 0 < r)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω) (hcore : ∀ z ∈ Ω, β z.2 = 1)
    (hstart : ∀ s ∈ Ioo a A, ∀ p ∈ flight s ⁻¹' lateBox κ d s, β p = 1)
    (N : ℕ) (g : ℝ≥0∞) (P : ℝ → ℝ → Prop)
    (horder : ∀ s ∈ Ioo a A, ∀ t ∈ Ioo a A, P s t → s ≤ t)
    (hblock : ∀ s ∈ Ioo a A, ∀ t ∈ Ioo a A, P s t →
      ∀ p ∈ flight s ⁻¹' lateBox κ d s, g ≤ localizedHistoryBlockMass
        (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1) hα.le hγ.le η r)
        (K/(4*r)) C t a η E.fraction s hΩ (lateBox κ d t) N (s,p)) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a A → t ∈ Ioo a A → P s t →
      g*hotLateBoxMass E.hotLimit κ d s ≤ hotLateBoxMass E.hotLimit κ d t := by
  have hh := E.covered_normal_endpoint_histories hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK.le hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hβ₁ hfrequency hr hΩ hcore
  exact ae_localized_hot_mass_growth
    (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1) hα.le hγ.le η r)
    (K/(4*r)) C a A η E.fraction κ d hΩ (f := E.hotLimit) (β := β)
    E.toHotLimitExtraction.hotLimit_nonneg hβ₁ N g P hh hstart horder hblock

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual hot mass grows across every sufficiently short late annular block -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem annular_growth_parameters {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ ε γ₀ : ℝ, 0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
        {S : AttainedCapSequence F},
      Published.DunfordPettis1940HotPairWindows → Published.GPV2009CarlemanInput →
      Published.GLPS1988Proposition3 → ∀ E : HotPairExtraction S,
      0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < K → 0 < α → α ≤ 1/4 → 0 < γ → 0 < d₀ → d₀ ≤ 1 →
      JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1 → 1 < q → q < 2 →
      (η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
      ∀ {b W B : ℝ}, 0 < b → 0 < W → W ≤ κ*b/200 → b+W < B →
        ENNReal.ofReal B < E.horizon → Real.exp η*E.fraction+6*W < κ*b/2 →
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
        s ∈ Ioo b (b+W) → t ∈ Ioo b (b+W) →
        (8*κ*A₀/K)*s ≤ t-s → t-s ≤ (16*κ*A₀/K)*s →
        (6:ℝ≥0∞)*hotLateBoxMass E.hotLimit κ d s ≤ hotLateBoxMass E.hotLimit κ d t) := by
  obtain ⟨A₀,hA₀,N,ε,γ₁,hε,hεsmall,hγ₁,hblock⟩ :=
    GeometricBackground.geometric_common_block_growth hd hdsmall hκ hκsmall hg
  obtain ⟨γ₂,hγ₂,hcutoff⟩ := GeometricBackground.exists_annular_characteristic_cutoff hκ hκsmall.le
  refine ⟨A₀,ε,min γ₁ γ₂,hA₀,hε,hεsmall,lt_min hγ₁ hγ₂,?_⟩
  intro s₀ η K α γ d₀ q F S hDP hcarleman hGLPS E hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    hηsmall hαsmall hγsmall hKlarge b W B hb hW hWsmall hB hH hspatial
  have hηquarter : η ≤ Real.log (1+(1/4:ℝ)/20) :=
    hηsmall.trans (Real.log_le_log (by positivity) (by linarith))
  obtain ⟨β,hβ,hβc,hβn,hβ₁,hcore,hfrequency⟩ := hcutoff
    (zero_lt_one.trans_le E.phase_mem.1) hη hηquarter hα.le hαmax hγ.le
    (hγsmall.trans (min_le_right _ _)) hK.le hb hWsmall E.fraction
  let C := 48*Real.pi*K/(κ*b)
  let Ω := characteristicHistoryCore b (κ*b/4) ((κ*b) • firstAxis)
  have hΩ : MeasurableSet Ω := characteristicHistoryCore_measurable _ _ _
  have hfreq : ∀ u : CharacteristicPhase, u.1 ∈ Ioo b (b+W) → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C := by
    intro u hu hus
    have hh := hfrequency u ⟨hu.1.le,hu.2.le⟩ hus
    change GeometricBackground.frequency E.phase η E.fraction K α γ u.1
      (spaceEquiv (u.2.1+u.1 • u.2.2)) u.2.2 ≤ C
    simpa only [spaceEquiv_apply,JetPeriodicDatum.spatialMap,split_apply] using hh
  let P : ℝ → ℝ → Prop := fun s t => (8*κ*A₀/K)*s ≤ t-s ∧ t-s ≤ (16*κ*A₀/K)*s
  have horder : ∀ s ∈ Ioo b (b+W), ∀ t ∈ Ioo b (b+W), P s t → s ≤ t := by
    intro s hs t _ hp
    have hsp : 0 < s := hb.trans hs.1
    have hh : 0 < (8*κ*A₀/K)*s := by positivity
    dsimp only [P] at hp
    linarith [hp.1]
  have hstart : ∀ s ∈ Ioo b (b+W), ∀ p ∈ flight s ⁻¹' lateBox κ d s, β p = 1 := by
    intro s hs p hp
    have hc := lateBox_start_commonCore hκ hκsmall.le hdsmall hb hWsmall
      ⟨hs.1.le,hs.2.le⟩ hp
    exact hcore p hc.1 hc.2
  have hpoint : ∀ s ∈ Ioo b (b+W), ∀ t ∈ Ioo b (b+W), P s t →
      ∀ p ∈ flight s ⁻¹' lateBox κ d s, (6:ℝ≥0∞) ≤ localizedHistoryBlockMass
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1) hα.le hγ.le η (κ*b))
      (K/(4*(κ*b))) C t b η E.fraction s hΩ (lateBox κ d t) N (s,p) := by
    intro s hs t ht hp
    have hΔW : t-s ≤ W := by linarith [hs.1,ht.2]
    apply phase_block_lower (κ := κ) (d := d) (s := s) (Δ := t-s)
    intro x v hx
    have hcut := lateBox_above_spatial_cutoff hκ hdsmall hb hs.1.le hΔW hspatial hx
    have hh := hblock (zero_lt_one.trans_le E.phase_mem.1) hη hηsmall hα.le hαsmall
      hγ.le (hγsmall.trans (min_le_left _ _)) hK hKlarge hb hWsmall
      ⟨hs.1.le,hs.2.le⟩ hp.1 hp.2 hΔW hs.1.le E.fraction_mem.1 x v hx hcut
    simpa only [C,Ω,show s+(t-s)=t by ring] using hh.le
  have hh := E.window_mass_growth_from_blocks hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    hb (by linarith) hB hH (show 0 ≤ C by dsimp [C]; positivity) (mul_pos hκ hb)
    hβ hβc hβn hβ₁ hfreq hΩ (fun z hz => hcore z.2 hz.1 hz.2) hstart N 6 P horder hpoint
  filter_upwards [hh] with s hs
  filter_upwards [hs] with t ht
  intro hsw htw hlo hhi
  exact ht hsw htw ⟨hlo,hhi⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform geometric parameters force late-box vanishing for every infinite-horizon extraction -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem uniform_late_zero_parameters {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ ε γ₀ : ℝ, 0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
        {S : AttainedCapSequence F},
      Published.DunfordPettis1940HotPairWindows → Published.GPV2009CarlemanInput →
      Published.GLPS1988Proposition3 → ∀ E : HotPairExtraction S,
      0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < K → 0 < α → α ≤ 1/4 → 0 < γ → 0 < d₀ → d₀ ≤ 1 →
      JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1 → 1 < q → q < 2 →
      η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
      E.horizon = ⊤ → ∃ R : ℝ, 0 < R ∧
        ∀ᵐ t ∂volume, R < t → hotLateBoxMass E.hotLimit κ d t = 0 := by
  obtain ⟨A₀,ε,γ₀,hA₀,hε,hεsmall,hγ₀,hannular⟩ :=
    annular_growth_parameters hd hdsmall hκ hκsmall hg
  refine ⟨A₀,ε,γ₀,hA₀,hε,hεsmall,hγ₀,?_⟩
  intro s₀ η K α γ d₀ q F S hDP hcarleman hGLPS E hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hηsmall hαsmall hγsmall hKlarge hH
  have hbase : 15360*A₀ ≤ K := by
    have hh := mul_le_mul_of_nonneg_right hεsmall hK.le
    nlinarith
  have hlocal (b W : ℝ) (hb : 0 < b) (hW : 0 < W) (hWsmall : W ≤ κ*b/200)
      (hcut : Real.exp η*E.fraction+6*W < κ*b/2) :=
    hannular hDP hcarleman hGLPS E hs₀ hsmax hη hηmax hK hα hαmax
      hγ hd₀ hd₀max hsmall hq₁ hq₂ hηsmall hαsmall hγsmall hKlarge
      hb hW hWsmall (B := 2*(b+W)) (by linarith)
      (by rw [hH]; exact ENNReal.ofReal_lt_top) hcut
  obtain ⟨R,hR,hgrow⟩ := GrowthContradiction.annular_to_late_growth
    (hotLateBoxMass E.hotLimit κ d) hκ hK hA₀ hbase hlocal
  refine ⟨R,hR,?_⟩
  let δ := 8*κ*A₀/K
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ κ/1920 := by
    dsimp [δ]
    apply (div_le_iff₀ hK).mpr
    have hh := mul_le_mul_of_nonneg_left hbase hκ.le
    nlinarith
  have hr : (1+2*δ)^4 < 3 := by
    have hh : 1+2*δ ≤ (11/10:ℝ) := by nlinarith
    have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+2*δ) hh 4
    norm_num at hp
    linarith
  let m : ℝ → ℝ := fun t => (hotLateBoxMass E.hotLimit κ d t).toReal
  have hcap := E.toHotLimitExtraction.hotLateBoxMass_real_cap hκ.le hd.le hq₂
  have hfinite := E.toHotLimitExtraction.hotLateBoxMass_finite hκ.le hd.le hq₂
  have hstep : ∀ᵐ s ∂volume, R < s → ∀ᵐ t ∂volume,
      t ∈ Ioo ((1+δ)*s) ((1+2*δ)*s) → 3*m s ≤ m t := by
    filter_upwards [hgrow] with s hs
    intro hRs
    filter_upwards [hs,hfinite] with t ht htf
    intro hit
    have hspos := hR.trans hRs
    have htpos : 0 < t := (mul_pos (by positivity : (0:ℝ)<1+δ) hspos).trans hit.1
    have hh := ENNReal.toReal_mono (htf htpos.le) (ht hRs hit)
    rw [ENNReal.toReal_mul] at hh
    norm_num at hh
    exact (mul_le_mul_of_nonneg_right (by norm_num : (3:ℝ)≤6) ENNReal.toReal_nonneg).trans hh
  have hlatecap : ∀ᵐ t ∂volume, R < t → m t ≤ lateBoxCapConstant q κ d*(1+t)^4 := by
    filter_upwards [hcap] with t ht
    intro hRt
    exact ht (hR.trans hRt).le
  have hz : ∀ᵐ t ∂volume, R < t → m t = 0 :=
    GrowthContradiction.ae_zero_of_late_growth_cap (r₀ := 1+δ) (r₁ := 1+2*δ)
      hR.le (by linarith) (by linarith) hr
      (lateBoxCapConstant_nonneg hκ.le hd.le) (fun _ => ENNReal.toReal_nonneg)
      hlatecap hstep
  filter_upwards [hz,hfinite] with t ht hf
  intro hRt
  have hm0 := ht hRt
  exact (ENNReal.toReal_eq_toReal_iff' (hf (hR.trans hRt).le) (by simp)).mp
    (by simpa only [ENNReal.toReal_zero] using hm0)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual hot mass grows across every sufficiently short late annular block -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.annular_mass_growth
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {d κ : ℝ} (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ ε γ₀ : ℝ, 0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      (η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
      ∀ {b W B : ℝ}, 0 < b → 0 < W → W ≤ κ*b/200 → b+W < B →
        ENNReal.ofReal B < E.horizon → Real.exp η*E.fraction+6*W < κ*b/2 →
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
        s ∈ Ioo b (b+W) → t ∈ Ioo b (b+W) →
        (8*κ*A₀/K)*s ≤ t-s → t-s ≤ (16*κ*A₀/K)*s →
        (6:ℝ≥0∞)*hotLateBoxMass E.hotLimit κ d s ≤ hotLateBoxMass E.hotLimit κ d t) := by
  obtain ⟨A₀,ε,γ₀,hA₀,hε,hεsmall,hγ₀,hgrowth⟩ :=
    annular_growth_parameters hd hdsmall hκ hκsmall hg
  exact ⟨A₀,ε,γ₀,hA₀,hε,hεsmall,hγ₀,hgrowth hDP hcarleman hGLPS E
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
