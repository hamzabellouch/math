import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdAverages
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotSourceIntegrability
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdBounds
import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedDensitySequence
import OAI.MathematicalPhysics.Boltzmann.Branching.AverageMajorant
import OAI.MathematicalPhysics.Boltzmann.Branching.AveragingTailSources
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCoordinates
import OAI.MathematicalPhysics.Boltzmann.Branching.CompactCapFamily
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanBackwardMap
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion
import OAI.MathematicalPhysics.Boltzmann.Branching.SupportedTransportTest
import OAI.MathematicalPhysics.Boltzmann.Branching.WindowLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalL1ApproximationLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeSurvival

namespace OAI

section

/-! # The concrete outer-annulus bound for the positive cap family -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.outer_bound {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) (J : ℕ) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T, ∀ᵐ v : Velocity,
      u ∉ AnnularEnvelope.torusTail s₀ η J → torusPhysical q F.solution.value (u,v) ≤
        (2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J)*H q v := by
  have hδ : 0 < DatumBounds.scale s₀ η (N+1) := DatumBounds.scale_pos hs₀ _
  have hδmax : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hn p : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds hδ hδmax q
    exact mul_nonneg F.coefficient_mem.1 (hb p).1
  exact capped_spacetime_outer_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
    hq (by positivity) (bounds (by positivity) F.amplitude_pos).1 hT
    (mul_nonneg (by norm_num) F.amplitude_pos.le) hTmax hδ hδmax le_rfl N J
    ((HotSeedProfile.normalized_measurable q _).const_mul _) hn F.initial_bound F.solution F.cap.le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniformly integrable GLPS sources for the actual rescaled hot solutions -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.TransportCutoff

theorem kineticWindow_velocity_integrable {f : Velocity → ℝ} (hf : Integrable f)
    (a A R : ℝ) : Integrable (fun z : Published.KineticPhase => f z.2)
      (kineticWindowVolume a A R) := by
  unfold kineticWindowVolume
  have : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  exact hf.comp_snd _

end BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem localized_hot_sources_ui_tail (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A R) :
    ∃ N : ℕ, UniformIntegrable (fun n => localizedSource A χ
      (S.euclideanHot (κ (n+N))) (S.euclideanHotSource (κ (n+N)))) 1 volume := by
  have hseq := (S.eventually_euclideanHot_bound hs₀ hsmax hη hηmax hK hd₀.le hq₂ hU hA).and
    (S.eventually_euclideanHotSource_bound hcarleman hs₀ hsmax hη hηmax hK hα hαmax
      hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hseq
  have hf : UniformIntegrable (fun n => S.euclideanHot (κ (n+N))) 1
      (kineticWindowVolume a A R) := by
    apply Compactness.uniformIntegrable_of_abs_le
      (kineticWindow_velocity_integrable ((integrable_H hq₂).const_mul (A+1)) a A R)
      (fun n => (S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _).aestronglyMeasurable)
    intro n
    rw [kineticWindowVolume_eq]
    filter_upwards [((hN (n+N) (Nat.le_add_left N n)).1).filter_mono ae_restrict_le,
      ae_restrict_mem (kineticWindow_measurable a A R)] with z hz hwin
    have h := hz ⟨ha.le.trans hwin.1.1.1,hwin.1.1.2⟩
    rw [abs_of_nonneg h.1]
    exact h.2
  have hQ : UniformIntegrable (fun n => S.euclideanHotSource (κ (n+N))) 1
      (kineticWindowVolume a A R) := by
    apply Compactness.uniformIntegrable_of_abs_le
      (kineticWindow_velocity_integrable (sourceEnvelope_integrable hq₂ s₀ η K α γ d₀ a A) a A R)
      (fun n => (S.euclideanHotSource_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _).aestronglyMeasurable)
    intro n
    rw [kineticWindowVolume_eq]
    filter_upwards [((hN (n+N) (Nat.le_add_left N n)).2).filter_mono ae_restrict_le,
      ae_restrict_mem (kineticWindow_measurable a A R)] with z hz hwin
    exact hz hwin.1.1
  exact ⟨N,localizedSource_ui_window ha.le hχ hc hs hf hQ⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Strong averaged limits agree with averages of the weak hot density -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem HotLimitExtraction.average_limit_identified (S : AttainedCapSequence F)
    (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {A R : ℝ}
    (hA : ENNReal.ofReal A < E.horizon)
    {χ : Published.KineticPhase → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {g : Published.SpaceTime → ℝ} (hg : LocallyIntegrable g)
    {K : Set Published.SpaceTime} (hKc : IsCompact K)
    (hKw : K ⊆ EuclideanFlight.hotBaseSet A R)
    (hstrong : Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, ψ v*(χ (z,v)*S.euclideanHot (E.indices n) (z,v)))-g z) 1
      (volume.restrict K)) atTop (𝓝 0)) :
    g =ᵐ[volume.restrict K]
      (fun z => ∫ v, ψ v*(χ (z,v)*E.hotLimit (EuclideanFlight.hotChart (z,v)))) := by
  have hw := E.average_weak S hs₀ hsmax hη hηmax hK hd₀ hq hA R hχ hc hψ hψc
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
  have hfi : ∀ᶠ n in atTop, Integrable
      (fun z => ∫ v, ψ v*(χ (z,v)*S.euclideanHot (E.indices n) (z,v)))
      (EuclideanFlight.hotBaseVolume A R) := by
    filter_upwards [S.eventually_euclideanHot_integrable E hs₀ hsmax hη hηmax hK hd₀ hq hA R]
      with n hn
    have hi := (hn.bdd_mul hm.aestronglyMeasurable (ae_of_all _ hb)).integral_prod_left
    simpa only [mul_assoc] using hi
  rw [EuclideanFlight.hotBaseVolume_eq] at hw hfi
  exact hw.eq_of_local_strong hfi hg hKc hKw hstrong

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A common weak subsequence for every hot pair window -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

structure HotPairExtraction (S : AttainedCapSequence F) extends HotLimitExtraction S where
  pairProfile : ℕ → HotPairPhase → ℝ
  pairWeak : ∀ j : ℕ, Published.WeakL1Converges (hotPairWindowVolume (j+1) (j+1))
    (fun n => CollisionCompactness.pairProduct (S.hotDensity (indices n))) (pairProfile j)
  pairNonneg : ∀ j : ℕ, ∀ᵐ z ∂hotPairWindowVolume (j+1) (j+1), 0 ≤ pairProfile j z

theorem exists_hot_pair_extraction (hDP : Published.DunfordPettis1940HotPairWindows)
    (S : AttainedCapSequence F) (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) :
    ∃ (φ : ℕ → ℕ) (W : ℕ → HotPairPhase → ℝ), StrictMono φ ∧
      ∀ j : ℕ, Published.WeakL1Converges (hotPairWindowVolume (j+1) (j+1))
        (fun n => CollisionCompactness.pairProduct (S.hotDensity (E.indices (φ n)))) (W j) := by
  have hm n := CollisionCompactness.pairProduct_measurable
    (S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq (E.indices n))
  have hb (j : ℕ) := S.hotPair_bounds hs₀ hsmax hη hηmax hK hd₀ hq
    (show 0 ≤ (j:ℝ)+1 by positivity) ((j:ℝ)+1)
  exact Published.L1WeakCompactnessInput.countable
    (fun j : ℕ => hotPairWindowVolume (j+1) (j+1))
    (fun j => hDP (j+1) (j+1) (by positivity) (by positivity)) hm
    (fun j => Compactness.uniformIntegrable_comp (hb j).1 E.indices)
    (fun j => (hb j).2.comp E.indices)

theorem exists_hot_pair_limit (hDP : Published.DunfordPettis1940HotPairWindows)
    (S : AttainedCapSequence F) (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) : Nonempty (HotPairExtraction S) := by
  obtain ⟨φ,W,hφ,hW⟩ := S.exists_hot_pair_extraction hDP E hs₀ hsmax hη hηmax hK hd₀ hq
  refine ⟨{ E.subsequence φ hφ with pairProfile := W, pairWeak := hW, pairNonneg := ?_ }⟩
  intro j
  apply (hW j).nonneg
  intro n
  exact ae_of_all _ (CollisionCompactness.pairProduct_nonneg
    (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq _))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A common bound for each compactly localized actual hot average -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_hot_average_bounded (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 ≤ a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U)
    {χ : Published.KineticPhase → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ kineticWindow a A R)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ᵐ z ∂(volume : Measure Published.SpaceTime),
      |∫ v, ψ v*(χ (z,v)*S.euclideanHot (κ n) (z,v))| ≤ B := by
  obtain ⟨C,hC⟩ := hχ.bounded_above_of_compact_support hc
  obtain ⟨D,hD⟩ := hψ.bounded_above_of_compact_support hψc
  let M : Velocity → ℝ := fun v => (A+1)*H q v
  have hi : Integrable M := (integrable_H hq).const_mul _
  have hn (v : Velocity) : 0 ≤ M v := mul_nonneg (by linarith) (H_nonneg q v)
  refine ⟨(|D| * |C|)*(∫ v, M v),mul_nonneg (by positivity) (integral_nonneg hn),?_⟩
  filter_upwards [S.eventually_euclideanHot_bound hs₀ hsmax hη hηmax hK hd₀ hq hU hA]
    with n hb
  have hk (z : Published.KineticPhase) : |ψ z.2*χ z| ≤ |D| * |C| := by
    rw [abs_mul]
    exact mul_le_mul ((hD z.2).trans (le_abs_self D)) ((hC z).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  have hf : ∀ᵐ z ∂((volume : Measure Published.SpaceTime).prod (volume : Measure Velocity)),
      ψ z.2*χ z ≠ 0 → |S.euclideanHot (κ n) z| ≤ M z.2 := by
    rw [← Measure.volume_eq_prod]
    filter_upwards [hb] with z hz hne
    have hcs : z ∈ tsupport χ := subset_tsupport χ (mul_ne_zero_iff.mp hne).2
    have ht := (hs hcs).1.1
    have h := hz ⟨ha.trans ht.1,ht.2⟩
    rw [abs_of_nonneg h.1]
    exact h.2
  have h := Compactness.average_le_majorant hi hn (by positivity : 0 ≤ |D| * |C|) hk hf
  simpa only [mul_assoc] using h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Published velocity averaging applied to the actual rescaled hot sources -/

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hot_resolvent_averaging (hcarleman : Published.GPV2009CarlemanInput)
    (hGLPS : Published.GLPS1988Proposition3) (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Filter.Tendsto (fun n => S.normalizedHorizon (κ n)) Filter.atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A R)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (N : ℕ) (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Published.LocalL1Converges (fun n => Published.resolventAverage
        (localizedSource A χ (S.euclideanHot (κ (φ n+N)))
          (S.euclideanHotSource (κ (φ n+N)))) (ψ j)) (g j) := by
  obtain ⟨N,hN⟩ := S.localized_hot_sources_ui_tail hcarleman hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA hχ hc hs
  have hcompact : IsCompact (Prod.snd '' tsupport χ) := hc.image continuous_snd
  obtain ⟨B,hB,hball⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : Velocity)
  have hv : tsupport χ ⊆ {z : KineticPhase | ‖z.2‖ ≤ B} := by
    intro z hz
    have hb := hball (mem_image_of_mem Prod.snd hz)
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hb : ‖z.2‖ < B).le
  let r : ℕ → KineticPhase → ℝ := fun n => localizedSource A χ
    (S.euclideanHot (κ (n+N))) (S.euclideanHotSource (κ (n+N)))
  have hr : ∀ n, ∀ᵐ z ∂(volume : Measure KineticPhase), B < ‖z.2‖ → r n z = 0 := by
    intro n
    exact ae_of_all _ (fun z hz => localizedSource_velocity_support hv _ _ z hz)
  obtain ⟨φ,g,hφ,hg⟩ := hGLPS.countable_tests r hB hr hN ψ hψ hψc
  exact ⟨N,φ,g,hφ,hg⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Strong local convergence of the actual hot velocity averages -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hot_averages_compact (hcarleman : Published.GPV2009CarlemanInput)
    (hGLPS : Published.GLPS1988Proposition3) (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A R)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (N : ℕ) (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocallyIntegrable (g j) ∧ ∀ E : Set Published.SpaceTime, IsCompact E →
        E ⊆ Icc 0 A ×ˢ univ →
        Tendsto (fun n => eLpNorm (fun z =>
          (∫ v, ψ j v*(χ (z,v)*S.euclideanHot (κ (φ n+N)) (z,v)))-g j z) 1
            (volume.restrict E)) atTop (𝓝 0) := by
  obtain ⟨N,φ,g,hφ,hg⟩ := S.hot_resolvent_averaging hcarleman hGLPS hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA hχ hc hs ψ hψ hψc
  have hzero (p : Velocity × Velocity) : χ (TransportCutoff.characteristic p 0) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    have hh := (hs hp).1.1.1
    change a ≤ (0:ℝ) at hh
    linarith
  have hind : Tendsto (fun n => φ n+N) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right (φ n) N) hφ.tendsto_atTop
  have hslab := hind.eventually (S.eventually_scaled_slab hs₀ hU hA)
  have hmeasure : (volume.restrict (Icc (0:ℝ) A)).prod (volume : Measure Velocity) =
      (volume : Measure Published.SpaceTime).restrict (Icc 0 A ×ˢ univ) := by
    calc
      _ = (volume.restrict (Icc (0:ℝ) A)).prod ((volume : Measure Velocity).restrict univ) := by
        rw [Measure.restrict_univ]
      _ = _ := by rw [Measure.prod_restrict,Measure.volume_eq_prod]
  refine ⟨N,φ,g,hφ,fun j => ⟨(hg j).1,?_⟩⟩
  apply (hg j).congr_on_window
  filter_upwards [hslab] with n hn
  rw [← hmeasure]
  exact S.hot_velocity_averages_resolvent hs₀ hsmax hη hηmax hK hd₀.le hq₂ _
    (hn A ⟨ha.le.trans haA,le_rfl⟩).2 hχ hzero (ψ j)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # One subsequence for countably many actual localized hot averages -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hot_countable_averages_compact (hcarleman : Published.GPV2009CarlemanInput)
    (hGLPS : Published.GLPS1988Proposition3) (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    (a A R : ℕ → ℝ) (ha : ∀ j, 0 < a j) (haA : ∀ j, a j ≤ A j)
    (hA : ∀ j, ENNReal.ofReal (A j) < U)
    (χ : ℕ → Published.KineticPhase → ℝ) (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ kineticWindow (a j) (A j) (R j))
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocallyIntegrable (g j) ∧ ∀ E : Set Published.SpaceTime, IsCompact E →
        E ⊆ Icc 0 (A j) ×ˢ univ →
        Tendsto (fun n => eLpNorm (fun z =>
          (∫ v, ψ j v*(χ j (z,v)*S.euclideanHot (κ (φ n)) (z,v)))-g j z) 1
            (volume.restrict E)) atTop (𝓝 0) := by
  let r := fun j n => localizedSource (A j) (χ j)
    (S.euclideanHot (κ n)) (S.euclideanHotSource (κ n))
  have hUI j : ∃ N : ℕ, UniformIntegrable (fun n => r j (n+N)) 1 volume :=
    S.localized_hot_sources_ui_tail hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ hκ hU (ha j) (haA j) (hA j) (hχ j) (hc j) (hs j)
  have hcompact j : IsCompact (Prod.snd '' tsupport (χ j)) := (hc j).image continuous_snd
  choose B hB hball using fun j => (hcompact j).isBounded.subset_ball_lt 0 (0 : Velocity)
  have hv j : tsupport (χ j) ⊆ {z : KineticPhase | ‖z.2‖ ≤ B j} := by
    intro z hz
    have hb := hball j (mem_image_of_mem Prod.snd hz)
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hb : ‖z.2‖ < B j).le
  have hr j n : ∀ᵐ z ∂(volume : Measure KineticPhase), B j < ‖z.2‖ → r j n z = 0 :=
    ae_of_all _ (fun z hz => localizedSource_velocity_support (hv j) _ _ z hz)
  obtain ⟨φ,g,hφ,hg⟩ := hGLPS.countable_tail_sources_tests r B hB hr hUI ψ hψ hψc
  have hzero j (p : Velocity × Velocity) : χ j (TransportCutoff.characteristic p 0) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    have hh := (hs j hp).1.1.1
    change a j ≤ (0:ℝ) at hh
    exact (not_le_of_gt (ha j)) hh
  have hslab j := hφ.tendsto_atTop.eventually (S.eventually_scaled_slab hs₀ hU (hA j))
  have hmeasure j : (volume.restrict (Icc (0:ℝ) (A j))).prod (volume : Measure Velocity) =
      (volume : Measure Published.SpaceTime).restrict (Icc 0 (A j) ×ˢ univ) := by
    calc
      _ = (volume.restrict (Icc (0:ℝ) (A j))).prod
          ((volume : Measure Velocity).restrict univ) := by rw [Measure.restrict_univ]
      _ = _ := by rw [Measure.prod_restrict,Measure.volume_eq_prod]
  refine ⟨φ,g,hφ,fun j => ⟨(hg j).1,?_⟩⟩
  apply (hg j).congr_on_window
  filter_upwards [hslab j] with n hn
  rw [← hmeasure j]
  exact S.hot_velocity_averages_resolvent hs₀ hsmax hη hηmax hK hd₀.le hq₂ _
    (hn (A j) ⟨(ha j).le.trans (haA j),le_rfl⟩).2 (hχ j) (hzero j) (ψ j)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Strong local velocity averaging to the same extracted hot density -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem HotLimitExtraction.strong_averages (hcarleman : Published.GPV2009CarlemanInput)
    (hGLPS : Published.GLPS1988Proposition3) (S : AttainedCapSequence F)
    (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (a A R : ℕ → ℝ) (ha : ∀ j, 0 < a j) (haA : ∀ j, a j ≤ A j)
    (hA : ∀ j, ENNReal.ofReal (A j) < E.horizon)
    (χ : ℕ → Published.KineticPhase → ℝ) (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ kineticWindow (a j) (A j) (R j))
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j (B : ℝ) (D : Set Published.SpaceTime),
      IsCompact D → D ⊆ EuclideanFlight.hotBaseSet (A j) B →
      Tendsto (fun n => eLpNorm (fun z =>
        (∫ v, ψ j v*(χ j (z,v)*S.euclideanHot (E.indices (φ n)) (z,v)))-
        (∫ v, ψ j v*(χ j (z,v)*E.hotLimit (EuclideanFlight.hotChart (z,v))))) 1
          (volume.restrict D)) atTop (𝓝 0) := by
  obtain ⟨φ,g,hφ,hg⟩ := S.hot_countable_averages_compact hcarleman hGLPS hs₀ hsmax hη
    hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ E.indices_strict E.horizon_limit
    a A R ha haA hA χ hχ hc hs ψ hψ hψc
  let E' := E.subsequence φ hφ
  refine ⟨φ,hφ,fun j B D hD hDw => ?_⟩
  have ht := (hg j).2 D hD (hDw.trans (EuclideanFlight.hotBaseSet_time (A j) B))
  have he := E'.average_limit_identified S hs₀ hsmax hη hηmax hK hd₀.le hq₂ (hA j)
    (hχ j).continuous (hc j) (hψ j).continuous (hψc j) (hg j).1 hD hDw ht
  simp only [E',HotLimitExtraction.subsequence_hotLimit] at he
  apply ht.congr
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [he] with z hz
  rw [hz]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual cap limit retains the common half-Gaussian moment envelope -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.moment_bound {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T,
      VelocityMoment.moment (fun v => torusPhysical q F.solution.value (u,v)) ≤
        ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
          (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
          (AnnularEnvelope.torusChart u)) := by
  have hδ : 0 < DatumBounds.scale s₀ η (N+1) := DatumBounds.scale_pos hs₀ _
  have hδmax : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hn p : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds hδ hδmax q
    exact mul_nonneg F.coefficient_mem.1 (hb p).1
  exact capped_spacetime_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
    hq (by positivity) (bounds (by positivity) F.amplitude_pos).1 hT
    (mul_nonneg (by norm_num) F.amplitude_pos.le) hTmax hδ hδmax le_rfl N
    ((HotSeedProfile.normalized_measurable q _).const_mul _) hn F.initial_bound F.solution F.cap.le

theorem CompactCapFamily.weak_limit_moment {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ}
    (hg : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g)
    (hgn : ∀ p, 0 ≤ g p) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume F.time,
      VelocityMoment.moment (fun v => g (u,v)) ≤
        ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
          (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
          (AnnularEnvelope.torusChart u)) := by
  have hA := momentBase_nonneg hs₀ hK hd₀ η α q
  have hB := JetEnvelopeGain.momentConstant_nonneg hK α γ
  apply hg.velocity_moment
    (fun n => torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q)
    (fun n => torusPhysical_nonneg (fun z => ((F.approximation (φ n)).solution.value_bounds z).1) q)
    hgn (fun n => memLp_one_iff_integrable.mp (F.density_ui.memLp (φ n)))
    ((AnnularEnvelope.commonMoment_measurable s₀ η _ _).comp AnnularEnvelope.torusChart_measurable)
    (CollisionCompactness.torus_common_integrable hs₀ hη hηmax F.time_pos.le hA hB)
    (fun u => AnnularEnvelope.commonMoment_nonneg hA hB s₀ η (AnnularEnvelope.torusChart u))
  intro n
  exact (F.approximation (φ n)).moment_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq F.time_pos.le F.time_le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Integrability of compact interior tests of the actual hot transport equation -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_transport_test_integrable (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A R) :
    ∀ᶠ n in atTop, Integrable (fun z =>
      transportDerivative χ z*S.euclideanHot (κ n) z+χ z*S.euclideanHotSource (κ n) z) := by
  filter_upwards [S.eventually_euclideanHot_bound hs₀ hsmax hη hηmax hK hd₀.le hq₂ hU hA,
    S.eventually_euclideanHotSource_bound hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA] with n hf hQ
  have hiF : Integrable (S.euclideanHot (κ n)) (kineticWindowVolume a A R) := by
    apply (kineticWindow_velocity_integrable ((integrable_H hq₂).const_mul (A+1)) a A R).mono'
      (S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _).aestronglyMeasurable
    rw [kineticWindowVolume_eq]
    filter_upwards [hf.filter_mono ae_restrict_le,ae_restrict_mem (kineticWindow_measurable a A R)]
      with z hz hwin
    have hb := hz ⟨ha.le.trans hwin.1.1.1,hwin.1.1.2⟩
    simpa only [Real.norm_of_nonneg hb.1] using hb.2
  have hiQ : Integrable (S.euclideanHotSource (κ n)) (kineticWindowVolume a A R) := by
    apply (kineticWindow_velocity_integrable
      (sourceEnvelope_integrable hq₂ s₀ η K α γ d₀ a A) a A R).mono'
      (S.euclideanHotSource_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ _).aestronglyMeasurable
    rw [kineticWindowVolume_eq]
    filter_upwards [hQ.filter_mono ae_restrict_le,ae_restrict_mem (kineticWindow_measurable a A R)]
      with z hz hwin
    simpa only [Real.norm_eq_abs] using hz hwin.1.1
  rw [kineticWindowVolume_eq] at hiF hiQ
  exact transport_test_integrable (kineticWindow_measurable a A R) hχ hc hs hiF hiQ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual dilated hot solutions satisfy the characteristic weak balance -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hot_characteristic_test (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : S.radius n*A ≤ shrinkingHorizon F.horizonScale n)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0)
    (hterminal : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p A) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      (∫ t in 0..A, transportDerivative χ (TransportCutoff.characteristic p t)*S.euclideanHot n (TransportCutoff.characteristic p t)+
        χ (TransportCutoff.characteristic p t)*S.euclideanHotSource n (TransportCutoff.characteristic p t)) = 0 := by
  have hm := S.normalizedHot_mild hs₀ hsmax hη hηmax hK hd₀ hq n hA
  have hfm := S.normalizedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n
  obtain ⟨hgm,B,hB⟩ := S.rescaledHotForcing_properties hs₀ hsmax hη hηmax hK hd₀ hq n
  have hi : Measurable (fun p =>
      (F.approximation n).hotInitial (PositiveIntegral.scalePhase (S.radius n) p)/S.radius n) :=
    (((F.approximation n).hotInitial_measurable).comp
      (by unfold PositiveIntegral.scalePhase; fun_prop)).div_const _
  have he := EuclideanFlight.smooth_linear_tested (q := q) hA0 hi hfm hgm hB hm hχ hzero hterminal
  simpa only [euclideanHot,S.euclideanHotSource_eq hs₀ n] using he

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Compact interior weak transport balances for the actual dilated hot solutions -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_hot_transport_balance (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A B R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
    (hB : ENNReal.ofReal B < U)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ kineticWindow a A R) :
    ∀ᶠ n in atTop, (∫ z, transportDerivative χ z*S.euclideanHot (κ n) z+
      χ z*S.euclideanHotSource (κ n) z) = 0 := by
  have hA : ENNReal.ofReal A < U :=
    (ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB
  have hB0 : 0 ≤ B := ha.le.trans (haA.trans hAB.le)
  have hzero (p : Velocity × Velocity) : χ (TransportCutoff.characteristic p 0) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => not_le_of_gt ha (hs h).1.1.1)
  have hterminal (p : Velocity × Velocity) : χ (TransportCutoff.characteristic p B) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => not_le_of_gt hAB (hs h).1.1.2)
  filter_upwards [S.eventually_transport_test_integrable hcarleman hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA hχ hc hs,
    S.eventually_scaled_slab hs₀ hU hB] with n hi hslab
  let f : Published.KineticPhase → ℝ := fun z =>
    transportDerivative χ z*S.euclideanHot (κ n) z+χ z*S.euclideanHotSource (κ n) z
  let D : Set Published.KineticPhase := (Ioc 0 B ×ˢ (univ : Set Velocity)) ×ˢ univ
  have hμ : ((volume.restrict (Ioc 0 B)).prod (volume : Measure Velocity)).prod volume =
      (volume : Measure Published.KineticPhase).restrict D := by
    dsimp only [D]
    rw [Measure.volume_eq_prod,Measure.volume_eq_prod,← Measure.prod_restrict,← Measure.prod_restrict]
    simp only [Measure.restrict_univ]
  have hii : Integrable f (((volume.restrict (Ioc 0 B)).prod (volume : Measure Velocity)).prod volume) := by
    rw [hμ]
    exact hi.mono_measure Measure.restrict_le_self
  have hpath := S.hot_characteristic_test hs₀ hsmax hη hηmax hK hd₀.le hq₂ (κ n) hB0
    (hslab B ⟨hB0,le_rfl⟩).2 hχ hzero hterminal
  have hh := EuclideanFlight.integral_eq_zero_of_characteristics hB0 hii hpath
  rw [hμ] at hh
  have hout (z : Published.KineticPhase) (hz : z ∉ D) : f z = 0 := by
    have hn : z ∉ tsupport χ := by
      intro h
      have ht := (hs h).1.1
      exact hz ⟨⟨⟨ha.trans_le ht.1,ht.2.trans hAB.le⟩,mem_univ _⟩,mem_univ _⟩
    dsimp only [f]
    rw [transportDerivative_eq_zero hn,image_eq_zero_of_notMem_tsupport hn,zero_mul,zero_mul,add_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at hh
  exact hh

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
