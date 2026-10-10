import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedDensitySequence
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCharacteristics
import OAI.MathematicalPhysics.Boltzmann.Branching.HotWindowInput
import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeSurvival
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricColdSource
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreConvergence
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds
import OAI.MathematicalPhysics.Boltzmann.Jets.JetContinuation

namespace OAI

section

/-! # Actual weak hot limits on bounded spacetime windows -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem exists_hot_weak_limit (hDP : Published.DunfordPettis1940HotWindows)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (κ : ℕ → ℕ)
    {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∃ (φ : ℕ → ℕ) (g : HotKineticPhase → ℝ), StrictMono φ ∧
      Published.WeakL1Converges (hotWindowVolume A R)
        (fun n => S.hotDensity (κ (φ n))) g ∧
      (∀ᵐ z ∂hotWindowVolume A R, 0 ≤ g z) ∧
      (∀ᵐ z ∂hotWindowVolume A R, g z ≤ (A+1)*H q z.2) := by
  have hui := S.hotDensity_uniformIntegrable hs₀ hsmax hη hηmax hK hd₀ hq A R
  obtain ⟨φ,g,hφ,hg⟩ := hDP A R hA hR (fun n => S.hotDensity (κ n))
    (fun n => S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq (κ n))
    (Compactness.uniformIntegrable_comp hui κ)
    ((S.hotDensity_unifTight hs₀ hsmax hη hηmax hK hd₀ hq hA R).comp κ)
  refine ⟨φ,g,hφ,hg,?_,?_⟩
  · exact hg.nonneg (fun n => ae_of_all _
      (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq (κ (φ n))))
  · exact hg.le (fun n => memLp_one_iff_integrable.mp (hui.memLp (κ (φ n))))
      (((ChartKernel.measurable_H q).comp measurable_snd).const_mul _)
      (hot_majorant_integrable hq A R)
      (fun n => S.hotDensity_bound hs₀ hsmax hη hηmax hK hd₀ hq (κ (φ n)) A R)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The exact affine cap passes to the weak hot limit -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hotWindow_time_mem (A R : ℝ) :
    ∀ᵐ z ∂hotWindowVolume A R, z.1.1 ∈ Icc (0:ℝ) A := by
  exact Measure.quasiMeasurePreserving_fst.ae
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc))

theorem hotDensity_cap_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (A R : ℝ) :
    ∀ᵐ z ∂hotWindowVolume A R, S.hotDensity n z ≤ (z.1.1+S.coldFraction n)*H q z.2 := by
  let μt : Measure ℝ := volume.restrict (Icc (0:ℝ) A)
  let μx : Measure JetPrototype.Space := volume.restrict (Metric.closedBall 0 R)
  have hB : ∀ᵐ u ∂μt.prod (μx.prod volume),
      S.extendedHot n u ≤ (u.1+S.coldFraction n)*H q u.2.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
      (S.extendedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n)
      ((measurable_fst.add_const _).mul
        ((ChartKernel.measurable_H q).comp measurable_snd.snd)))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hb := S.extendedHot_bound_at hs₀ hsmax hη hηmax hK hd₀ hq n ht.1
    have hab : μx.prod (volume : Measure Velocity) ≤ FlightMeasure.phaseVolume :=
      Measure.prod_mono Measure.restrict_le_self le_rfl
    exact hb.filter_mono (ae_mono hab)
  exact (measurePreserving_prodAssoc μt μx (volume : Measure Velocity)).quasiMeasurePreserving.ae hB

theorem hot_velocity_integrable {q : ℝ} (hq : q < 2) (A R : ℝ) :
    Integrable (fun z : HotKineticPhase => H q z.2) (hotWindowVolume A R) := by
  unfold hotWindowVolume
  have : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict
      (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
  exact (integrable_H hq).comp_snd _

theorem hot_time_majorant_integrable {q : ℝ} (hq : q < 2) (A R : ℝ) :
    Integrable (fun z : HotKineticPhase => z.1.1*H q z.2) (hotWindowVolume A R) := by
  apply (hot_majorant_integrable hq A R).mono'
    (measurable_fst.fst.mul ((ChartKernel.measurable_H q).comp measurable_snd)).aestronglyMeasurable
  filter_upwards [hotWindow_time_mem A R] with z hz
  change ‖z.1.1*H q z.2‖ ≤ (A+1)*H q z.2
  rw [Real.norm_of_nonneg (mul_nonneg hz.1 (H_nonneg q _))]
  exact mul_le_mul_of_nonneg_right (hz.2.trans (by linarith)) (H_nonneg q _)

theorem hot_weak_limit_cap (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {κ : ℕ → ℕ} {l A R : ℝ}
    (hl : Tendsto (fun n => S.coldFraction (κ n)) atTop (𝓝 l))
    {g : HotKineticPhase → ℝ}
    (hg : Published.WeakL1Converges (hotWindowVolume A R) (fun n => S.hotDensity (κ n)) g) :
    ∀ᵐ z ∂hotWindowVolume A R, g z ≤ (z.1.1+l)*H q z.2 := by
  have hui := S.hotDensity_uniformIntegrable hs₀ hsmax hη hηmax hK hd₀ hq A R
  have hb (n) : ∀ᵐ z ∂hotWindowVolume A R,
      S.hotDensity (κ n) z ≤ z.1.1*H q z.2+S.coldFraction (κ n)*H q z.2 := by
    simpa only [add_mul] using S.hotDensity_cap_bound hs₀ hsmax hη hηmax hK hd₀ hq (κ n) A R
  simpa only [Pi.mul_apply,Function.comp_apply,add_mul] using hg.le_affine
    (fun n => memLp_one_iff_integrable.mp (hui.memLp (κ n)))
    (measurable_fst.fst.mul ((ChartKernel.measurable_H q).comp measurable_snd))
    ((ChartKernel.measurable_H q).comp measurable_snd)
    (hot_time_majorant_integrable hq A R) (hot_velocity_integrable hq A R) hl hb

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # One subsequence for the hot density, mesh phase and limiting horizon -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

structure HotLimitExtraction (S : AttainedCapSequence F) where
  fraction : ℝ
  fraction_mem : fraction ∈ Icc 0 1
  phase : ℝ
  phase_mem : phase ∈ Icc 1 (Real.exp η)
  horizon : ℝ≥0∞
  horizon_ge : 1 ≤ horizon
  indices : ℕ → ℕ
  indices_strict : StrictMono indices
  fraction_limit : Tendsto (fun n => S.coldFraction (indices n)) atTop (𝓝 fraction)
  phase_limit : Tendsto (fun n => GeometricMesh.phase (s₀/S.radius (indices n)) η)
    atTop (𝓝 phase)
  horizon_limit : Tendsto (fun n => S.normalizedHorizon (indices n)) atTop (𝓝 horizon)
  profile : ℕ → HotKineticPhase → ℝ
  weak : ∀ j : ℕ, Published.WeakL1Converges (hotWindowVolume (j+1) (j+1))
    (fun n => S.hotDensity (indices n)) (profile j)
  nonneg : ∀ j : ℕ, ∀ᵐ z ∂hotWindowVolume (j+1) (j+1), 0 ≤ profile j z
  cap : ∀ j : ℕ, ∀ᵐ z ∂hotWindowVolume (j+1) (j+1),
    profile j z ≤ (z.1.1+fraction)*H q z.2

theorem exists_hot_limit_extraction (hDP : Published.DunfordPettis1940HotWindows)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) : Nonempty (HotLimitExtraction S) := by
  obtain ⟨l,hl,θ,hθ,U,hU,a,ha,hla,hθa,hUa⟩ := S.joint_subsequence hs₀ hη
  let μ : ℕ → Measure HotKineticPhase := fun j => hotWindowVolume (j+1) (j+1)
  have hui (j) : UniformIntegrable (fun n => S.hotDensity (a n)) 1 (μ j) :=
    Compactness.uniformIntegrable_comp
      (S.hotDensity_uniformIntegrable hs₀ hsmax hη hηmax hK hd₀ hq _ _) a
  have htight (j) : UnifTight (fun n => S.hotDensity (a n)) 1 (μ j) :=
    (S.hotDensity_unifTight hs₀ hsmax hη hηmax hK hd₀ hq (by positivity) _).comp a
  obtain ⟨b,g,hb,hg⟩ := Published.L1WeakCompactnessInput.countable μ
    (fun j => hDP (j+1) (j+1) (by positivity) (by positivity))
    (fun n => S.hotDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq (a n)) hui htight
  refine ⟨{
    fraction := l
    fraction_mem := hl
    phase := θ
    phase_mem := hθ
    horizon := U
    horizon_ge := hU
    indices := a ∘ b
    indices_strict := ha.comp hb
    fraction_limit := hla.comp hb.tendsto_atTop
    phase_limit := hθa.comp hb.tendsto_atTop
    horizon_limit := hUa.comp hb.tendsto_atTop
    profile := g
    weak := hg
    nonneg := ?_
    cap := ?_ }⟩
  · intro j
    exact (hg j).nonneg (fun n => ae_of_all _
      (S.hotDensity_nonneg hs₀ hsmax hη hηmax hK hd₀ hq (a (b n))))
  · intro j
    exact S.hot_weak_limit_cap hs₀ hsmax hη hηmax hK hd₀ hq
      (hla.comp hb.tendsto_atTop) (hg j)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual cold labels approaching each point of the limiting geometric mesh -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabel (E : HotLimitExtraction S) (k : ℤ) (a : Bool) (n : ℕ) :
    JetLattice.Label :=
  ⟨GeometricMesh.jetIndex s₀ η (fun j => S.radius (E.indices j)) k n,a,0⟩

theorem HotLimitExtraction.coldLabel_scale_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) :
    Tendsto (fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus/S.radius (E.indices n))
      atTop (𝓝 (E.phase*Real.exp (η*(k:ℝ)))) :=
  GeometricMesh.jet_scale_approximation hs₀ hη (fun n => S.radius_pos hs₀ (E.indices n))
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop) E.phase_limit k

theorem HotLimitExtraction.coldLabel_retained (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool)
    (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))) :
    ∀ᶠ n in atTop, (E.coldLabel k a n).annulus < F.indices (E.indices n) :=
  GeometricMesh.jetIndex_eventually_retained hs₀ hη (fun n => S.radius_pos hs₀ (E.indices n))
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop)
    E.phase_limit E.fraction_limit k hk

theorem HotLimitExtraction.coldLabel_scale_tendsto_zero (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) :
    Tendsto (fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus) atTop (𝓝 0) := by
  have h := ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop).mul
    (E.coldLabel_scale_limit hs₀ hη k a)
  simpa only [Function.comp_def,zero_mul,mul_div_cancel₀ _ (S.radius_pos hs₀ _).ne'] using h

theorem HotLimitExtraction.coldLabel_width_tendsto_zero (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) :
    Tendsto (fun n => d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
      atTop (𝓝 0) := by
  simpa only [zero_pow (by decide : (10:ℕ) ≠ 0),mul_zero] using
    ((E.coldLabel_scale_tendsto_zero hs₀ hη k a).pow 10).const_mul d₀

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The quantitative free-flight error of the constructed cap approximations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.cold {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (i : Label) : ℝ × JetPrototype.Phase → ℝ :=
  rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N F.solution.value i

theorem CapApproximation.local_free_error {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (m : ℕ) (i : Label) (hi0 : i.lattice = 0) (hi : i.annulus < N)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    (Ω : Set JetPrototype.Space) [IsFiniteMeasure (JetPrototype.spaceVolume.restrict Ω)]
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    let s := jetScale s₀ η i.annulus
    let E := coldOpticalDepth (4*JetBarrierCollision.frequencyConstant*K*d₀*s^9)
      (weightFrequencyConstant q 2) (DatumBounds.scale s₀ η (N+1))
      (escapedFrequencyConstant s₀ η α K d₀ q m) m t
    let ε := JetSupersolution.epsilon K s (d₀*s^10)
    let μ := (JetPrototype.spaceVolume.restrict Ω).prod (volume : Measure Velocity)
    let error := fun p : JetPrototype.Phase => |H q p.2*F.cold i (t,p)-
      JetFreeTransport.free η K α γ s (d₀*s^10) t i.positive (shift (displacement i.lattice) p)|
    Integrable error μ ∧ (∫ p, error p ∂μ) ≤
      (E+ε)*(JetPrototype.spaceVolume.restrict Ω).real univ*(JetBarrierLocalMass.massConstant*(K/s)) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  exact rebuilt_local_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hTmax
    hq (by positivity) (bounds (by positivity) F.amplitude_pos).1 hT (by linarith [F.amplitude_pos])
    hδ hsmall le_rfl m N i hi0 hwidth hdmax
    ((HotSeedProfile.normalized_measurable q _).const_mul F.coefficient) hh₀ F.initial_bound
    F.solution F.cap.le hi Ω ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The positive terminal cap scale is an excluded cold label -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_at_endpoint (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hfrac : 0 < E.fraction) (k : ℤ) (a : Bool)
    (hk : E.phase*Real.exp (η*(k:ℝ)) = E.fraction) :
    ∀ᶠ n in atTop, (E.coldLabel k a n).annulus = F.indices (E.indices n) := by
  have hm := E.coldLabel_scale_limit hs₀ hη k a
  rw [hk] at hm
  have he := GeometricMesh.indices_eventually_eq_of_same_positive_limit hs₀.le hη hfrac
    (fun n => S.radius_pos hs₀ (E.indices n)) hm E.fraction_limit
  filter_upwards [he] with n hn
  exact Nat.add_right_cancel hn

theorem HotLimitExtraction.coldLabel_below_endpoint (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool)
    (hk : E.phase*Real.exp (η*(k:ℝ)) < E.fraction) :
    ∀ᶠ n in atTop, F.indices (E.indices n) < (E.coldLabel k a n).annulus := by
  have he := (E.coldLabel_scale_limit hs₀ hη k a).eventually_lt E.fraction_limit hk
  filter_upwards [he] with n hn
  by_contra h
  have hb := JetGeometry.scale_antitone hs₀.le hη.le
    (Nat.add_le_add_right (le_of_not_gt h) 1)
  exact (not_lt_of_ge hb)
    ((div_lt_div_iff_of_pos_right (S.radius_pos hs₀ (E.indices n))).mp hn)

theorem HotLimitExtraction.coldLabel_retained_iff (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) :
    ∀ᶠ n in atTop, ((E.coldLabel k a n).annulus < F.indices (E.indices n) ↔
      E.fraction < E.phase*Real.exp (η*(k:ℝ))) := by
  rcases lt_trichotomy E.fraction (E.phase*Real.exp (η*(k:ℝ))) with h | h | h
  · filter_upwards [E.coldLabel_retained hs₀ hη k a h] with n hn
    exact iff_of_true hn h
  · have hp : 0 < E.fraction := by
      rw [h]
      exact mul_pos (lt_of_lt_of_le zero_lt_one E.phase_mem.1) (Real.exp_pos _)
    filter_upwards [E.coldLabel_at_endpoint hs₀ hη hp k a h.symm] with n hn
    rw [hn,h]
    simp only [lt_self_iff_false]
  · filter_upwards [E.coldLabel_below_endpoint hs₀ hη k a h] with n hn
    exact iff_of_false (not_lt_of_ge hn.le) (not_lt_of_ge h.le)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual cold cap colors converge to their free flight on dilation windows -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_cold_dilation_free_error {s₀ η K α γ d₀ q T a S U : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q T (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 T) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (hwidth : ∀ n, T*(d₀*jetScale s₀ η (j n).annulus^10) ≤
      enlargementWidth η (jetScale s₀ η (j n).annulus))
    (hdmax : ∀ n, d₀*jetScale s₀ η (j n).annulus^10 ≤ 1/64)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ x in Ω, ∫ v : Velocity,
      |r n*(H q v*(F n).cold (j n) (t n,(r n • x,v))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • x,v)))|
      ∂volume ∂JetPrototype.spaceVolume) atTop (𝓝 0) := by
  let s := fun n => jetScale s₀ η (j n).annulus
  let δ := fun n => DatumBounds.scale s₀ η (N n+1)
  let C := 4*JetBarrierCollision.frequencyConstant*K*d₀
  let A := weightFrequencyConstant q 2
  let D := escapedFrequencyConstant s₀ η α K d₀ q 0
  let E := fun n => coldOpticalDepth (C*s n^9) A (δ n) D 0 (t n)
  let ε := fun n => JetSupersolution.epsilon K (s n) (d₀*(s n)^10)
  let err := fun n (p : JetPrototype.Phase) =>
    H q p.2*(F n).cold (j n) (t n,p)-
      JetFreeTransport.free η K α γ (s n) (d₀*(s n)^10) (t n) (j n).positive
        (shift (displacement (j n).lattice) p)
  let I := fun n => ∫ p : JetPrototype.Phase, |err n p|
    ∂(JetPrototype.spaceVolume.restrict (r n • Ω)).prod volume
  have hs (n) : 0 < s n := DatumBounds.scale_pos (η := η) hs₀ _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) JetBarrierCollision.frequencyConstant_nonneg) hK) hd₀.le
  have hA : 0 ≤ A := weightFrequencyConstant_nonneg q (by norm_num)
  have hD : 0 ≤ D := escapedFrequencyConstant_nonneg hs₀ hK hd₀ η α q 0
  have hEn (n) : 0 ≤ E n := coldOpticalDepth_nonneg
    (mul_nonneg hC (pow_nonneg (hs n).le _)) hA (DatumBounds.scale_pos hs₀ _).le hD (ht n).1.le 0
  have hεn (n) : 0 ≤ ε n := JetSupersolution.epsilon_nonneg hK (hs n)
    (mul_pos hd₀ (pow_pos (hs n) _))
  have hcomp (n) : IsCompact (r n • Ω) := hΩ.image (continuous_const_smul (r n))
  have hfin (n) : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (r n • Ω)) :=
    isFiniteMeasure_restrict.mpr (hcomp n).measure_lt_top.ne
  have hbound (n) : Integrable (fun p => |err n p|)
      ((JetPrototype.spaceVolume.restrict (r n • Ω)).prod volume) ∧
      I n ≤ (E n+ε n)*((r n)^3*JetPrototype.spaceVolume.real Ω)*
        (JetBarrierLocalMass.massConstant*(K/s n)) := by
    let _ := hfin n
    have hb := (F n).local_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hT hTmax hq hsmall 0 (j n) (hj0 n) (hj n) (hwidth n) (hdmax n) (r n • Ω) (ht n)
    dsimp only at hb
    refine ⟨hb.1,?_⟩
    simpa only [I,err,E,ε,C,A,D,s,δ,measureReal_restrict_apply_univ,
      ColdDilationMeasure.spaceVolume_real_smul Ω (hr n)] using hb.2
  have hElim : Tendsto E atTop (𝓝 0) :=
    coldOpticalDepth_tendsto_zero hC hA hD hS (fun n => (hr n).le)
      (fun n => (hs n).le) (fun n => (ht n).1.le) (fun n => (DatumBounds.scale_pos hs₀ _).le)
      hhi htime hδ hrlim
  have hεlim : Tendsto ε atTop (𝓝 0) := jet_epsilon_tendsto_zero hs hhi hrlim K d₀
  have hlim : Tendsto (fun n => I n/(r n)^2) atTop (𝓝 0) :=
    scaled_local_error_tendsto_zero hEn hεn measureReal_nonneg JetBarrierLocalMass.massConstant_nonneg
      hK hr hs ha hlo (fun n => integral_nonneg (fun _ => abs_nonneg _))
      (fun n => (hbound n).2) hElim hεlim
  convert hlim using 1
  funext n
  rw [ColdDilationMeasure.dilated_error_integral (err n) Ω (hr n)]
  rw [← integral_prod _ (hbound n).1]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Cold dilation estimates for cap shots with varying horizons -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_variable_cold_dilation_free_error {s₀ η K α γ d₀ q a S U : ℝ} {T : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : ∀ n, 0 ≤ T n) (hTmax : ∀ n, T n ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q (T n) (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 (T n)) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (hwidth : ∀ n, T n*(d₀*jetScale s₀ η (j n).annulus^10) ≤
      enlargementWidth η (jetScale s₀ η (j n).annulus))
    (hdmax : ∀ n, d₀*jetScale s₀ η (j n).annulus^10 ≤ 1/64)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ x in Ω, ∫ v : Velocity,
      |r n*(H q v*(F n).cold (j n) (t n,(r n • x,v))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • x,v)))|
      ∂volume ∂JetPrototype.spaceVolume) atTop (𝓝 0) := by
  let s := fun n => jetScale s₀ η (j n).annulus
  let δ := fun n => DatumBounds.scale s₀ η (N n+1)
  let C := 4*JetBarrierCollision.frequencyConstant*K*d₀
  let A := weightFrequencyConstant q 2
  let D := escapedFrequencyConstant s₀ η α K d₀ q 0
  let E := fun n => coldOpticalDepth (C*s n^9) A (δ n) D 0 (t n)
  let ε := fun n => JetSupersolution.epsilon K (s n) (d₀*(s n)^10)
  let err := fun n (p : JetPrototype.Phase) =>
    H q p.2*(F n).cold (j n) (t n,p)-
      JetFreeTransport.free η K α γ (s n) (d₀*(s n)^10) (t n) (j n).positive
        (shift (displacement (j n).lattice) p)
  let I := fun n => ∫ p : JetPrototype.Phase, |err n p|
    ∂(JetPrototype.spaceVolume.restrict (r n • Ω)).prod volume
  have hs (n) : 0 < s n := DatumBounds.scale_pos (η := η) hs₀ _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) JetBarrierCollision.frequencyConstant_nonneg) hK) hd₀.le
  have hA : 0 ≤ A := weightFrequencyConstant_nonneg q (by norm_num)
  have hD : 0 ≤ D := escapedFrequencyConstant_nonneg hs₀ hK hd₀ η α q 0
  have hEn (n) : 0 ≤ E n := coldOpticalDepth_nonneg
    (mul_nonneg hC (pow_nonneg (hs n).le _)) hA (DatumBounds.scale_pos hs₀ _).le hD (ht n).1.le 0
  have hεn (n) : 0 ≤ ε n := JetSupersolution.epsilon_nonneg hK (hs n)
    (mul_pos hd₀ (pow_pos (hs n) _))
  have hcomp (n) : IsCompact (r n • Ω) := hΩ.image (continuous_const_smul (r n))
  have hfin (n) : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (r n • Ω)) :=
    isFiniteMeasure_restrict.mpr (hcomp n).measure_lt_top.ne
  have hbound (n) : Integrable (fun p => |err n p|)
      ((JetPrototype.spaceVolume.restrict (r n • Ω)).prod volume) ∧
      I n ≤ (E n+ε n)*((r n)^3*JetPrototype.spaceVolume.real Ω)*
        (JetBarrierLocalMass.massConstant*(K/s n)) := by
    let _ := hfin n
    have hb := (F n).local_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      (hT n) (hTmax n) hq hsmall 0 (j n) (hj0 n) (hj n) (hwidth n) (hdmax n) (r n • Ω) (ht n)
    dsimp only at hb
    refine ⟨hb.1,?_⟩
    simpa only [I,err,E,ε,C,A,D,s,δ,measureReal_restrict_apply_univ,
      ColdDilationMeasure.spaceVolume_real_smul Ω (hr n)] using hb.2
  have hElim : Tendsto E atTop (𝓝 0) :=
    coldOpticalDepth_tendsto_zero hC hA hD hS (fun n => (hr n).le)
      (fun n => (hs n).le) (fun n => (ht n).1.le) (fun n => (DatumBounds.scale_pos hs₀ _).le)
      hhi htime hδ hrlim
  have hεlim : Tendsto ε atTop (𝓝 0) := jet_epsilon_tendsto_zero hs hhi hrlim K d₀
  have hlim : Tendsto (fun n => I n/(r n)^2) atTop (𝓝 0) :=
    scaled_local_error_tendsto_zero hEn hεn measureReal_nonneg JetBarrierLocalMass.massConstant_nonneg
      hK hr hs ha hlo (fun n => integral_nonneg (fun _ => abs_nonneg _))
      (fun n => (hbound n).2) hElim hεlim
  convert hlim using 1
  funext n
  rw [ColdDilationMeasure.dilated_error_integral (err n) Ω (hr n)]
  rw [← integral_prod _ (hbound n).1]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Thermal mask replacement on finite spatial cylinders -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_mask_average_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) (t : ℝ)
    (Ω : Set Transverse) (hΩ : volume Ω < ⊤) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    let r := fun n => S.radius (E.indices n)
    let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
    let d := fun n => d₀*(s n)^10
    let μ := E.phase*Real.exp (η*(k:ℝ))
    Tendsto (fun n => ∫ x : JetPrototype.Space,
      |∫ w, JetGeometry.maskError (r n) η (s n) (d n) μ t a (x.1,w)
        ∂(volume : Measure Transverse).prod volume| ∂(volume.restrict Ω).prod ν)
      atTop (𝓝 0) := by
  intro r s d μ
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hrlim : Tendsto r atTop (𝓝 0) :=
    (S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop
  have hb := JetGeometry.maskError_average_L1_tendsto hr hrlim
    (E.coldLabel_scale_limit hs₀ hη k a) (E.coldLabel_width_tendsto_zero hs₀ hη k a)
    η t a Ω hΩ
  change Tendsto (fun n => ∫ y, |∫ w,
    JetGeometry.maskError (r n) η (r n*(s n/r n)) (d n) μ t a (y,w)
      ∂(volume : Measure Transverse).prod volume| ∂volume.restrict Ω) atTop (𝓝 0) at hb
  simp only [mul_div_cancel₀ _ (hr _).ne'] at hb
  have h := hb.const_mul (ν.real univ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with n
  exact (integral_fun_fst (μ := volume.restrict Ω) (ν := ν)
    (fun y => |∫ w, JetGeometry.maskError (r n) η (s n) (d n) μ t a (y,w)
      ∂(volume : Measure Transverse).prod volume|)).symm

theorem HotLimitExtraction.coldLabel_mask_average_integrable (E : HotLimitExtraction S)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ)
    (Ω : Set Transverse) (hΩ : volume Ω < ⊤) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun x : JetPrototype.Space => ∫ w,
      JetGeometry.maskError (S.radius (E.indices n)) η
        (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
        (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
        (E.phase*Real.exp (η*(k:ℝ))) t a (x.1,w)
      ∂(volume : Measure Transverse).prod volume) ((volume.restrict Ω).prod ν) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  exact (JetGeometry.maskError_integrable _ _ _ _ _ _ _
    ((volume : Measure Transverse).restrict Ω)).integral_prod_left.comp_fst ν

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The rebuilt cold family of an actual cap shot -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.cold_properties {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    (∀ i, Measurable (F.cold i)) ∧ (∀ i u, 0 ≤ F.cold i u) ∧
      (∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, F.cold i u ≤ F.solution.value u) ∧
      (∀ i, ColdMildAE q (N+1) (damping q (N+1) F.amplitude) T F.solution.value
        (color s₀ η K α γ d₀ q N i) (F.cold i)) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hp := rebuiltColdFamily_properties hq (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR le_rfl
    F.solution.measurable_value (measurable_color s₀ η K α γ d₀ q N)
    F.solution.value_bounds hc₀ hi.2 (F.solution.all_mild hT)
  exact ⟨hp.1,fun i u => (hp.2.1 i u).1,hp.2.2.1,hp.2.2.2.2⟩

theorem CapApproximation.hotNetSource_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.hotNetSource := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hh := (F.hot_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).1
  exact ((measurable_forcing F.solution.measurable_value q (N+1) _).sub
    (Measurable.tsum (fun i => measurable_coldForcing F.solution.measurable_value (hc.1 i) q (N+1) _))).sub
    (hh.const_mul _)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual hot remainder satisfies a bounded linear mild equation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.hotInitial {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (p : JetPrototype.Phase) : ℝ :=
  initial s₀ η K α γ d₀ q N
    (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p-
      ∑' i, color s₀ η K α γ d₀ q N i p

theorem CapApproximation.hot_mild {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, (fun p => F.hot (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T (damping q (N+1) F.amplitude) JetBarrier.flight
        F.hotInitial (remainderForcing q (N+1) (damping q (N+1) F.amplitude)
          F.solution.value F.cold) (t,p)) := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh₀
  exact family_hot_mildAE hq (by positivity : 0 ≤ (N+1:ℝ))
    (bounds (by positivity) F.amplitude_pos).1 hT (mul_nonneg (by norm_num) F.amplitude_pos.le) le_rfl
    F.solution.measurable_value hc.1 F.solution.value_bounds hc.2.1 hc.2.2.1
    (fun i p => (hi.1 i p).1) hi.2 F.solution.mild hc.2.2.2

theorem CapApproximation.hot_localized {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (χ χ' : JetPrototype.Phase → ℝ → ℝ)
    (hχ : ∀ p, ContinuousOn (χ p) (Icc 0 T))
    (hχ' : ∀ p, ContinuousOn (χ' p) (Icc 0 T))
    (hdχ : ∀ p t, t ∈ Icc 0 T → HasDerivAt (χ p) (χ' p t) t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      χ p T*F.hot (T,JetBarrier.flight T p) = Real.exp (-T)*χ p 0*F.hotInitial p+
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ p t*F.hotNetSource (t,JetBarrier.flight t p)+
            (χ' p t+χ p t)*F.hot (t,JetBarrier.flight t p)) := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hb := family_hot_bounds hq (by positivity : 0 ≤ (N+1:ℝ)) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) F.amplitude_pos.le)
    le_rfl F.solution.measurable_value hc.1 F.solution.value_bounds hc.2.1 hc.2.2.1
  have hm : Measurable F.hotInitial := by
    unfold hotInitial initial
    exact ((measurable_seed s₀ η K α γ d₀ q N).add
      ((HotSeedProfile.normalized_measurable q _).const_mul F.coefficient)).sub
      (Measurable.tsum (measurable_color s₀ η K α γ d₀ q N))
  exact PositiveIntegral.localized_characteristic hT hm hb.1 hb.2.2.1
    (fun u => by rw [abs_of_nonneg (hb.2.2.2 u).1]; exact (hb.2.2.2 u).2)
    (F.hot_mild hs₀ hsmax hη hηmax hK hd₀ hq hT) χ χ' hχ hχ' hdχ

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The mixed-cold source bound for the actual cap approximations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.coldSource {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) : ℝ × JetPrototype.Phase → ℝ :=
  coldFamilySource q (N+1) F.cold

theorem CapApproximation.coldSource_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.coldSource := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hC : Measurable (fun u => ∑' i, F.cold i u) := Measurable.tsum hc.1
  exact (measurable_forcing hC q (N+1) 0).sub
    (Measurable.tsum (fun i => measurable_coldForcing hC (hc.1 i) q (N+1) 0))

theorem CapApproximation.cold_source_bound (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) (m : ℕ)
    (htail : JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent (m+1 : ℕ))*T^(m+1) ≤ 1) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → 0 ≤ F.coldSource u ∧
      F.coldSource u ≤ (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
        JetEscapedEnvelope.constant s₀ η α K d₀
          (JetEscapedEnvelope.exponent (m+1 : ℕ))*u.1^m := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀.le hq₂ hT
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hE := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α
    (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have hb := geometric_cold_source (b := (N+1:ℝ)) hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ hTmax (m+1 : ℕ) N hc.1
    (fun u => (F.solution.value_bounds u).2) hc.2.1 hc.2.2.1
    (rebuilt_zero s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N
      (fun u => (F.solution.value_bounds u).1))
    (fun t ht i x w => rebuilt_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall
      hq₂ (by positivity) hL hT hR (hTmax.trans (by norm_num)) le_rfl N hh₀
      F.solution.measurable_value F.solution.value_bounds F.initial_bound i ht
      (JetPeriodicDatum.spatialMap x,w))
    (fun n i => rebuilt_shift n (F.solution.periodic n) i)
    (fun t ht => by simpa only [Real.rpow_natCast] using tail_small hE ht.1.le ht.2 htail)
  filter_upwards [hb] with u hu hut
  refine ⟨(hu hut).1,?_⟩
  have h := (hu hut).2
  rw [scalarMajorant_eq_source s₀ η K α γ d₀ q N m hut.1 0] at h
  simpa only [CapApproximation.coldSource,ZeroProfile.source,mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_add] using h

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Thermal concentration for the actual mesh labels -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_thermal_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 ≤ t) {B : ℝ} {ψ : Velocity → ℝ}
    (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) (x : JetPrototype.Space) :
    let r := fun n => S.radius (E.indices n)
    let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
    let d := fun n => d₀*(s n)^10
    let μ := E.phase*Real.exp (η*(k:ℝ))
    Tendsto (fun n => (∫ v, r n*JetFreeTransport.free η K α γ (s n) (d n)
        (r n*t) a (r n • x,v)*ψ v)-
      (JetCoreDensity.compressed K α γ μ t (AxialFlow.foot (JetPrototype.sign a) α γ μ t x.2)*
        ψ (PlaneChart.join 0 (AxialFlow.velocity (JetPrototype.sign a) α γ μ t x.2)))*
      (∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
        JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
  intro r s d μ
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hs (n) : 0 < s n := DatumBounds.scale_pos hs₀ _
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hrlim : Tendsto r atTop (𝓝 0) :=
    (S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop
  have hslim : Tendsto (fun n => s n/r n) atTop (𝓝 μ) := E.coldLabel_scale_limit hs₀ hη k a
  have hdlim : Tendsto d atTop (𝓝 0) := E.coldLabel_width_tendsto_zero hs₀ hη k a
  have hclip : Tendsto (fun n => max (μ/2) (s n/r n)) atTop (𝓝 μ) := by
    have hm : Tendsto (fun n => max (μ/2) (s n/r n)) atTop (𝓝 (max (μ/2) μ)) :=
      tendsto_const_nhds.max hslim
    simpa only [max_eq_right (show μ/2 ≤ μ by linarith)] using hm
  have hbase := JetCoreDensity.dilated_free_thermal_reduction hr hK hα hγ
    (by positivity : 0 < μ/2) (fun n => le_max_left (μ/2) (s n/r n))
    (fun n => mul_pos hd₀ (pow_pos (hs n) 10)) hμ ht hrlim hclip hdlim hψ hψB η a x
  apply hbase.congr'
  filter_upwards [hslim.eventually (lt_mem_nhds (show μ/2 < μ by linarith))] with n hn
  rw [max_eq_right hn.le,mul_div_cancel₀ _ (hr n).ne']

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Spatial L1 thermal reduction for the actual retained-scale labels -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_thermal_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t) {B : ℝ} {ψ : Velocity → ℝ}
    (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    let r := fun n => S.radius (E.indices n)
    let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
    let d := fun n => d₀*(s n)^10
    let μ := E.phase*Real.exp (η*(k:ℝ))
    Tendsto (fun n => ∫ x, |(∫ v, r n*JetFreeTransport.free η K α γ (s n) (d n)
        (r n*t) a (r n • x,v)*ψ v)-
      JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
        (∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
          JetThermalKernel.J (SheetMeasures.join w)
          ∂(volume : Measure Transverse).prod volume)| ∂ρ) atTop (𝓝 0) := by
  intro r s d μ
  let f : ℕ → JetPrototype.Space → ℝ := fun n x =>
    (∫ v, r n*JetFreeTransport.free η K α γ (s n) (d n) (r n*t) a (r n • x,v)*ψ v)-
      JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
        (∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
          JetThermalKernel.J (SheetMeasures.join w)
          ∂(volume : Measure Transverse).prod volume)
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hs (n) : 0 < s n := DatumBounds.scale_pos hs₀ _
  have hd (n) : 0 < d n := mul_pos hd₀ (pow_pos (hs n) 10)
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hfm (n) : Measurable (f n) :=
    (JetCoreDensity.free_average_measurable (r n) η K α γ (s n) (d n) t a hψ.measurable).sub
      ((JetCoreDensity.limitingCoefficient_measurable hα.le hγ.le hμ ht.le K
        (JetPrototype.sign a) hψ).mul
          (JetCoreDensity.mask_average_measurable (r n) η (s n/r n) (d n) t a))
  have hl (x) : Tendsto (fun n => f n x) atTop (𝓝 0) :=
    E.coldLabel_thermal_limit hs₀ hη hK hα.le hγ.le hd₀ k a ht.le hψ hψB x
  let C := ((K*max 1 (α*γ)⁻¹)/t)*B
  have hb (n x) : |f n x| ≤ 2*C := by
    have hfree := JetCoreDensity.dilated_free_average_bound (hr n) hK hα hγ
      (hs n) (hd n) ht η a x hψ hψB
    have hc := JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB
      (JetPrototype.sign a) x
    have hm := JetCoreDensity.masked_thermal_bound
      (JetCoreDensity.dilatedMask_abs_le (r n) η (s n/r n) (d n) t a x)
    have hp : |JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
        (∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
          JetThermalKernel.J (SheetMeasures.join w)
          ∂(volume : Measure Transverse).prod volume)| ≤ C := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) hm).trans hc
    exact (abs_sub _ _).trans ((add_le_add hfree hp).trans_eq (by dsimp [C]; ring))
  have h := tendsto_integral_of_dominated_convergence (μ := ρ)
    (F := fun n x => |f n x|) (f := fun _ => (0:ℝ)) (fun _ => 2*C)
    (fun n => (hfm n).abs.aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      exact hb n x)) (ae_of_all _ (fun x => by simpa only [abs_zero] using (hl x).abs))
  simpa only [integral_zero] using h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual free-core average reduces to its limiting shell and fine stripes -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.coldLabelFreeAverage (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  let r := S.radius (E.indices n)
  let s := JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  ∫ v, r*JetFreeTransport.free η K α γ s (d₀*s^10) (r*t) a (r • x,v)*ψ v

def HotLimitExtraction.coldLabelStripeAverage (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (y : Transverse) : ℝ :=
  let r := S.radius (E.indices n)
  let s := JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  ∫ w, (JetGeometry.stripe s a).indicator (fun _ => (1:ℝ))
    (r • (y-t • ((d₀*s^10) • w.1)))*JetThermalKernel.J (SheetMeasures.join w)
    ∂(volume : Measure Transverse).prod volume

def HotLimitExtraction.coldLabelStripedProfile (E : HotLimitExtraction S) (k : ℤ) (a : Bool)
    (n : ℕ) (t : ℝ) (ψ : Velocity → ℝ) (x : JetPrototype.Space) : ℝ :=
  let μ := E.phase*Real.exp (η*(k:ℝ))
  JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
    ((JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*
      E.coldLabelStripeAverage k a n t x.1)

theorem HotLimitExtraction.coldLabel_free_striped_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t) {B : ℝ} {ψ : Velocity → ℝ}
    (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (Ω : Set Transverse) (hΩ : volume Ω < ⊤) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Tendsto (fun n => ∫ x, |E.coldLabelFreeAverage k a n t ψ x-
      E.coldLabelStripedProfile k a n t ψ x| ∂(volume.restrict Ω).prod ν) atTop (𝓝 0) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  let ρ := (volume.restrict Ω).prod ν
  let r := fun n => S.radius (E.indices n)
  let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  let d := fun n => d₀*(s n)^10
  let μ := E.phase*Real.exp (η*(k:ℝ))
  let c := JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ
  let m := fun n x => ∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
    JetThermalKernel.J (SheetMeasures.join w) ∂(volume : Measure Transverse).prod volume
  let e := fun n (x : JetPrototype.Space) => ∫ w,
    JetGeometry.maskError (r n) η (s n) (d n) μ t a (x.1,w)
    ∂(volume : Measure Transverse).prod volume
  let f := E.coldLabelFreeAverage k a
  let C := ((K*max 1 (α*γ)⁻¹)/t)*B
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hs (n) : 0 < s n := DatumBounds.scale_pos hs₀ _
  have hd (n) : 0 < d n := mul_pos hd₀ (pow_pos (hs n) 10)
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have htlim := E.coldLabel_thermal_L1_limit hs₀ hη hK hα hγ hd₀ k a ht hψ hψB ρ
  have hmlim := E.coldLabel_mask_average_limit hs₀ hη k a t Ω hΩ ν
  change Tendsto (fun n => ∫ x, |f n t ψ x-c x*m n x| ∂ρ) atTop (𝓝 0) at htlim
  change Tendsto (fun n => ∫ x, |e n x| ∂ρ) atTop (𝓝 0) at hmlim
  have hlim := htlim.add (hmlim.const_mul C)
  simp only [mul_zero,zero_add] at hlim
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _ hlim
  intro n
  have hi₁ : Integrable (fun x => f n t ψ x-c x*m n x) ρ :=
    JetCoreDensity.thermal_error_integrable (hr n) hK hα hγ (hs n) (hd n) hμ ht η a hψ hψB ρ
  have hi₂ : Integrable (e n) ρ := E.coldLabel_mask_average_integrable k a n t Ω hΩ ν
  rw [← integral_const_mul,← integral_add hi₁.abs (hi₂.abs.const_mul C)]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
    (hi₁.abs.add (hi₂.abs.const_mul C))
  filter_upwards [] with x
  have he : e n x = m n x-(JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*
      E.coldLabelStripeAverage k a n t x.1 := by
    have hb := JetGeometry.maskError_average_eq (r n) η (s n/r n) (d n) μ t a x
    simp only [mul_div_cancel₀ _ (hr n).ne'] at hb
    simpa only [e,m,r,s,d,coldLabelStripeAverage] using hb
  have hid : f n t ψ x-E.coldLabelStripedProfile k a n t ψ x =
      (f n t ψ x-c x*m n x)+c x*e n x := by
    rw [he]
    change f n t ψ x-c x*((JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*
      E.coldLabelStripeAverage k a n t x.1) = _
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right
    (JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB (JetPrototype.sign a) x)
    (abs_nonneg _)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Cold free-flight convergence on varying cap horizons -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_variable_cold_dilation_limit {s₀ η K α γ d₀ q a S U : ℝ} {T : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : ∀ n, 0 ≤ T n) (hTmax : ∀ n, T n ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q (T n) (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 (T n)) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ x in Ω, ∫ v : Velocity,
      |r n*(H q v*(F n).cold (j n) (t n,(r n • x,v))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • x,v)))|
      ∂volume ∂JetPrototype.spaceVolume) atTop (𝓝 0) := by
  have hslim : Tendsto (fun n => jetScale s₀ η (j n).annulus) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (DatumBounds.scale_pos (η := η) hs₀ _).le) hhi
    simpa only [mul_zero] using hrlim.const_mul S
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (eventually_cold_survival_geometry (T := (1/32:ℝ)) (d₀ := d₀) hη hslim)
  apply (tendsto_add_atTop_iff_nat n₀).mp
  exact cap_variable_cold_dilation_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max (fun n => hT (n+n₀)) (fun n => hTmax (n+n₀)) hq hsmall
    (fun n => N (n+n₀)) (fun n => F (n+n₀)) (fun n => j (n+n₀))
    (fun n => hj0 (n+n₀)) (fun n => hj (n+n₀)) (fun n => r (n+n₀)) (fun n => t (n+n₀))
    (fun n => hr (n+n₀)) (hrlim.comp (tendsto_add_atTop_nat n₀))
    (fun n => ht (n+n₀)) ha hS (fun n => hlo (n+n₀)) (fun n => hhi (n+n₀))
    (fun n => htime (n+n₀)) (fun n => hδ (n+n₀))
    (fun n => (mul_le_mul_of_nonneg_right (hTmax (n+n₀)) (by positivity)).trans
      (hn₀ (n+n₀) (by omega)).1) (fun n => (hn₀ (n+n₀) (by omega)).2) Ω hΩ

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Product-space cold dilation with varying cap horizons -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_variable_cold_L1_dilation_limit {s₀ η K α γ d₀ q a S U : ℝ} {T : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : ∀ n, 0 ≤ T n) (hTmax : ∀ n, T n ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q (T n) (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 (T n)) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ p : JetPrototype.Phase,
      |r n*(H q p.2*(F n).cold (j n) (t n,(r n • p.1,p.2))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • p.1,p.2)))|
      ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) := by
  have hbase := cap_variable_cold_dilation_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hT hTmax hq hsmall N F j hj0 hj r t hr hrlim ht ha hS hlo hhi htime hδ Ω hΩ
  apply hbase.congr'
  have hslim : Tendsto (fun n => jetScale s₀ η (j n).annulus) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (DatumBounds.scale_pos (η := η) hs₀ _).le) hhi
    simpa only [mul_zero] using hrlim.const_mul S
  filter_upwards [eventually_cold_survival_geometry (T := (1/32:ℝ)) (d₀ := d₀) hη hslim] with n hn
  have hcomp : IsCompact (r n • Ω) := hΩ.image (continuous_const_smul (r n))
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (r n • Ω)) :=
    isFiniteMeasure_restrict.mpr hcomp.measure_lt_top.ne
  have hb := (F n).local_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    (hT n) (hTmax n) hq hsmall 0 (j n) (hj0 n) (hj n)
    ((mul_le_mul_of_nonneg_right (hTmax n) (by positivity)).trans hn.1) hn.2 (r n • Ω) (ht n)
  dsimp only at hb
  exact (integral_prod _ (ColdDilationMeasure.integrable_dilated_error (hr n) Ω hb.1)).symm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Cold/free convergence for the actual retained mesh labels -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_free_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool)
    (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    let j := E.coldLabel k a
    let r := fun n => S.radius (E.indices n)
    Tendsto (fun n => ∫ p : JetPrototype.Phase,
      |r n*(H q p.2*(F.approximation (E.indices n)).cold (j n) (r n*t,(r n • p.1,p.2))-
        JetFreeTransport.free η K α γ (JetGeometry.jetScale s₀ η (j n).annulus)
          (d₀*(JetGeometry.jetScale s₀ η (j n).annulus)^10) (r n*t) (j n).positive
          (shift (displacement (j n).lattice) (r n • p.1,p.2)))|
      ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) := by
  intro j r
  let μ := E.phase*Real.exp (η*(k:ℝ))
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hrlim : Tendsto r atTop (𝓝 0) :=
    (S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hs : Tendsto (fun n => JetGeometry.jetScale s₀ η (j n).annulus/r n) atTop (𝓝 μ) :=
    E.coldLabel_scale_limit hs₀ hη k a
  have hlo := hs.eventually (lt_mem_nhds (show μ/2 < μ by linarith))
  have hhi := hs.eventually (gt_mem_nhds (show μ < 2*μ by linarith))
  have hgood : ∀ᶠ n in atTop,
      (j n).annulus < F.indices (E.indices n) ∧
      r n*t ∈ Ioc 0 (shrinkingHorizon F.horizonScale (E.indices n)) ∧
      (μ/2)*r n ≤ JetGeometry.jetScale s₀ η (j n).annulus ∧
      JetGeometry.jetScale s₀ η (j n).annulus ≤ (2*μ)*r n := by
    filter_upwards [E.coldLabel_retained hs₀ hη k a hk,
      S.eventually_scaled_slab hs₀ E.horizon_limit htU,hlo,hhi] with n hj htime hl hu
    exact ⟨hj,⟨mul_pos (hr n) ht,(htime t ⟨ht.le,le_rfl⟩).2⟩,
      ((lt_div_iff₀ (hr n)).mp hl).le,((div_lt_iff₀ (hr n)).mp hu).le⟩
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hgood
  apply (tendsto_add_atTop_iff_nat n₀).mp
  exact cap_variable_cold_L1_dilation_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    (fun n => (shrinkingHorizon_pos F.horizonScale_pos (E.indices (n+n₀))).le)
    (fun n => (shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le)
    hq hsmall (fun n => F.indices (E.indices (n+n₀)))
    (fun n => F.approximation (E.indices (n+n₀))) (fun n => j (n+n₀)) (fun _ => rfl)
    (fun n => (hn₀ (n+n₀) (by omega)).1) (fun n => r (n+n₀)) (fun n => r (n+n₀)*t)
    (fun n => hr (n+n₀)) (hrlim.comp (tendsto_add_atTop_nat n₀))
    (fun n => (hn₀ (n+n₀) (by omega)).2.1) (by positivity : 0 < μ/2)
    (by positivity : 0 ≤ 2*μ) (fun n => (hn₀ (n+n₀) (by omega)).2.2.1)
    (fun n => (hn₀ (n+n₀) (by omega)).2.2.2)
    (U := t) (fun n => (mul_comm (r (n+n₀)) t).le)
    (fun n => (div_le_one (hr (n+n₀))).mp (S.coldFraction_mem hs₀ (E.indices (n+n₀))).2)
    Ω hΩ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
