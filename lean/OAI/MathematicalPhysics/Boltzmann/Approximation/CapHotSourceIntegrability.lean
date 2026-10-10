import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLabelFreeLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLossScaling
import OAI.MathematicalPhysics.Boltzmann.Branching.HotWindowGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricDampedRetention

namespace OAI

section

/-! # Lower source and loss bounds for the actual finite cap solutions -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.hot_net_lower {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (u : ℝ × JetPrototype.Phase) :
    -(lossFrequency q (N+1) F.solution.value u*F.hot u) ≤ F.hotNetSource u := by
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
  exact HotRepresentative.hot_net_source_lower (damping q (N+1) F.amplitude)
    (fun i => GaussianLocal.measurable_state (hp.1 i))
    (GaussianLocal.measurable_state F.solution.measurable_value)
    (fun i p => ⟨(hp.2.1 i (p.1.1,(p.1.2,p.2))).1, by
      have hc := hp.2.2.1 {i} (p.1.1,(p.1.2,p.2))
      simpa only [Finset.sum_singleton,GaussianLocal.state] using hc.trans (F.solution.value_bounds _).2⟩)
    (fun p => F.solution.value_bounds (p.1.1,(p.1.2,p.2)))
    (fun s p => hp.2.2.1 s (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)

theorem CapApproximation.loss_bound {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → lossFrequency q (N+1) F.solution.value u ≤
      2*Real.pi*(‖u.2.2‖+1)*
        ((u.1+DatumBounds.scale s₀ η (N+1)+escapedConstant s₀ η K α d₀)*hotConstant q+
          JetEnvelopeGain.momentConstant K α γ/u.1) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hp := rebuiltColdFamily_properties hq (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR le_rfl
    F.solution.measurable_value (measurable_color s₀ η K α γ d₀ q N)
    F.solution.value_bounds hc₀ hi.2 (F.solution.all_mild hT)
  have hreg := F.hot_regular hs₀ hsmax hη hηmax hK hd₀.le hq hT
  have hν := geometric_loss_bound (b := (N+1:ℝ)) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hTmax N F.solution.measurable_value hp.1 F.solution.value_bounds
    (fun i u => (hp.2.1 i u).1) hp.2.2.1
    (rebuilt_zero s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N
      (fun u => (F.solution.value_bounds u).1))
    (fun t ht i x w => rebuilt_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall
      hq (by positivity) hL hT hR (hTmax.trans (by norm_num)) le_rfl N hh₀
      F.solution.measurable_value F.solution.value_bounds F.initial_bound i ht
      (JetPeriodicDatum.spatialMap x,w))
    F.solution.periodic (fun n i => rebuilt_shift n (F.solution.periodic n) i) hreg.1.measurable
  filter_upwards [hν] with u hu ht
  apply (hu ht).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add (hreg.2 u.1 ⟨ht.1.le,ht.2⟩) le_rfl) (hotConstant_nonneg q)) le_rfl

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform lower hot-source bounds on positive rescaled time slabs -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def lossEnvelope (s₀ η K α γ d₀ q a A : ℝ) : ℝ :=
  ((A+1+escapedConstant s₀ η K α d₀)*hotConstant q)*(A+1)+
    JetEnvelopeGain.momentConstant K α γ*(1+1/a)

theorem eventually_rescaledHotSource_lower (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Icc a A →
      -(2*Real.pi*(‖u.2.2‖+1)*lossEnvelope s₀ η K α γ d₀ q a A) ≤
        S.rescaledHotSource (κ n) u := by
  have hrsmall := ((S.radius_tendsto_zero hs₀).comp hκ.tendsto_atTop).eventually
    (gt_mem_nhds zero_lt_one)
  filter_upwards [hrsmall,S.eventually_scaled_slab hs₀ hU hA] with n hr₁ hslab
  let Fn := F.approximation (κ n)
  have hT := (shrinkingHorizon_pos F.horizonScale_pos (κ n)).le
  have hTmax := (shrinkingHorizon_le F.horizonScale_pos (κ n)).trans F.horizonScale_le
  have hν := Fn.loss_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq hT hTmax
  have hcap := Fn.hot_spacetime_cap hs₀ hsmax hη hηmax hK hd₀.le hq hT
  have hn := (Fn.hot_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT).2.1
  have hr := S.radius_pos hs₀ (κ n)
  have hqp := ColdDilationMeasure.spacetime_dilation_quasiMeasurePreserving hr
  filter_upwards [hqp.ae hν,hqp.ae hcap] with u hu hc ht
  have htpos : 0 < u.1 := ha.trans_le ht.1
  have hphys := hslab u.1 ⟨htpos.le,ht.2⟩
  have hνp := hu ⟨mul_pos hr htpos,hphys.2⟩
  have hcp := hc hphys
  have hδ : S.radius (κ n)*S.coldFraction (κ n) =
      DatumBounds.scale s₀ η (F.indices (κ n)+1) := by
    dsimp [coldFraction]
    field_simp
  change Fn.hot (S.radius (κ n)*u.1,(S.radius (κ n) • u.2.1,u.2.2)) ≤
    S.radius (κ n)*u.1+DatumBounds.scale s₀ η (F.indices (κ n)+1) at hcp
  rw [← hδ] at hcp
  change lossFrequency q (F.indices (κ n)+1) Fn.solution.value
    (S.radius (κ n)*u.1,(S.radius (κ n) • u.2.1,u.2.2)) ≤
      2*Real.pi*(‖u.2.2‖+1)*
        ((S.radius (κ n)*u.1+DatumBounds.scale s₀ η (F.indices (κ n)+1)+
          escapedConstant s₀ η K α d₀)*hotConstant q+
            JetEnvelopeGain.momentConstant K α γ/(S.radius (κ n)*u.1)) at hνp
  conv_rhs at hνp => rw [← hδ]
  have hprod := Cap.scaled_loss_product_bound hr hr₁.le (S.coldFraction_mem hs₀ (κ n))
    ha ht.1 ht.2 (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)
    (hotConstant_nonneg q) (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    (by positivity : 0 ≤ 2*Real.pi*(‖u.2.2‖+1)) (hn _) hcp hνp
  have hlow := Fn.hot_net_lower hs₀ hsmax hη hηmax hK hd₀.le hq hT
    (S.radius (κ n)*u.1,(S.radius (κ n) • u.2.1,u.2.2))
  exact (neg_le_neg hprod).trans hlow

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A uniform absolute bound for the actual rescaled transport source -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem lossEnvelope_nonneg (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α γ q : ℝ) {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) :
    0 ≤ lossEnvelope s₀ η K α γ d₀ q a A := by
  unfold lossEnvelope
  exact add_nonneg (mul_nonneg (mul_nonneg (by
    have := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent 0)
    change 0 ≤ escapedConstant s₀ η K α d₀ at this
    change 0 ≤ A+1+escapedConstant s₀ η K α d₀
    linarith) (VelocityMoment.hotConstant_nonneg q)) (by linarith))
    (mul_nonneg (JetEnvelopeGain.momentConstant_nonneg hK α γ)
      (add_nonneg zero_le_one (one_div_pos.mpr ha).le))

def sourceEnvelope (s₀ η K α γ d₀ q a A : ℝ) (v : Velocity) : ℝ :=
  2*JetMainGain.coefficient K α γ q+1+
    2*Real.pi*(‖v‖+1)*lossEnvelope s₀ η K α γ d₀ q a A

theorem eventually_rescaledHotSource_abs (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Icc a A →
      |S.rescaledHotSource (κ n) u| ≤ sourceEnvelope s₀ η K α γ d₀ q a A u.2.2 := by
  let C := 2*HotApplication.realBound q
  let B := (2*JetMainGain.coefficient K α γ q+C)*
    JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (1+1 : ℕ))
  have he := ((S.sourceError_tendsto hs₀ C B A (by decide : 0 < (1:ℕ))).comp
    hκ.tendsto_atTop).eventually (gt_mem_nhds zero_lt_one)
  have hD := lossEnvelope_nonneg hs₀ hK hd₀ η α γ q ha (ha.le.trans haA)
  have hmain := JetMainGain.coefficient_nonneg hK α γ q
  filter_upwards [he,S.eventually_rescaledHotSource_upper hcarleman hs₀ hsmax hη hηmax
    hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU hA 1,
    S.eventually_rescaledHotSource_lower hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq₂ hκ hU ha hA] with n hn hupper hlower
  filter_upwards [hupper,hlower] with u hu hl ht
  have hlo := hl ht
  have hup := hu ⟨ha.trans_le ht.1,ht.2⟩
  have herr : S.sourceError C B A 1 (κ n) < 1 := hn
  have hnonneg : 0 ≤ 2*Real.pi*(‖u.2.2‖+1)*lossEnvelope s₀ η K α γ d₀ q a A :=
    mul_nonneg (by positivity) hD
  apply abs_le.mpr
  constructor <;> dsimp [sourceEnvelope]
  · linarith
  · change S.rescaledHotSource (κ n) u ≤ 2*JetMainGain.coefficient K α γ q+
      S.sourceError C B A 1 (κ n) at hup
    linarith

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The finite cap solution retains its smallest cold scale in the loss estimate -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.loss_scale_bound {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → lossFrequency q (N+1) F.solution.value u ≤
      2*Real.pi*(‖u.2.2‖+1)*
        ((u.1+DatumBounds.scale s₀ η (N+1)+escapedConstant s₀ η K α d₀)*hotConstant q+
          JetEnvelopeGain.momentConstant K α γ/(u.1+JetGeometry.jetScale s₀ η N)) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hp := rebuiltColdFamily_properties hq (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR le_rfl
    F.solution.measurable_value (measurable_color s₀ η K α γ d₀ q N)
    F.solution.value_bounds hc₀ hi.2 (F.solution.all_mild hT)
  have hreg := F.hot_regular hs₀ hsmax hη hηmax hK hd₀.le hq hT
  have hν := geometric_loss_scale_bound (b := (N+1:ℝ)) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hTmax N F.solution.measurable_value hp.1 F.solution.value_bounds
    (fun i u => (hp.2.1 i u).1) hp.2.2.1
    (rebuilt_zero s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N
      (fun u => (F.solution.value_bounds u).1))
    (fun t ht i x w => rebuilt_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall
      hq (by positivity) hL hT hR (hTmax.trans (by norm_num)) le_rfl N hh₀
      F.solution.measurable_value F.solution.value_bounds F.initial_bound i ht
      (JetPeriodicDatum.spatialMap x,w))
    F.solution.periodic (fun n i => rebuilt_shift n (F.solution.periodic n) i) hreg.1.measurable
  filter_upwards [hν] with u hu ht
  apply (hu ht).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_right
    (add_le_add (hreg.2 u.1 ⟨ht.1.le,ht.2⟩) le_rfl) (hotConstant_nonneg q)) le_rfl

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Integrable velocity majorants for rescaled hot transport sources -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_abs_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hg : Integrable g μ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ g x) : UniformIntegrable f 1 μ := by
  have hb (n) : ∀ᵐ x ∂μ, ‖f n x‖ₑ ≤ ‖g x‖ₑ := by
    filter_upwards [hfg n] with x hx
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_eq_abs,Real.norm_of_nonneg ((abs_nonneg _).trans hx)]
    exact hx
  have hc : UniformIntegrable (fun _ : ℕ => g) 1 μ :=
    uniformIntegrable_const (by norm_num) (by norm_num) (memLp_one_iff_integrable.mpr hg)
  obtain ⟨hu,C,hC⟩ := hc
  exact ⟨hu.ae_mono hf hb,C,fun n => (eLpNorm_mono_enorm_ae (hf n) (hb n)).trans (hC n)⟩

end BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem sourceEnvelope_integrable {q : ℝ} (hq : q < 2) (s₀ η K α γ d₀ a A : ℝ) :
    Integrable (fun v : Velocity => sourceEnvelope s₀ η K α γ d₀ q a A v*H q v) := by
  have hv : Integrable (fun v : Velocity => ‖v‖*H q v) := by
    simpa only [pow_one] using integrable_moment_H hq 1
  have he : Integrable (fun v : Velocity => (‖v‖+1)*H q v) := by
    apply (hv.add (integrable_H hq)).congr
    exact ae_of_all _ (fun v => by
      change ‖v‖*H q v+H q v = (‖v‖+1)*H q v
      ring)
  have h := ((integrable_H hq).const_mul (2*JetMainGain.coefficient K α γ q+1)).add
    (he.const_mul (2*Real.pi*lossEnvelope s₀ η K α γ d₀ q a A))
  convert h using 1
  funext v
  simp only [sourceEnvelope,Pi.add_apply]
  ring

theorem sourceEnvelope_window_integrable {q : ℝ} (hq : q < 2) (s₀ η K α γ d₀ a A R : ℝ) :
    Integrable (fun z : HotKineticPhase => sourceEnvelope s₀ η K α γ d₀ q a A z.2*H q z.2)
      (hotWindowVolume A R) := by
  unfold hotWindowVolume
  have : IsFiniteMeasure ((volume : Measure JetPrototype.Space).restrict
      (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : JetPrototype.Space) R).measure_lt_top.ne
  exact (sourceEnvelope_integrable hq s₀ η K α γ d₀ a A).comp_snd _

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform integrability of the actual hot sources on positive-time windows -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def hotSourceDensity (S : AttainedCapSequence F) (a A : ℝ) (n : ℕ)
    (z : HotKineticPhase) : ℝ :=
  {z : HotKineticPhase | z.1.1 ∈ Icc a A}.indicator
    (fun z => H q z.2*S.rescaledHotSource n (z.1.1,(z.1.2,z.2))) z

theorem hotSourceDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (a A : ℝ) (n : ℕ) :
    Measurable (S.hotSourceDensity a A n) := by
  have hm := (F.approximation n).hotNetSource_measurable hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le
  exact (((ChartKernel.measurable_H q).comp measurable_snd).mul
    (hm.comp (by fun_prop))).indicator (measurableSet_Icc.preimage measurable_fst.fst)

theorem eventually_hotSourceDensity_bound (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) (R : ℝ) :
    ∀ᶠ n in atTop, ∀ᵐ z ∂hotWindowVolume A R,
      |S.hotSourceDensity a A (κ n) z| ≤ sourceEnvelope s₀ η K α γ d₀ q a A z.2*H q z.2 := by
  have hD := lossEnvelope_nonneg hs₀ hK hd₀ η α γ q ha (ha.le.trans haA)
  have hmajor (v : Velocity) : 0 ≤ sourceEnvelope s₀ η K α γ d₀ q a A v := by
    unfold sourceEnvelope
    have := JetMainGain.coefficient_nonneg hK α γ q
    have := mul_nonneg (by positivity : 0 ≤ 2*Real.pi*(‖v‖+1)) hD
    linarith
  filter_upwards [S.eventually_rescaledHotSource_abs hcarleman hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA] with n hn
  have hg : ∀ᵐ z ∂(volume : Measure HotKineticPhase), z.1.1 ∈ Icc a A →
      |S.rescaledHotSource (κ n) (z.1.1,(z.1.2,z.2))| ≤
        sourceEnvelope s₀ η K α γ d₀ q a A z.2 := by
    have hh := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure JetPrototype.Space)
      (volume : Measure Velocity)).quasiMeasurePreserving.ae hn
    change ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure JetPrototype.Space)).prod
      (volume : Measure Velocity), z.1.1 ∈ Icc a A →
        |S.rescaledHotSource (κ n) (z.1.1,(z.1.2,z.2))| ≤
          sourceEnvelope s₀ η K α γ d₀ q a A z.2 at hh
    simpa only [Measure.volume_eq_prod] using hh
  rw [hotWindowVolume_eq]
  filter_upwards [hg.filter_mono ae_restrict_le] with z hz
  by_cases ht : z.1.1 ∈ Icc a A
  · rw [hotSourceDensity,indicator_of_mem (show z ∈ {z : HotKineticPhase | z.1.1 ∈ Icc a A} from ht),abs_mul,abs_of_nonneg (H_nonneg q z.2)]
    exact (mul_le_mul_of_nonneg_left (hz ht) (H_nonneg q z.2)).trans_eq (mul_comm _ _)
  · rw [hotSourceDensity,indicator_of_notMem (show z ∉ {z : HotKineticPhase | z.1.1 ∈ Icc a A} from ht),abs_zero]
    exact mul_nonneg (hmajor z.2) (H_nonneg q z.2)

theorem hotSourceDensity_uniformIntegrable_tail (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) (R : ℝ) :
    ∃ N : ℕ, UniformIntegrable (fun n => S.hotSourceDensity a A (κ (n+N))) 1
      (hotWindowVolume A R) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (S.eventually_hotSourceDensity_bound hcarleman hs₀ hsmax
    hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA R)
  refine ⟨N,Compactness.uniformIntegrable_of_abs_le
    (sourceEnvelope_window_integrable hq₂ s₀ η K α γ d₀ a A R) ?_ ?_⟩
  · intro n
    exact (S.hotSourceDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ a A _).aestronglyMeasurable
  · intro n
    exact hN (n+N) (Nat.le_add_left N n)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
