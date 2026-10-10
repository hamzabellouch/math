import Mathlib
import OAI.Probability.SLELocalization.LoewnerFlow
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI


/-! Conformal localization and Loewner Localized estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.LoewnerLocalized
open LoewnerCutoff LoewnerExit LoewnerField
open scoped unitInterval
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)

lemma source_until_stop (h : IsLoewnerTraceUsing driver γ g f)
    (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (h0 : 0 < deficit hε hT.le U z ρ δ 0) :
    z ∈ localizationDomain γ (stop hε hT.le U z ρ δ) ∧
      EqOn (fun s => g s z) (position hε hT.le U z) (Icc 0 (stop hε hT.le U z ρ δ)) := by
  have hb := stop_bounds hε hT.le U z ρ δ
  have hh := h.cutoff_solution_live hε hb.1 (H := position hε hT.le U z) ?_ ?_
  · simpa only [position_initial] using hh
  · intro t ht
    rw [← hU ⟨ht.1,ht.2.trans hb.2⟩]
    exact (position_derivWithin hε hT.le U z ⟨ht.1,ht.2.trans hb.2⟩).mono
      (Icc_subset_Icc le_rfl hb.2)
  · intro t ht
    exact ((deficit_nonneg_iff hε hT.le U z ρ δ t).1
      (nonneg_until hε hT.le hT U z ρ δ h0 ht)).2.1

lemma logDerivative_eq_source (h : IsLoewnerTraceUsing driver γ g f)
    (hcont : ContinuousOn driver (Icc 0 T))
    (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (h0 : 0 < deficit hε hT.le U z ρ δ 0) {t : ℝ}
    (ht : t ∈ Icc 0 (stop hε hT.le U z ρ δ)) :
    logDerivative hε hT.le U z t = Real.log ‖deriv (g t) z‖ := by
  have hb := stop_bounds hε hT.le U z ρ δ
  have hs := source_until_stop hε hT h U z ρ δ hU h0
  have hz := survivingDomain_mono ht.2 hs.1
  have hu := hcont.mono (Icc_subset_Icc le_rfl (ht.2.trans hb.2))
  rw [logDerivative_eq_integral hε hT.le U z ⟨ht.1,ht.2.trans hb.2⟩,
    h.log_deriv_norm_eq ht.1 hu hz]
  have hi := (h.continuous_spatialCoefficient ht.1 hu hz).intervalIntegrable_of_Icc (μ := volume) ht.1
  rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro s hst
  rw [uIcc_of_le ht.1] at hst
  have hss : s ∈ Icc 0 (stop hε hT.le U z ρ δ) := ⟨hst.1,hst.2.trans ht.2⟩
  have hh := ((deficit_nonneg_iff hε hT.le U z ρ δ s).1
    (nonneg_until hε hT.le hT U z ρ δ h0 hss)).2.1
  unfold variation
  rw [clampIm_eq (by simpa using hh)]
  simp only [← hs.2 hss, hU ⟨hst.1,hss.2.trans hb.2⟩, Complex.reCLM_apply]

lemma radius_eq_source (h : IsLoewnerTraceUsing driver γ g f)
    (hcont : ContinuousOn driver (Icc 0 T))
    (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (h0 : 0 < deficit hε hT.le U z ρ δ 0) {t : ℝ}
    (ht : t ∈ Icc 0 (stop hε hT.le U z ρ δ)) :
    radius hε hT.le U z t = loewnerRadius g t z := by
  have hs := source_until_stop hε hT h U z ρ δ hU h0
  rw [radius, logDerivative_eq_source hε hT h hcont U z ρ δ hU h0 ht,
    Real.exp_log (norm_pos_iff.2 (h.deriv_ne_zero ht.1 (survivingDomain_mono ht.2 hs.1))),
    ← hs.2 ht]
  rfl

lemma sine_eq_source (h : IsLoewnerTraceUsing driver γ g f)
    (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (h0 : 0 < deficit hε hT.le U z ρ δ 0) {t : ℝ}
    (ht : t ∈ Icc 0 (stop hε hT.le U z ρ δ)) :
    sine hε hT.le U z t = (g t z).im / ‖g t z - (driver t : ℂ)‖ := by
  have hs := source_until_stop hε hT h U z ρ δ hU h0
  have hh := ((deficit_nonneg_iff hε hT.le U z ρ δ t).1
    (nonneg_until hε hT.le hT U z ρ δ h0 ht)).2.1
  rw [sine, clampIm_eq (by simpa using hh), ← hs.2 ht,
    hU ⟨ht.1,ht.2.trans (stop_bounds hε hT.le U z ρ δ).2⟩]

end SLEExactGauge.LoewnerLocalized

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.LoewnerLocalized
open LoewnerCutoff LoewnerExit LoewnerField GreenPhysical
open scoped unitInterval
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)

lemma field_eq_radius_sine (p a sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ)
    (hy : ε ≤ (position hε hT.le U z t).im)
    (hU : extendDriver T U t = sdev*b) :
    field hε hT.le p a sdev U z t b =
      (radius hε hT.le U z t)^(-p) * (sine hε hT.le U z t)^a := by
  rw [field, green_eq_source _ _ _ _ _ (height_pos hε hT.le U z t)]
  have hh : height hε hT.le U z t = (position hε hT.le U z t).im := max_eq_right hy
  rw [hh, radius, sine, clampIm_eq (by simpa using hy), hU]
  simp only [Complex.norm_def, Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
    Complex.sub_im, Complex.ofReal_im, sub_zero, pow_two]

lemma clock_bounds_stop (h : IsLoewnerTraceUsing driver γ g f)
    (hcont : ContinuousOn driver (Icc 0 T))
    (U : C(I, ℝ)) (z : ℂ) (u δ : ℝ) (hδ : 0 < δ)
    (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (h0 : 0 < deficit hε hT.le U z ((2*z.im)*Real.exp (-u)) δ 0) :
    z.im*Real.exp (-u/(2*δ^2)) ≤ (position hε hT.le U z
      (stop hε hT.le U z ((2*z.im)*Real.exp (-u)) δ)).im ∧
      stop hε hT.le U z ((2*z.im)*Real.exp (-u)) δ ≤ u*z.im^2/(4*δ^4) := by
  let ρ := (2*z.im)*Real.exp (-u)
  let τ := stop hε hT.le U z ρ δ
  have hb : τ ∈ Icc 0 T := stop_bounds hε hT.le U z ρ δ
  have hs := source_until_stop hε hT h U z ρ δ hU h0
  have ha (t : ℝ) (ht : t ∈ Icc 0 τ) : δ ≤ (g t z).im / ‖g t z - (driver t : ℂ)‖ := by
    rw [← sine_eq_source hε hT h U z ρ δ hU h0 ht]
    exact ((deficit_nonneg_iff hε hT.le U z ρ δ t).1
      (nonneg_until hε hT.le hT U z ρ δ h0 ht)).2.2
  have hc := h.finite_clock_bounds (u := u) hb.1 hδ (hcont.mono (Icc_subset_Icc le_rfl hb.2)) hs.1 ?_ ?_
  · have heq : g τ z = position hε hT.le U z τ := hs.2 ⟨hb.1,le_rfl⟩
    rw [heq] at hc
    exact hc
  · intro t ht
    have hz := survivingDomain_mono ht.2.le hs.1
    have hnorm : 0 < ‖g t z - (driver t : ℂ)‖ := norm_pos_iff.2 (h.centered_ne_zero ht.1.le hz)
    have hq : δ * ‖g t z - (driver t : ℂ)‖ ≤ (g t z).im :=
      (le_div_iff₀ hnorm).1 (ha t ⟨ht.1.le,ht.2.le⟩)
    simpa only [mul_pow, Complex.normSq_eq_norm_sq] using
      pow_le_pow_left₀ (mul_nonneg hδ.le hnorm.le) hq 2
  · rw [← radius_eq_source hε hT h hcont U z ρ δ hU h0 ⟨hb.1,le_rfl⟩]
    exact ((deficit_nonneg_iff hε hT.le U z ρ δ τ).1
      (nonneg_until hε hT.le hT U z ρ δ h0 ⟨hb.1,le_rfl⟩)).1

lemma terminal_cases (h : IsLoewnerTraceUsing driver γ g f)
    (hcont : ContinuousOn driver (Icc 0 T))
    (U : C(I, ℝ)) (z : ℂ) (u δ : ℝ) (hδ : 0 < δ)
    (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (h0 : 0 < deficit hε hT.le U z ((2*z.im)*Real.exp (-u)) δ 0)
    (hsmall : ε < z.im*Real.exp (-u/(2*δ^2)))
    (hlarge : u*z.im^2/(4*δ^4) < T) :
    let ρ := (2*z.im)*Real.exp (-u)
    let τ := stop hε hT.le U z ρ δ
    radius hε hT.le U z τ = ρ ∨ sine hε hT.le U z τ = δ := by
  dsimp only
  let ρ := (2*z.im)*Real.exp (-u)
  let τ := stop hε hT.le U z ρ δ
  have hb : τ ∈ Icc 0 T := stop_bounds hε hT.le U z ρ δ
  have hc := clock_bounds_stop hε hT h hcont U z u δ hδ hU h0
  have hn := nonpos_at_of_lt hε hT.le hT U z ρ δ (hc.2.trans_lt hlarge)
  have hp := (deficit_nonneg_iff hε hT.le U z ρ δ τ).1
    (nonneg_until hε hT.le hT U z ρ δ h0 ⟨hb.1,le_rfl⟩)
  by_contra he
  push Not at he
  have hh : 0 < deficit hε hT.le U z ρ δ τ :=
    (deficit_pos_iff hε hT.le U z ρ δ τ).2
      ⟨lt_of_le_of_ne hp.1 (Ne.symm he.1),hsmall.trans_le hc.1,
        lt_of_le_of_ne hp.2.2 (Ne.symm he.2)⟩
  exact (not_lt_of_ge hn) hh

end SLEExactGauge.LoewnerLocalized

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.FiniteTilt
open LoewnerCutoff LoewnerExit LoewnerField LoewnerLocalized GreenPhysical
open scoped unitInterval

structure Cutoff (z : ℂ) (u : ℝ) where
  angle : ℝ
  angle_pos : 0 < angle
  angle_initial : angle < z.im / ‖z‖
  height : ℝ
  height_pos : 0 < height
  horizon : ℝ≥0
  horizon_pos : 0 < (horizon:ℝ)
  height_small : height < z.im * Real.exp (-u/(2*angle^2))
  time_large : u*z.im^2/(4*angle^4) < horizon

end SLEExactGauge.FiniteTilt

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.FiniteTilt
open LoewnerCutoff LoewnerExit LoewnerField LoewnerLocalized GreenPhysical
open scoped unitInterval
namespace Cutoff
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)

lemma height_initial (hz : z ∈ halfPlane) (hu : 0 ≤ u) : C.height < z.im := by
  have he : Real.exp (-u/(2*C.angle^2)) ≤ 1 := Real.exp_le_one_iff.2
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hu) (by positivity))
  exact C.height_small.trans_le (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hz.le)

lemma initial_deficit (hz : z ∈ halfPlane) (hu : 0 < u) (V : C(I, ℝ))
    (hV0 : extendDriver C.horizon V 0 = 0) :
    0 < deficit C.height_pos C.horizon.coe_nonneg V z ((2*z.im)*Real.exp (-u)) C.angle 0 := by
  apply (deficit_pos_iff _ _ _ _ _ _ _).2
  have hy0 : 0 < z.im := hz
  have hy := C.height_initial hz hu.le
  have hr : (2*z.im)*Real.exp (-u) < 2*z.im := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left
      (Real.exp_lt_one_iff.2 (neg_neg_of_pos hu)) (show 0 < 2*z.im by positivity)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [LoewnerExit.radius, position_initial, logDerivative_initial, Real.exp_zero, div_one] using hr
  · simpa only [position_initial] using hy
  · simpa only [LoewnerExit.sine, position_initial, hV0, Complex.ofReal_zero, sub_zero,
      clampIm_eq hy.le] using C.angle_initial

def paths {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) : Ω → C(I, ℝ) :=
  BrownianDriver.path B (Real.sqrt κ) C.horizon

def stopTime {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) : ℝ :=
  stop C.height_pos C.horizon.coe_nonneg (C.paths κ B sample) z ((2*z.im)*Real.exp (-u)) C.angle

def value {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) : ℝ :=
  field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (C.paths κ B sample) z
    (C.stopTime κ B sample) (B (C.stopTime κ B sample).toNNReal sample)

lemma path_eq {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) :
    EqOn (extendDriver C.horizon (C.paths κ B sample)) (fun t => Real.sqrt κ*B t.toNNReal sample)
      (Icc 0 (C.horizon:ℝ)) := by
  intro t ht
  exact BrownianDriver.extend_eq B (Real.sqrt κ) C.horizon sample hc ht

lemma initial_deficit_brownian {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    (hz : z ∈ halfPlane) (hu : 0 < u)
    (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0) :
    0 < deficit C.height_pos C.horizon.coe_nonneg (C.paths κ B sample) z
      ((2*z.im)*Real.exp (-u)) C.angle 0 := by
  apply C.initial_deficit hz hu
  simpa only [Real.toNNReal_zero, hb0, mul_zero] using
    C.path_eq κ B sample hc ⟨le_rfl,C.horizon.coe_nonneg⟩

lemma bounds {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) :
    C.stopTime κ B sample ∈ Icc 0 (C.horizon:ℝ) :=
  stop_bounds C.height_pos C.horizon.coe_nonneg _ z _ C.angle

lemma value_nonneg {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) :
    0 ≤ C.value κ B sample := (green_pos _ _ _ _ _).le

lemma value_bound {Ω : Type*} (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (sample : Ω) (hz : z ∈ halfPlane) (hu : 0 < u)
    (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0) :
    C.value κ B sample ≤ ((2*z.im)*Real.exp (-u))^(-(1-κ/8)) := by
  have hy0 : 0 < z.im := hz
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := sub_nonneg.2 ((le_div_iff₀ hκ.1).2 (by simpa using hκ.2.le))
  have h0 := C.initial_deficit_brownian κ B sample hz hu hc hb0
  have hd := (deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle _).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle h0
      ⟨(C.bounds κ B sample).1,le_rfl⟩)
  apply green_le_fixed_radius _ _ _ _ _ _ (LoewnerField.height_pos _ _ _ _ _) ha hp (by positivity)
  simpa only [LoewnerExit.radius, LoewnerField.height, max_eq_right hd.2.1] using hd.1

lemma expectation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (hz : z ∈ halfPlane) (hu : 0 ≤ u) :
    Integrable (C.value κ B) P ∧ (∫ sample, C.value κ B sample ∂P) =
      green (1-κ/8) (8/κ-1) z.re z.im 0 :=
  localized_expectation hB κ hκ C.height_pos C.horizon C.horizon_pos z (C.height_initial hz hu).le _ C.angle

end Cutoff

end SLEExactGauge.FiniteTilt

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.FiniteTilt
open scoped unitInterval

lemma initial_sine_pos {z : ℂ} (hz : z ∈ halfPlane) : 0 < z.im/‖z‖ := by
  have hy : 0 < z.im := hz
  have hne : z ≠ 0 := by
    intro he
    simp only [he, Complex.zero_im, lt_self_iff_false] at hy
  exact div_pos hy (norm_pos_iff.2 hne)

def shrinkingAngle (z : ℂ) (n : ℕ) : ℝ := (z.im/‖z‖)/((n:ℝ)+2)

lemma shrinkingAngle_pos {z : ℂ} (hz : z ∈ halfPlane) (n : ℕ) :
    0 < shrinkingAngle z n := div_pos (initial_sine_pos hz) (by positivity)

lemma shrinkingAngle_initial {z : ℂ} (hz : z ∈ halfPlane) (n : ℕ) :
    shrinkingAngle z n < z.im/‖z‖ := by
  apply div_lt_self (initial_sine_pos hz)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

lemma shrinkingAngle_tendsto (z : ℂ) : Tendsto (shrinkingAngle z) atTop (𝓝 0) := by
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (z.im/‖z‖)).comp (tendsto_add_atTop_nat 2)
  change Tendsto (fun n : ℕ => (z.im/‖z‖)/((n:ℝ)+2)) atTop (𝓝 0)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using ht

def cutoffs {z : ℂ} (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 ≤ u) (n : ℕ) : Cutoff z u where
  angle := shrinkingAngle z n
  angle_pos := shrinkingAngle_pos hz n
  angle_initial := shrinkingAngle_initial hz n
  height := z.im*Real.exp (-u/(2*(shrinkingAngle z n)^2))/2
  height_pos := by have hy : 0 < z.im := hz; positivity
  horizon := ⟨u*z.im^2/(4*(shrinkingAngle z n)^4)+1, by positivity⟩
  horizon_pos := by change 0 < u*z.im^2/(4*(shrinkingAngle z n)^4)+1; positivity
  height_small := by
    have he := mul_pos (show 0 < z.im from hz) (Real.exp_pos (-u/(2*(shrinkingAngle z n)^2)))
    linarith
  time_large := by
    change u*z.im^2/(4*(shrinkingAngle z n)^4) < u*z.im^2/(4*(shrinkingAngle z n)^4)+1
    linarith

end SLEExactGauge.FiniteTilt

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerExit LoewnerField LoewnerLocalized GreenPhysical
open scoped unitInterval
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
variable {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
variable (hz : z ∈ halfPlane) (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
include h hz hu hc hb0

lemma source_live : z ∈ localizationDomain γ (C.stopTime κ B sample) := by
  exact (source_until_stop C.height_pos C.horizon_pos h _ z _ C.angle
    (C.path_eq κ B sample hc) (C.initial_deficit_brownian κ B sample hz hu hc hb0)).1

lemma source_radius : radius C.height_pos C.horizon.coe_nonneg (C.paths κ B sample) z
    (C.stopTime κ B sample) = loewnerRadius g (C.stopTime κ B sample) z := by
  exact radius_eq_source C.height_pos C.horizon_pos h
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) _ z _ C.angle
    (C.path_eq κ B sample hc) (C.initial_deficit_brownian κ B sample hz hu hc hb0)
    ⟨(C.bounds κ B sample).1,le_rfl⟩

lemma source_sine : sine C.height_pos C.horizon.coe_nonneg (C.paths κ B sample) z
    (C.stopTime κ B sample) = loewnerAngleSine κ (fun t => B t sample) g
      (C.stopTime κ B sample) z := by
  unfold loewnerAngleSine
  simpa only [Complex.ofReal_mul] using sine_eq_source C.height_pos C.horizon_pos h _ z _ C.angle
    (C.path_eq κ B sample hc) (C.initial_deficit_brownian κ B sample hz hu hc hb0)
    ⟨(C.bounds κ B sample).1,le_rfl⟩

lemma radius_lower : (2*z.im)*Real.exp (-u) ≤ loewnerRadius g (C.stopTime κ B sample) z := by
  rw [← C.source_radius κ B sample h hz hu hc hb0]
  exact ((deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle _).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle
      (C.initial_deficit_brownian κ B sample hz hu hc hb0) ⟨(C.bounds κ B sample).1,le_rfl⟩)).1

lemma value_eq_source : C.value κ B sample =
    (loewnerRadius g (C.stopTime κ B sample) z)^(-(1-κ/8)) *
      (loewnerAngleSine κ (fun t => B t sample) g (C.stopTime κ B sample) z)^(8/κ-1) := by
  have hh := ((deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle _).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle
      (C.initial_deficit_brownian κ B sample hz hu hc hb0) ⟨(C.bounds κ B sample).1,le_rfl⟩)).2.1
  rw [Cutoff.value, field_eq_radius_sine C.height_pos C.horizon_pos _ _ _ _ z _ _ hh
    (C.path_eq κ B sample hc (C.bounds κ B sample)),
    C.source_radius κ B sample h hz hu hc hb0, C.source_sine κ B sample h hz hu hc hb0]

lemma source_terminal : loewnerRadius g (C.stopTime κ B sample) z = (2*z.im)*Real.exp (-u) ∨
    loewnerAngleSine κ (fun t => B t sample) g (C.stopTime κ B sample) z = C.angle := by
  have hh := terminal_cases C.height_pos C.horizon_pos h
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
    (C.paths κ B sample) z u C.angle C.angle_pos (C.path_eq κ B sample hc)
    (C.initial_deficit_brownian κ B sample hz hu hc hb0) C.height_small C.time_large
  change radius _ _ _ _ (C.stopTime κ B sample) = _ ∨
    sine _ _ _ _ (C.stopTime κ B sample) = _ at hh
  rwa [C.source_radius κ B sample h hz hu hc hb0, C.source_sine κ B sample h hz hu hc hb0] at hh

lemma stopTime_le_radius {t : ℝ} (ht : 0 ≤ t) (_hzt : z ∈ localizationDomain γ t)
    (hrt : loewnerRadius g t z = (2*z.im)*Real.exp (-u)) : C.stopTime κ B sample ≤ t := by
  by_contra hn
  have hlt : t < C.stopTime κ B sample := lt_of_not_ge hn
  have ha := h.radius_strictAnti (C.bounds κ B sample).1
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
    (C.source_live κ B sample h hz hu hc hb0) ⟨ht,hlt.le⟩ ⟨(C.bounds κ B sample).1,le_rfl⟩ hlt
  dsimp only at ha
  rw [hrt] at ha
  exact (not_lt_of_ge (C.radius_lower κ B sample h hz hu hc hb0)) ha

lemma angle_exit_bound (hκ : 0 < κ ∧ κ < 8)
    (he : loewnerAngleSine κ (fun t => B t sample) g (C.stopTime κ B sample) z = C.angle) :
    C.value κ B sample ≤ ((2*z.im)*Real.exp (-u))^(-(1-κ/8))*C.angle^(8/κ-1) := by
  rw [C.value_eq_source κ B sample h hz hu hc hb0, he]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg C.angle_pos.le _)
  exact Real.rpow_le_rpow_of_nonpos (by have hy : 0 < z.im := hz; positivity)
    (C.radius_lower κ B sample h hz hu hc hb0) (by linarith [hκ.2])

end SLEExactGauge.FiniteTilt.Cutoff

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.IsLoewnerTraceUsing
variable {κ : ℝ} {B : ℝ≥0 → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma sine_positive_minimum (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ * B t.toNNReal) γ g f)
    (hc : Continuous B) {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ∃ η : ℝ, 0 < η ∧ ∀ t ∈ Icc 0 T, η ≤ loewnerAngleSine κ B g t z := by
  have hgc := h.continuous_eval hT hz
  have hdc : Continuous (fun t : ℝ => ((Real.sqrt κ * B t.toNNReal : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.mul (hc.comp continuous_real_toNNReal))
  have hnum := Complex.continuous_im.comp_continuousOn hgc
  have hden := (hgc.sub hdc.continuousOn).norm
  have hn (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖g t z - ((Real.sqrt κ * B t.toNNReal : ℝ) : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (h.centered_ne_zero ht.1 (survivingDomain_mono ht.2 hz))
  have hx := hnum.div hden hn
  have hct : ContinuousOn (fun t => loewnerAngleSine κ B g t z) (Icc 0 T) := by
    apply hx.congr
    intro t ht
    simp only [loewnerAngleSine, Function.comp_def, Complex.ofReal_mul, Pi.div_apply, Pi.sub_apply]
  obtain ⟨t, ht, hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hct
  refine ⟨loewnerAngleSine κ B g t z, ?_, hm⟩
  have hh := div_pos (h.im_pos ht.1 (survivingDomain_mono ht.2 hz))
    (norm_pos_iff.2 (h.centered_ne_zero ht.1 (survivingDomain_mono ht.2 hz)))
  simpa only [loewnerAngleSine, Complex.ofReal_mul] using hh

end SLEExactGauge.IsLoewnerTraceUsing

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.FiniteTilt
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
variable {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
variable {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
include h hz hu hc hb0

lemma eventually_value_at_radius {t : ℝ≥0} (hzt : z ∈ localizationDomain γ t)
    (hrt : loewnerRadius g t z = (2*z.im)*Real.exp (-u)) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((cutoffs hz u hu.le n).value κ B sample) =
      finiteStoppedDensity κ (fun t => B t sample) γ g z u := by
  obtain ⟨η, hη, hm⟩ := h.sine_positive_minimum (κ := κ) (B := fun t => B t sample) hc t.coe_nonneg hzt
  have hδ : ∀ᶠ n : ℕ in atTop, shrinkingAngle z n < η :=
    (shrinkingAngle_tendsto z).eventually (gt_mem_nhds hη)
  filter_upwards [hδ] with n hn
  let C := cutoffs hz u hu.le n
  have hh : loewnerRadius g (C.stopTime κ B sample) z = (2*z.im)*Real.exp (-u) := by
    rcases C.source_terminal κ B sample h hz hu hc hb0 with hr | hs
    · exact hr
    · have htm := hm (C.stopTime κ B sample)
        ⟨(C.bounds κ B sample).1,C.stopTime_le_radius κ B sample h hz hu hc hb0 t.coe_nonneg hzt hrt⟩
      rw [hs] at htm
      exact False.elim ((not_lt_of_ge htm) hn)
  have he : C.stopTime κ B sample = t := h.live_radius_injective
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
    (C.bounds κ B sample).1 t.coe_nonneg (C.source_live κ B sample h hz hu hc hb0) hzt
    (hh.trans hrt.symm)
  have htau := h.firstLiveRadiusStop_eq
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) hzt hrt
  have hp : codimension κ = 1-κ/8 := by unfold codimension dimension; ring
  rw [finiteStoppedDensity, htau, ite_eq_right (ENNReal.coe_ne_top), ENNReal.coe_toReal, hp,
    ← he, ← C.value_eq_source κ B sample h hz hu hc hb0]

lemma tendsto_value_killed (hκ : 0 < κ ∧ κ < 8) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((cutoffs hz u hu.le n).value κ B sample)) atTop
      (𝓝 (finiteStoppedDensity κ (fun t => B t sample) γ g z u)) := by
  by_cases he : ∃ t : ℝ≥0, z ∈ localizationDomain γ t ∧
      loewnerRadius g t z = (2*z.im)*Real.exp (-u)
  · obtain ⟨t, hzt, hrt⟩ := he
    have hh : (fun n : ℕ => ENNReal.ofReal ((cutoffs hz u hu.le n).value κ B sample)) =ᶠ[atTop]
        (fun _ => finiteStoppedDensity κ (fun t => B t sample) γ g z u) :=
      eventually_value_at_radius κ B sample h hz hu hc hb0 hzt hrt
    exact tendsto_const_nhds.congr' hh.symm
  · have hset : {t : ℝ≥0 | z ∈ localizationDomain γ t ∧
        loewnerRadius g t z = (2*z.im)*Real.exp (-u)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro t ht
      exact he ⟨t,ht⟩
    have htau : firstLiveRadiusStop γ g z u = (⊤ : ℝ≥0∞) := by
      simp only [firstLiveRadiusStop, hset, Set.image_empty, sInf_empty]
    rw [finiteStoppedDensity, htau, ite_eq_left rfl]
    have ha : 0 < 8/κ-1 := sub_pos.2 ((lt_div_iff₀ hκ.1).2 (by simpa using hκ.2))
    have hlim := (shrinkingAngle_tendsto z).rpow_const_nhds_zero ha
    have hlim' : Tendsto (fun n : ℕ => ((2*z.im)*Real.exp (-u))^(-(1-κ/8)) *
        (shrinkingAngle z n)^(8/κ-1)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlim
    have hl : Tendsto (fun n : ℕ => (cutoffs hz u hu.le n).value κ B sample) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => (cutoffs hz u hu.le n).value_nonneg κ B sample) _ hlim'
      intro n
      let C := cutoffs hz u hu.le n
      have hs : loewnerAngleSine κ (fun t => B t sample) g (C.stopTime κ B sample) z = C.angle := by
        rcases C.source_terminal κ B sample h hz hu hc hb0 with hr | hs
        · exact False.elim (he ⟨⟨C.stopTime κ B sample,(C.bounds κ B sample).1⟩,
            C.source_live κ B sample h hz hu hc hb0, hr⟩)
        · exact hs
      exact C.angle_exit_bound κ B sample h hz hu hc hb0 hκ hs
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl

end SLEExactGauge.FiniteTilt

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge
open FiniteTilt GreenPhysical

lemma finiteStoppedDensity_zero {κ : ℝ} {B : ℝ≥0 → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal) γ g f)
    (hb0 : B 0 = 0) {z : ℂ} (hz : z ∈ halfPlane) :
    finiteStoppedDensity κ B γ g z 0 =
      ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)) := by
  rw [finiteStoppedDensity, firstLiveRadiusStop_zero h hz, ite_eq_right ENNReal.zero_ne_top,
    ENNReal.toReal_zero, h.radius_initial hz]
  simp only [loewnerAngleSine, h.initial z hz, Real.toNNReal_zero, hb0, mul_zero,
    Complex.ofReal_zero, sub_zero]

lemma green_initial (κ : ℝ) {z : ℂ} (hz : z ∈ halfPlane) :
    green (1-κ/8) (8/κ-1) z.re z.im 0 =
      (2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1) := by
  have hp : codimension κ = 1-κ/8 := by unfold codimension dimension; ring
  rw [green_eq_source _ _ _ _ _ hz, Real.exp_zero, div_one, hp]
  congr 3
  rw [Complex.norm_eq_sqrt_sq_add_sq]

theorem finiteStoppedCenteredLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 ≤ u) :
    (∫⁻ sample, finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∂P) =
      ENNReal.ofReal ((2 * z.im) ^ (-codimension κ) *
        (z.im / ‖z‖) ^ (8 / κ - 1)) := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · have he : (fun sample => finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z 0) =ᵐ[P]
        (fun _ => ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))) := by
      filter_upwards [hmaps,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hb
      exact finiteStoppedDensity_zero (κ := κ) (B := fun t => B t sample) hm hb hz
    rw [lintegral_congr_ae he, lintegral_const, measure_univ, mul_one]
  · let C := cutoffs hz u hu.le
    let F := fun n sample => ENNReal.ofReal ((C n).value κ B sample)
    have hexp (n : ℕ) := (C n).expectation hB κ hκ hz hu.le
    have hFm (n : ℕ) : AEMeasurable (F n) P :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hexp n).1.aemeasurable
    have hFb (n : ℕ) : ∀ᵐ sample ∂P, F n sample ≤ ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8))) := by
      filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hc hb
      exact ENNReal.ofReal_le_ofReal ((C n).value_bound κ hκ B sample hz hu hc hb)
    have hFl : ∀ᵐ sample ∂P, Tendsto (fun n => F n sample) atTop
        (𝓝 (finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u)) := by
      filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hc hb
      exact tendsto_value_killed κ B sample hm hz hu hc hb hκ
    have hfin : (∫⁻ _ : Ω, ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8))) ∂P) ≠ (⊤ : ℝ≥0∞) := by
      rw [lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_ne_top
    have hdct := tendsto_lintegral_of_dominated_convergence'
      (fun _ : Ω => ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8)))) hFm hFb hfin hFl
    have hint (n : ℕ) : (∫⁻ sample, F n sample ∂P) = ENNReal.ofReal (green (1-κ/8) (8/κ-1) z.re z.im 0) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hexp n).1
        (Filter.Eventually.of_forall (fun sample => (C n).value_nonneg κ B sample)), (hexp n).2]
    simp only [hint] at hdct
    have he := tendsto_nhds_unique hdct tendsto_const_nhds
    rw [green_initial κ hz] at he
    exact he

end SLEExactGauge

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BoundaryFunctional

def clampRe (ε : ℝ) (w : ℂ) : ℂ := BoundaryCutoff.clamp 1 ε w

def velocity (ε u : ℝ) (w : ℂ) : ℂ := BoundaryCutoff.velocity 1 ε u w

lemma clampRe_ne_zero {ε : ℝ} (hε : 0 < ε) (w : ℂ) : clampRe ε w ≠ 0 :=
  BoundaryCutoff.clamp_ne_zero (by norm_num) hε w

lemma clampRe_norm {ε : ℝ} (hε : 0 < ε) (w : ℂ) : ε ≤ ‖clampRe ε w‖ :=
  BoundaryCutoff.clamp_norm (by norm_num) hε w

lemma clampRe_norm_sub (ε : ℝ) (z w : ℂ) : ‖clampRe ε z-clampRe ε w‖ ≤ 2*‖z-w‖ :=
  BoundaryCutoff.clamp_norm_sub (by norm_num) z w

lemma velocity_lipschitz {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    LipschitzWith ⟨4/ε^2,by positivity⟩ (velocity ε u) :=
  BoundaryCutoff.velocity_lipschitz (by norm_num) hε u

lemma norm_velocity_sub_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) (z w : ℂ) :
    ‖velocity ε u z-velocity ε u w‖ ≤ (4/ε^2)*‖z-w‖ :=
  BoundaryCutoff.norm_velocity_sub_le (by norm_num) hε u z w

lemma continuous_velocity {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℂ => velocity ε p.1 p.2) :=
  BoundaryCutoff.continuous_velocity (by norm_num) hε

lemma exists_solution {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hU : ContinuousOn U (Icc 0 T)) (z : ℂ) :
    ∃ H : ℝ → ℂ, H 0=z ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t :=
  BoundaryCutoff.exists_solution (by norm_num) hε hT U hU z

lemma norm_velocity_driver_sub_le {ε : ℝ} (hε : 0 < ε) (u v : ℝ) (z : ℂ) :
    ‖velocity ε u z - velocity ε v z‖ ≤ (4 / ε^2) * |u-v| := by
  have he (a : ℝ) : velocity ε 0 (z - (a : ℂ)) = velocity ε a z := by
    simp [velocity,BoundaryCutoff.velocity]
  have hh := norm_velocity_sub_le hε 0 (z-(u:ℂ)) (z-(v:ℂ))
  rw [he, he] at hh
  convert hh using 1
  rw [sub_sub_sub_cancel_left, ← Complex.ofReal_sub, Complex.norm_real, abs_sub_comm]
  simp [Real.norm_eq_abs]

lemma derivWithin_right {ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt H (velocity ε (U t) (H t)) (Ici t) t :=
  (hH t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

lemma derivWithin_left {ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    HasDerivWithinAt H (velocity ε (U t) (H t)) (Iic t) t :=
  (hH t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht)

lemma solution_eq {ε T : ℝ} (hε : 0 < ε) {U : ℝ → ℝ} {H G : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (velocity ε (U t) (G t)) (Icc 0 T) t)
    (h0 : H 0 = G 0) : EqOn H G (Icc 0 T) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (s := fun _ => univ) (fun t _ => (velocity_lipschitz hε (U t)).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hH) (fun _ ht => derivWithin_right hH ht)
    (fun _ _ => mem_univ _) (HasDerivWithinAt.continuousOn hG)
    (fun _ ht => derivWithin_right hG ht) (fun _ _ => mem_univ _) h0

lemma solution_dist_le {ε T D : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    {U V : ℝ → ℝ} {H G : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity ε (U t) (H t)) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (velocity ε (V t) (G t)) (Icc 0 T) t)
    (h0 : H 0 = G 0) (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ D)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (H t) (G t) ≤ D * Real.exp ((4 / ε^2) * T) := by
  let K : ℝ≥0 := ⟨4 / ε^2, by positivity⟩
  have hK : (0 : ℝ) < K := by change 0 < 4 / ε^2; positivity
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      dist (velocity ε (V s) (G s)) (velocity ε (U s) (G s)) ≤ (K : ℝ) * D := by
    rw [dist_eq_norm]
    calc
      _ ≤ (4 / ε^2) * |V s-U s| := norm_velocity_driver_sub_le hε _ _ _
      _ ≤ (K : ℝ) * D := by
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hUV s ⟨hs.1, hs.2.le⟩) hK.le
  have hh := dist_le_of_approx_trajectories_ODE
    (fun t => velocity_lipschitz hε (U t))
    (HasDerivWithinAt.continuousOn hH) (fun _ hs => derivWithin_right hH hs)
    (fun t _ => le_of_eq (dist_self (velocity ε (U t) (H t))))
    (HasDerivWithinAt.continuousOn hG) (fun _ hs => derivWithin_right hG hs)
    hb (le_of_eq (dist_eq_zero.2 h0)) t ht
  have he : gronwallBound 0 K (0 + (K : ℝ)*D) (t-0) =
      D * (Real.exp ((K : ℝ)*t)-1) := by
    simp only [gronwallBound, zero_add, sub_zero, ite_eq_right (ne_of_gt hK)]
    field_simp
    ring
  rw [he] at hh
  have hexp : Real.exp ((K : ℝ)*t) ≤ Real.exp ((K : ℝ)*T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK.le)
  apply hh.trans
  change D * (Real.exp ((4 / ε^2)*t)-1) ≤ D * Real.exp ((4 / ε^2)*T)
  change Real.exp ((4 / ε^2)*t) ≤ Real.exp ((4 / ε^2)*T) at hexp
  exact mul_le_mul_of_nonneg_left (by linarith) hD

end SLEExactGauge.BoundaryFunctional

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BoundaryFunctional
open scoped unitInterval

def extendDriver (T : ℝ) (U : C(I, ℝ)) (t : ℝ) : ℝ :=
  U (projIcc 0 1 zero_le_one (t / T))

lemma continuous_extendDriver (T : ℝ) (U : C(I, ℝ)) : Continuous (extendDriver T U) :=
  U.continuous.comp (continuous_projIcc.comp (continuous_id.div_const T))

def solution {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) : ℝ → ℂ :=
  (exists_solution hε hT (extendDriver T U) (continuous_extendDriver T U).continuousOn z).choose

lemma solution_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    solution hε hT U z 0 = z :=
  (exists_solution hε hT (extendDriver T U)
    (continuous_extendDriver T U).continuousOn z).choose_spec.1

lemma solution_deriv {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (solution hε hT U z)
      (velocity ε (extendDriver T U t) (solution hε hT U z t)) (Icc 0 T) t :=
  (exists_solution hε hT (extendDriver T U)
    (continuous_extendDriver T U).continuousOn z).choose_spec.2

def solutionPath {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (U : C(I, ℝ)) (z : ℂ) :
    C(Icc 0 T, ℂ) :=
  ⟨fun t => solution hε hT U z t,
    continuousOn_iff_continuous_domRestrict.1 (HasDerivWithinAt.continuousOn (solution_deriv hε hT U z))⟩

lemma solutionPath_lipschitz {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    LipschitzWith ⟨Real.exp ((4 / ε^2) * T), (Real.exp_pos _).le⟩
      (fun U : C(I, ℝ) => solutionPath hε hT U z) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  apply (ContinuousMap.dist_le (mul_nonneg (Real.exp_pos _).le dist_nonneg)).2
  intro t
  have hUV (s : ℝ) (_hs : s ∈ Icc 0 T) :
      |extendDriver T U s-extendDriver T V s| ≤ dist U V := by
    exact (ContinuousMap.dist_apply_le_dist (f := U) (g := V)
      (projIcc 0 1 zero_le_one (s/T)))
  have hh := solution_dist_le hε dist_nonneg (solution_deriv hε hT U z)
    (solution_deriv hε hT V z)
    ((solution_initial hε hT U z).trans (solution_initial hε hT V z).symm)
    hUV t.property
  change dist (solution hε hT U z t) (solution hε hT V z t) ≤
    Real.exp ((4 / ε^2)*T) * dist U V
  simpa only [mul_comm] using hh

def position {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℂ :=
  solutionPath hε hT U z (projIcc 0 T hT t)

lemma position_eq {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    position hε hT U z t = solution hε hT U z t := by
  simp only [position, solutionPath, projIcc, max_eq_right ht.1,
    min_eq_right ht.2]
  rfl

lemma continuous_position {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    Continuous (fun p : C(I, ℝ) × ℝ => position hε hT p.1 z p.2) := by
  exact continuous_eval.comp (((solutionPath_lipschitz hε hT z).continuous.comp continuous_fst).prodMk
    ((continuous_projIcc (h := hT)).comp continuous_snd))

lemma continuous_joint_extendDriver (T : ℝ) :
    Continuous (fun p : C(I, ℝ) × ℝ => extendDriver T p.1 p.2) := by
  exact continuous_eval.comp (continuous_fst.prodMk
    ((continuous_projIcc (h := zero_le_one)).comp (continuous_snd.div_const T)))

def variation {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  (-2 / (clampRe ε (position hε hT U z t - (extendDriver T U t : ℂ)))^2).re

lemma continuous_clampRe (ε : ℝ) : Continuous (clampRe ε) := by
  change Continuous (fun w : ℂ => Complex.equivRealProdCLM.symm (1*max (1*w.re) ε,w.im))
  apply Complex.equivRealProdCLM.symm.continuous.comp
  apply Continuous.prodMk <;> fun_prop

lemma continuous_variation {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    Continuous (fun p : C(I, ℝ) × ℝ => variation hε hT p.1 z p.2) := by
  have hw := (continuous_position hε hT z).sub
    (Complex.continuous_ofReal.comp (continuous_joint_extendDriver T))
  exact Complex.continuous_re.comp (continuous_const.div
    (((continuous_clampRe ε).comp hw).pow 2)
    (fun p => pow_ne_zero 2 (clampRe_ne_zero hε _)))

def logDerivative {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..(projIcc 0 T hT t : ℝ), variation hε hT U z s

lemma continuous_logDerivative {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (z : ℂ) :
    Continuous (fun p : C(I, ℝ) × ℝ => logDerivative hε hT p.1 z p.2) := by
  have hc := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (a₀ := 0) (f := fun U t => variation hε hT U z t)
    (continuous_variation hε hT z)
  exact hc.comp (continuous_fst.prodMk
    (continuous_subtype_val.comp ((continuous_projIcc (h := hT)).comp continuous_snd)))

lemma abs_variation_le {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) :
    |variation hε hT U z t| ≤ 2/ε^2 := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_div, norm_neg, Complex.norm_ofNat, norm_pow]
  apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hε)
  exact pow_le_pow_left₀ hε.le (clampRe_norm hε _) 2

lemma logDerivative_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) : logDerivative hε hT U z 0 = 0 := by
  simp only [logDerivative, projIcc_of_mem hT (left_mem_Icc.mpr hT), intervalIntegral.integral_same]

lemma abs_logDerivative_le {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) (t : ℝ) :
    |logDerivative hε hT U z t| ≤ (2/ε^2)*T := by
  have hb := (projIcc 0 T hT t).property
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := (projIcc 0 T hT t : ℝ))
    (fun s (_hs : s ∈ uIoc 0 (projIcc 0 T hT t : ℝ)) =>
      show ‖variation hε hT U z s‖ ≤ 2/ε^2 from abs_variation_le hε hT U z s)
  change |logDerivative hε hT U z t| ≤ _
  apply hi.trans
  rw [sub_zero, abs_of_nonneg hb.1]
  exact mul_le_mul_of_nonneg_left hb.2 (by positivity)

lemma position_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) : position hε hT U z 0 = z := by
  rw [position_eq hε hT U z ⟨le_rfl,hT⟩, solution_initial]

lemma position_derivWithin {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (position hε hT U z)
      (velocity ε (extendDriver T U t) (position hε hT U z t)) (Icc 0 T) t := by
  rw [position_eq hε hT U z ht]
  exact (solution_deriv hε hT U z t ht).congr
    (fun s hs => position_eq hε hT U z hs) (position_eq hε hT U z ht)

lemma position_deriv {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (position hε hT U z)
      (velocity ε (extendDriver T U t) (position hε hT U z t)) t :=
  (position_derivWithin hε hT U z ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

lemma logDerivative_eq_integral {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    logDerivative hε hT U z t = ∫ s in (0:ℝ)..t, variation hε hT U z s := by
  simp only [logDerivative, projIcc_of_mem hT ht]

lemma hasDerivAt_logDerivative {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (z : ℂ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (logDerivative hε hT U z) (variation hε hT U z t) t := by
  have hp : Continuous (fun t : ℝ => (U,t)) := continuous_const.prodMk continuous_id
  have hc := (continuous_variation hε hT z).comp hp
  dsimp only [Function.comp_def] at hc
  have hd : HasDerivAt (fun v : ℝ => ∫ s in (0:ℝ)..v, variation hε hT U z s)
      (variation hε hT U z t) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  exact logDerivative_eq_integral hε hT U z hs

lemma position_prefix_eq {ε T₁ T₂ S : ℝ} (hε : 0 < ε)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (_hS : 0 ≤ S) (hS₁ : S ≤ T₁) (hS₂ : S ≤ T₂)
    (U V : C(I, ℝ)) (z : ℂ)
    (hUV : EqOn (extendDriver T₁ U) (extendDriver T₂ V) (Icc 0 S)) :
    EqOn (position hε hT₁ U z) (position hε hT₂ V z) (Icc 0 S) := by
  apply solution_eq hε (U := extendDriver T₁ U) ?_ ?_ ((position_initial hε hT₁ U z).trans (position_initial hε hT₂ V z).symm)
  · intro t ht
    exact (position_derivWithin hε hT₁ U z ⟨ht.1,ht.2.trans hS₁⟩).mono
      (Icc_subset_Icc le_rfl hS₁)
  · intro t ht
    rw [hUV ht]
    exact (position_derivWithin hε hT₂ V z ⟨ht.1,ht.2.trans hS₂⟩).mono
      (Icc_subset_Icc le_rfl hS₂)

lemma logDerivative_prefix_eq {ε T₁ T₂ S : ℝ} (hε : 0 < ε)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (hS : 0 ≤ S) (hS₁ : S ≤ T₁) (hS₂ : S ≤ T₂)
    (U V : C(I, ℝ)) (z : ℂ)
    (hUV : EqOn (extendDriver T₁ U) (extendDriver T₂ V) (Icc 0 S)) :
    EqOn (logDerivative hε hT₁ U z) (logDerivative hε hT₂ V z) (Icc 0 S) := by
  have hH := position_prefix_eq hε hT₁ hT₂ hS hS₁ hS₂ U V z hUV
  intro t ht
  rw [logDerivative_eq_integral hε hT₁ U z ⟨ht.1,ht.2.trans hS₁⟩,
    logDerivative_eq_integral hε hT₂ V z ⟨ht.1,ht.2.trans hS₂⟩]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  have hsS : s ∈ Icc 0 S := ⟨hs.1,hs.2.trans ht.2⟩
  simp only [variation, hH hsS, hUV hsS]

lemma position_im_zero {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I, ℝ)) (x t : ℝ) : (position hε hT U (x:ℂ) t).im = 0 := by
  have hc := BoundaryCutoff.conjugate_deriv (solution_deriv hε hT U (x:ℂ))
  have he := solution_eq hε (solution_deriv hε hT U (x:ℂ)) hc (by
    rw [solution_initial]; simp)
  let v := projIcc 0 T hT t
  have hv := he v.property
  change solution hε hT U (x:ℂ) v = star (solution hε hT U (x:ℂ) v) at hv
  have hh := congrArg Complex.im hv
  change (solution hε hT U (x:ℂ) v).im = 0
  change (solution hε hT U (x:ℂ) v).im = -(solution hε hT U (x:ℂ) v).im at hh
  linarith

end SLEExactGauge.BoundaryFunctional

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Swallowing
open GreenPhysical

def radial (β x y : ℝ) : ℝ := (x^2+y^2)^(β/2)

def lyapunov (β C x y : ℝ) : ℝ := radial β x y+C*y^β

def radialX (β x y : ℝ) : ℝ := β*x*(x^2+y^2)^(β/2-1)

def radialXX (β x y : ℝ) : ℝ :=
  β*(x^2+y^2)^(β/2-1)+β*(β-2)*x^2*(x^2+y^2)^(β/2-2)

def radialXXX (β x y : ℝ) : ℝ :=
  3*β*(β-2)*x*(x^2+y^2)^(β/2-2)+
  β*(β-2)*(β-4)*x^3*(x^2+y^2)^(β/2-3)

lemma radial_pos (β x : ℝ) {y : ℝ} (hy : 0 < y) : 0 < radial β x y :=
  Real.rpow_pos_of_pos (q_pos x hy) _

lemma hasDerivAt_radial_path (β : ℝ) {X Y : ℝ → ℝ} {t X' Y' : ℝ}
    (hX : HasDerivAt X X' t) (hY : HasDerivAt Y Y' t) (hy : 0 < Y t) :
    HasDerivAt (fun t => radial β (X t) (Y t))
      (β*(X t*X'+Y t*Y')*(X t^2+Y t^2)^(β/2-1)) t := by
  have h := (((hX.pow 2).add (hY.pow 2)).rpow_const (p := β/2) (Or.inl (q_pos (X t) hy).ne'))
  simp only [Pi.add_apply,Pi.pow_apply] at h
  apply h.congr_deriv
  ring

lemma hasDerivAt_radial_x (β x y : ℝ) (hy : 0 < y) :
    HasDerivAt (radial β · y) (radialX β x y) x := by
  convert hasDerivAt_radial_path β (hasDerivAt_id x) (hasDerivAt_const x y) hy using 1 <;>
    simp [radialX]

lemma hasDerivAt_radialX_x (β x y : ℝ) (hy : 0 < y) :
    HasDerivAt (radialX β · y) (radialXX β x y) x := by
  have hq := ((hasDerivAt_id x).pow 2).add_const (y^2)
  have h := ((hasDerivAt_id x).const_mul β).mul
    (hq.rpow_const (p := β/2-1) (Or.inl (q_pos x hy).ne'))
  apply h.congr_deriv
  dsimp only [id_eq,Pi.pow_apply,radialXX]
  convert_to β*(x^2+y^2)^(β/2-1)+β*x*((2*x)*((β/2-1)*(x^2+y^2)^(β/2-1-1))) = _ using 1
  · ring
  rw [show β/2-1-1 = β/2-2 by ring]
  ring

lemma hasDerivAt_radialXX_x (β x y : ℝ) (hy : 0 < y) :
    HasDerivAt (radialXX β · y) (radialXXX β x y) x := by
  have hq := ((hasDerivAt_id x).pow 2).add_const (y^2)
  have h1 := (hq.rpow_const (p := β/2-1) (Or.inl (q_pos x hy).ne')).const_mul β
  have h2 := (((hasDerivAt_id x).pow 2).const_mul (β*(β-2))).mul
    (hq.rpow_const (p := β/2-2) (Or.inl (q_pos x hy).ne'))
  apply (h1.add h2).congr_deriv
  dsimp only [id_eq,Pi.pow_apply,radialXXX]
  rw [show β/2-1-1 = β/2-2 by ring,show β/2-2-1 = β/2-3 by ring]
  ring

lemma contDiff_radial_driver (β c y s : ℝ) (hy : 0 < y) :
    ContDiff ℝ ⊤ (fun b => radial β (c-s*b) y) := by
  unfold radial
  apply ContDiff.rpow_const_of_ne
  · fun_prop
  · intro x; exact (q_pos _ hy).ne'

lemma lyapunov_nonneg {β C : ℝ} (hC : 0 ≤ C) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    0 ≤ lyapunov β C x y := by
  exact add_nonneg (radial_pos β x hy).le (mul_nonneg hC (Real.rpow_nonneg hy.le _))

def generator (κ β C x y : ℝ) : ℝ :=
  β*(x*(2*x/(x^2+y^2))+y*(-2*y/(x^2+y^2)))*(x^2+y^2)^(β/2-1) +
  C*(β*y^(β-1)*(-2*y/(x^2+y^2))) + κ/2*radialXX β x y

end SLEExactGauge.Swallowing

end

end

end OAI
