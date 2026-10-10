import Mathlib
import OAI.Geometry.SmoothYau.Limits.PhaseImagVector

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

def profileFrequencyEnergy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) : ℝ :=
  1+selfMetricFlat g x (coordinateMetricGradient g φ x) (coordinateMetricGradient g φ x)

def profileFrequencyScale (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) : ℝ :=
  Real.sqrt (profileFrequencyEnergy g φ x)

lemma profileFrequencyEnergy_ge_one (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    1 ≤ profileFrequencyEnergy g φ x := by
  unfold profileFrequencyEnergy
  by_cases h : coordinateMetricGradient g φ x = 0
  · simp [h]
  · linarith [selfMetricFlat_pos g x h]

lemma profileFrequencyScale_sq (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    profileFrequencyScale g φ x ^ 2 = profileFrequencyEnergy g φ x :=
  Real.sq_sqrt (zero_le_one.trans (profileFrequencyEnergy_ge_one g φ x))

lemma profileFrequencyScale_ge_one (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (x : NormalWaveSpace) :
    1 ≤ profileFrequencyScale g φ x := by
  have h := Real.sqrt_nonneg (profileFrequencyEnergy g φ x)
  have he := profileFrequencyScale_sq g φ x
  have h1 := profileFrequencyEnergy_ge_one g φ x
  change 0 ≤ profileFrequencyScale g φ x at h
  nlinarith

lemma continuous_profileFrequencyEnergy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (profileFrequencyEnergy g φ) := by
  have hGi : ContDiff ℝ ∞ (fun x => (selfMetricFlat g x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (selfMetricFlat_invertible g x).contDiffAt_map_inverse.comp x
      (contDiff_selfMetricFlat g).contDiffAt
  have hg : Continuous (coordinateMetricGradient g φ) :=
    (hGi.clm_apply (hφ.fderiv_right (m := ∞) (by simp))).continuous
  exact continuous_const.add (((contDiff_selfMetricFlat g).continuous.clm_apply hg).clm_apply hg)

lemma profileFrequencyEnergy_frame (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} {q : NormalWaveParameter} (hq : q ∈ metricFrameSet g K) :
    profileFrequencyEnergy g φ q.1 = 1+‖gradient (normalWaveProfile g φ q) 0‖^2 := by
  unfold profileFrequencyEnergy
  rw [←metric_frame_gradient g hφ hq,hq.2,real_inner_self_eq_norm_sq]

lemma nearby_characteristic_energy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {φ : NormalWaveSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ, ∀ x : NormalWaveSpace,
      ‖x-q.1‖ ≤ r → ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ r →
      profileFrequencyEnergy g φ x/2 ≤ 1+‖phaseRealVector z‖^2 ∧
      1+‖phaseRealVector z‖^2 ≤ 2*profileFrequencyEnergy g φ x := by
  have hE := continuous_profileFrequencyEnergy g hφ
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hE.continuousOn
  let M := max 1 (C+1)
  have hM : 1 ≤ M := le_max_left _ _
  have hCM : C ≤ M := le_trans (by linarith) (le_max_right 1 (C+1))
  let H := fun w : NormalWaveSpace × NormalWaveSpace => profileFrequencyEnergy g φ (w.1+w.2)
  obtain ⟨rv,hrv,hvar⟩ := compact_uniform_value_radius H (hE.comp (continuous_fst.add continuous_snd))
    hK (show (0 : ℝ) < 1/4 by norm_num)
  let r := min (rv/2) (min 1 (1/(4*(2*M+1))))
  have hr : 0 < r := lt_min (half_pos hrv) (lt_min zero_lt_one (by positivity))
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrrv : r < rv := (min_le_left _ _).trans_lt (by linarith)
  have hrM : (2*M+1)*r ≤ 1/4 := by
    have hh := (min_le_right (rv/2) _).trans (min_le_right 1 (1/(4*(2*M+1))))
    have he := (le_div_iff₀ (show 0 < 4*(2*M+1) by positivity)).mp hh
    nlinarith
  refine ⟨r,hr,?_⟩
  intro q hq z x hx hz
  let a := gradient (normalWaveProfile g φ q) 0
  have ha : ‖a‖ ≤ M := by
    have he := profileFrequencyEnergy_frame g hφ hq
    have hb := (le_abs_self (profileFrequencyEnergy g φ q.1)).trans (hC q.1 hq.1)
    change profileFrequencyEnergy g φ q.1 = 1+‖a‖^2 at he
    nlinarith [sq_nonneg (M-1),norm_nonneg a]
  have hbda : |‖phaseRealVector z‖-‖a‖| ≤ r := (abs_norm_sub_norm_le _ _).trans hz
  have hb : ‖phaseRealVector z‖ ≤ M+1 := by
    have ht := (abs_le.mp hbda).2
    linarith
  have hs : |‖phaseRealVector z‖^2-‖a‖^2| ≤ 1/4 := by
    calc
      _ = |‖phaseRealVector z‖-‖a‖| *(‖phaseRealVector z‖+‖a‖) := by
        rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        ring
      _ ≤ r*(2*M+1) := mul_le_mul hbda (by linarith)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) hr.le
      _ ≤ 1/4 := by nlinarith [hrM]
  have hv : |profileFrequencyEnergy g φ x-profileFrequencyEnergy g φ q.1| < 1/4 := by
    have hh := hvar q.1 hq.1 (x-q.1)
      (show x-q.1 ∈ Metric.ball 0 rv by simpa only [Metric.mem_ball,dist_zero_right] using hx.trans_lt hrrv)
    simpa only [H,add_sub_cancel,add_zero,Real.norm_eq_abs] using hh
  have he := profileFrequencyEnergy_frame g hφ hq
  have h1 := profileFrequencyEnergy_ge_one g φ x
  change profileFrequencyEnergy g φ q.1 = 1+‖a‖^2 at he
  obtain ⟨hs₁,hs₂⟩ := abs_le.mp hs
  obtain ⟨hv₁,hv₂⟩ := abs_lt.mp hv
  constructor <;> linarith

theorem compact_normal_profile_angular_energy (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ φ : NormalWaveSpace → ℝ, ContDiff ℝ ∞ φ →
      ∃ r > 0, ∀ q ∈ metricFrameSet g K, ∀ z : Fin 3 → ℂ, ∀ x : NormalWaveSpace,
        (∑ i, z i*z i = -1) → ‖x-q.1‖ ≤ r →
        ‖phaseRealVector z-gradient (normalWaveProfile g φ q) 0‖ ≤ r →
        c*profileFrequencyScale g φ x^2 ≤
          ∑ i : Fin 3, (normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i))^2 ∧
        (∑ i : Fin 3, (normalImagCovector q z (EuclideanSpace.basisFun (Fin 3) ℝ i))^2) ≤
          C*profileFrequencyScale g φ x^2 := by
  obtain ⟨c,hc,C,hC,hb⟩ := compact_normal_angular_energy g hK
  refine ⟨c/2,half_pos hc,2*C,by positivity,?_⟩
  intro φ hφ
  obtain ⟨r,hr,he⟩ := nearby_characteristic_energy g hφ hK
  refine ⟨r,hr,?_⟩
  intro q hq z x hz hx hlin
  obtain ⟨hlo,hhi⟩ := he q hq z x hx hlin
  obtain ⟨hlo',hhi'⟩ := hb q hq z hz
  rw [profileFrequencyScale_sq]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hc.le]
  · nlinarith [mul_le_mul_of_nonneg_left hhi hC.le]
end YauCounterexamples
end

end OAI
