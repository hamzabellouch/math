import Mathlib
import OAI.Probability.SKGap.Entropy.ScalarEntropyTarget

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

lemma entropyTestBound_q_pos {P : Measure ℝ} [IsProbabilityMeasure P]
    {d D : ℝ} {s : ℝ≥0} (hs : s ≠ 0) (hD : EntropyTestBound P (gaussianReal d s) D) :
    0 < ∫ y, tanh y^2 ∂P := by
  have hn : 0 ≤ ∫ y, tanh y^2 ∂P := integral_nonneg (fun y => sq_nonneg (tanh y))
  by_contra hh
  have hzero : (∫ y, tanh y^2 ∂P) = 0 := le_antisymm (le_of_not_gt hh) hn
  let F : ℕ → ℝ → ℝ := fun n y => exp (-(n:ℝ)*tanh y^2)
  have hFn (n : ℕ) (y : ℝ) : ‖F n y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (sq_nonneg _))
  have hFi (n : ℕ) : Integrable (F n) (gaussianReal d s) :=
    Integrable.of_bound (by dsimp [F]; fun_prop) 1 (ae_of_all _ (hFn n))
  have h_lower (n : ℕ) : exp (-D) ≤ ∫ y, F n y ∂gaussianReal d s := by
    have h := entropyTestBound_continuous hD (f := fun y => -(n:ℝ)*tanh y^2)
      (by fun_prop) (integrable_tanh_sq.const_mul _) (hFi n)
    rw [integral_const_mul, hzero, mul_zero, zero_sub] at h
    have hz := integral_exp_pos (hFi n)
    calc
      _ ≤ exp (log (∫ y, F n y ∂gaussianReal d s)) := exp_le_exp.mpr (by linarith)
      _ = _ := exp_log hz
  have := nullSingletonClass_gaussianReal (μ := d) hs
  have hlim : Tendsto (fun n => ∫ y, F n y ∂gaussianReal d s) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => ∫ y, F n y ∂gaussianReal d s) atTop
        (𝓝 (∫ _ : ℝ, (0:ℝ) ∂gaussianReal d s)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
      · intro n; exact (hFi n).aestronglyMeasurable
      · exact integrable_const 1
      · intro n; exact ae_of_all _ (hFn n)
      · filter_upwards [(gaussianReal d s).ae_ne 0] with y hy
        have hm : tanh y ≠ 0 := fun hz => hy (tanh_injective (by simpa only [tanh_zero] using hz))
        have hc : 0 < tanh y^2 := sq_pos_of_ne_zero hm
        have hnat : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        have hneg := tendsto_neg_atTop_atBot.comp (hnat.atTop_mul_const hc)
        exact tendsto_exp_atBot.comp (by simpa only [Function.comp_def, neg_mul] using hneg)
    simpa using hh
  have hle := ge_of_tendsto hlim (Eventually.of_forall h_lower)
  exact (not_le_of_gt (exp_pos (-D))) hle

@[fun_prop] lemma continuous_entropyTransportLog {u d s : ℝ} (hu : u < 1) :
    Continuous (entropyTransportLog u d s) := by
  have hc : Continuous (entropyTransportDeriv u) := by unfold entropyTransportDeriv; fun_prop
  have hl := hc.log (fun y => (entropyTransportDeriv_pos hu y).ne')
  unfold entropyTransportLog
  exact ((continuous_const.mul ((continuous_id.sub continuous_const).mul continuous_tanh)).sub
    (continuous_const.mul (continuous_tanh.pow 2))).add hl

theorem test_transport_lower {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable id P) {u d : ℝ} {s : ℝ≥0} (hu : u < 1) (hs : s ≠ 0)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    u / (s : ℝ) * (∫ y, (y - d) * tanh y ∂P) -
      u ^ 2 / (2 * (s : ℝ)) * (∫ y, tanh y ^ 2 ∂P) +
      (1 - ∫ y, tanh y ^ 2 ∂P) * log (1 - u) ≤ D := by
  have hlog := integral_mono
    (((integrable_const (1 : ℝ)).sub integrable_tanh_sq).mul_const (log (1 - u)))
    (integrable_log_entropyTransportDeriv (P := P) hu) (log_entropyTransportDeriv_lower hu)
  simp only [Pi.sub_apply] at hlog
  rw [integral_mul_const, integral_sub (integrable_const 1) integrable_tanh_sq,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hlog
  have h := entropyTestBound_normalized hD (continuous_entropyTransportLog hu) (integrable_entropyTransportLog hP hu d s)
    (integrable_exp_entropyTransportLog hu hs) (integral_exp_entropyTransportLog hu hs)
  unfold entropyTransportLog at h
  rw [integral_add (f := fun y => u / (s : ℝ) * ((y - d) * tanh y) -
      u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2)
      (((integrable_sub_mul_tanh hP d).const_mul _).sub (integrable_tanh_sq.const_mul _))
      (integrable_log_entropyTransportDeriv hu),
    integral_sub ((integrable_sub_mul_tanh hP d).const_mul _) (integrable_tanh_sq.const_mul _),
    integral_const_mul, integral_const_mul] at h
  linarith

lemma continuous_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    Continuous (gaussianRatioLog d s r) := by
  have he : gaussianRatioLog d s r = fun y => (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (y - d)^2 := funext (gaussianRatioLog_formula hs hr)
  rw [he]; fun_prop

theorem test_variance_comparison {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (∫ y, (y - d) ^ 2 ∂P) ≤
      D := by
  have h := entropyTestBound_normalized hD (continuous_gaussianRatioLog hs hr) (integrable_gaussianRatioLog hs hr hP)
    (integrable_exp_gaussianRatioLog hs hr) (integral_exp_gaussianRatioLog hs hr)
  simp_rw [gaussianRatioLog_formula hs hr] at h
  rw [integral_add (integrable_const _) (hP.const_mul _), integral_const_mul] at h
  simpa using h

theorem test_variance_lower {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) {v : ℝ} (hv : 0 < v)
    (hvar : ∫ y, (y - d) ^ 2 ∂P = (s : ℝ) * v) :
    (v - 1 - log v) / 2 ≤ D := by
  let r : ℝ≥0 := s * ⟨v, hv.le⟩
  have hr : r ≠ 0 := mul_ne_zero hs (NNReal.coe_ne_zero.mp hv.ne')
  have h := test_variance_comparison hs hr hP hD
  change (log (s : ℝ) - log ((s : ℝ) * v)) / 2 +
    (1 / (2 * (s : ℝ)) - 1 / (2 * ((s : ℝ) * v))) *
      (∫ y, (y - d) ^ 2 ∂P) ≤ _ at h
  have hsp : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  rw [log_mul hsp hv.ne', hvar] at h
  convert h using 1
  field_simp
  ring

theorem test_scalar_inequality {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P)
    {j d : ℝ} {s : ℝ≥0} (hj0 : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y ^ 2 ∂P) ≤ (s : ℝ))
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    let q := ∫ y, tanh y ^ 2 ∂P
    let a := ∫ y, (y - d) * tanh y ∂P
    let T := j * (a - (s : ℝ) * (1 - q)) ^ 2 / (2 * (s : ℝ) * ((s : ℝ) + j * q))
    T ≤ D ∧
      (a ≠ (s : ℝ) * (1 - q) → T < D) := by
  dsimp only
  let q := ∫ y, tanh y ^ 2 ∂P
  let a := ∫ y, (y - d) * tanh y ∂P
  let k := j * q / (s : ℝ)
  let B := j * (1 - q)
  let C := j * a / (s : ℝ)
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hq0 : 0 < q := entropyTestBound_q_pos hs hD
  have hq1 : q < 1 := entropy_q_lt_one
  have hk0 : 0 < k := div_pos (mul_pos hj0 hq0) hsp
  have hk1 : k ≤ 1 := (div_le_one hsp).mpr hcons
  have hB0 : 0 < B := mul_pos hj0 (sub_pos.mpr hq1)
  have hB1 : B < 1 := by dsimp [B]; nlinarith
  have htransport (u : ℝ) (hu : u < 1) :
      u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u ≤ j * D := by
    have h := mul_le_mul_of_nonneg_left (test_transport_lower (secondMoment_integrable hP) hu hs hD) hj0.le
    change j * (u / (s : ℝ) * a - u ^ 2 / (2 * (s : ℝ)) * q + (1 - q) * log (1 - u)) ≤ j * D at h
    convert h using 1
    dsimp [k, B, C, entropyEll]
    field_simp
    ring
  have hvariance (hC : 1 < C) : C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * (j * D) := by
    let v := (∫ y, (y - d) ^ 2 ∂P) / (s : ℝ)
    have hcauchy := entropy_moment_cauchy hP d hq0
    have hcv : C ^ 2 / (j * k) ≤ v := by
      have heq : C ^ 2 / (j * k) * (s : ℝ) = a ^ 2 / q := by
        dsimp [C, k]
        field_simp
      dsimp [v]
      rw [le_div_iff₀ hsp, heq, div_le_iff₀ hq0]
      simpa only [q, a, mul_comm] using hcauchy
    have hv : 0 < v := (div_pos (pow_pos (by linarith : 0 < C) 2) (mul_pos hj0 hk0)).trans_le hcv
    have hvar : (∫ y, (y - d) ^ 2 ∂P) = (s : ℝ) * v := by dsimp [v]; field_simp
    have hbound := test_variance_lower hs (centered_secondMoment_integrable hP d) hD hv hvar
    exact entropy_variance_scaled_lower hj0 hj1.le hk0 hk1 hC hcv hbound
  have hopt := entropy_scalar_optimization hk0 hk1 hB0 hB1
    (mul_nonneg hj0.le (entropyTestBound_nonneg hD)) htransport hvariance
  have heq : (C - B) ^ 2 / (2 * (1 + k)) =
      j * (j * (a - (s : ℝ) * (1 - q)) ^ 2 / (2 * (s : ℝ) * ((s : ℝ) + j * q))) := by
    dsimp [C, B, k]
    field_simp
  rw [heq] at hopt
  refine ⟨le_of_mul_le_mul_left hopt.1 hj0, ?_⟩
  intro ha
  have hCB : C ≠ B := by
    intro h
    apply ha
    dsimp [C, B] at h
    have he := (div_eq_iff hsp.ne').mp h
    nlinarith
  exact lt_of_mul_lt_mul_left (hopt.2 hCB) hj0.le

theorem scalar_strict_witness {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y^2) P)
    {j d : ℝ} {s : ℝ≥0} (hj : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y^2 ∂P) ≤ (s:ℝ)) (hne : P ≠ gaussianReal d s) :
    ∃ f : ℝ →ᵇ ℝ, scalarEntropyTarget P j d s <
      (∫ y, f y ∂P) - log (∫ y, exp (f y) ∂gaussianReal d s) := by
  by_contra h
  push Not at h
  have hD : EntropyTestBound P (gaussianReal d s) (scalarEntropyTarget P j d s) := h
  have hop := test_scalar_inequality hP hj hj1 hs hcons hD
  have he : (∫ y, (y-d)*tanh y ∂P) = (s:ℝ)*(1-∫ y, tanh y^2 ∂P) := by
    by_contra hh
    exact lt_irrefl _ (hop.2 hh)
  have hzero : scalarEntropyTarget P j d s = 0 := by simp [scalarEntropyTarget, he]
  rw [hzero] at hD
  exact hne (entropyTestBound_zero_eq hD)

end SKGap

end
end
end
end

end OAI
