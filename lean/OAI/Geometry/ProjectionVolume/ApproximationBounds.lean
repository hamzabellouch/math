import OAI.Geometry.ProjectionVolume.BallBrightness
import OAI.Geometry.ProjectionVolume.SupportLimit
import OAI.Geometry.ProjectionVolume.InnerSequence

namespace OAI

open Set Metric Filter MeasureTheory
open scoped Pointwise Topology RealInnerProductSpace

namespace Paper092

theorem volume_smul_real {d : ℕ} (P : Set (Euclidean d)) {c : ℝ} (hc : 0 ≤ c) :
    (volume (c • P)).toReal = c ^ d * (volume P).toReal := by
  rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_pow, abs_of_nonneg hc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc _)]

theorem volume_real_mono {d : ℕ} {P K : Set (Euclidean d)} (hK : IsCompact K) (h : P ⊆ K) :
    (volume P).toReal ≤ (volume K).toReal :=
  ENNReal.toReal_mono hK.measure_lt_top.ne (measure_mono h)

theorem approximation_brightness_bound {d : ℕ} (hd : 2 ≤ d)
    {P K : Set (Euclidean d)} (hP : IsCompact P) (hK : IsCompact K)
    {scale R : ℝ} (hscale : 1 ≤ scale) (hR : 0 ≤ R) (hPK : P ⊆ K) (hKP : K ⊆ scale • P)
    (hKR : K ⊆ closedBall 0 R) (u : Euclidean d) (hu : ‖u‖ = 1) :
    0 ≤ brightness K u - brightness P u ∧
      brightness K u - brightness P u ≤
        (scale ^ (d - 1) - 1) * (euclideanUnitBallVolume (d - 1) * R ^ (d - 1)) := by
  have hmono := brightness_mono hPK hK u
  have hupper : brightness K u ≤ scale ^ (d - 1) * brightness P u := by
    have hh := brightness_mono hKP (hP.smul scale) u
    simpa only [brightness_body_smul, abs_of_nonneg (zero_le_one.trans hscale)] using hh
  have hbound : brightness P u ≤ euclideanUnitBallVolume (d - 1) * R ^ (d - 1) :=
    hmono.trans (by simpa only [hu, one_mul] using brightness_le_ball_bound hd hR hKR u)
  have hpow : 1 ≤ scale ^ (d - 1) := one_le_pow₀ hscale
  refine ⟨sub_nonneg.mpr hmono, ?_⟩
  calc
    brightness K u - brightness P u ≤ (scale ^ (d - 1) - 1) * brightness P u := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hpow)

theorem approximation_projectionBody_sandwich {d : ℕ} {P K : Set (Euclidean d)}
    (hP : IsCompact P) (hK : IsCompact K) {scale : ℝ} (hscale : 0 < scale)
    (hPK : P ⊆ K) (hKP : K ⊆ scale • P) :
    projectionBody P ⊆ projectionBody K ∧
      projectionBody K ⊆ scale ^ (d - 1) • projectionBody P := by
  refine ⟨projectionBody_mono hPK hK, ?_⟩
  have hh := projectionBody_mono hKP (hP.smul scale)
  simpa only [projectionBody_body_smul P scale hscale.ne', abs_of_pos hscale] using hh

theorem approximation_volume_sandwich {d : ℕ} {P K : Set (Euclidean d)}
    (hP : IsCompact P) (hK : IsCompact K) {scale : ℝ} (hscale : 0 ≤ scale)
    (hPK : P ⊆ K) (hKP : K ⊆ scale • P) :
    (volume P).toReal ≤ (volume K).toReal ∧
      (volume K).toReal ≤ scale ^ d * (volume P).toReal := by
  refine ⟨volume_real_mono hK hPK, ?_⟩
  exact (volume_real_mono (hP.smul scale) hKP).trans_eq (volume_smul_real P hscale)

theorem approximation_projectionBody_volume_sandwich {d : ℕ} {P K : Set (Euclidean d)}
    (hP : IsCompact P) (hK : IsCompact K) {scale : ℝ} (hscale : 0 < scale)
    (hPK : P ⊆ K) (hKP : K ⊆ scale • P) :
    (volume (projectionBody P)).toReal ≤ (volume (projectionBody K)).toReal ∧
      (volume (projectionBody K)).toReal ≤
        scale ^ (d * (d - 1)) * (volume (projectionBody P)).toReal := by
  obtain ⟨hPiPK, hPiKP⟩ := approximation_projectionBody_sandwich hP hK hscale hPK hKP
  have hh := approximation_volume_sandwich (projectionBody_isCompact P)
    (projectionBody_isCompact K) (pow_nonneg hscale.le _) hPiPK hPiKP
  simpa only [← pow_mul, Nat.mul_comm (d - 1) d] using hh

theorem approximation_brightness_uniform {d : ℕ} (hd : 2 ≤ d)
    {P : ℕ → Set (Euclidean d)} {K : Set (Euclidean d)}
    (hP : ∀ m, IsCompact (P m)) (hK : IsCompact K)
    {scale : ℕ → ℝ} (hscale : ∀ m, 1 ≤ scale m) (hscalelim : Tendsto scale atTop (𝓝 1))
    {R : ℝ} (hR : 0 ≤ R) (hKR : K ⊆ closedBall 0 R)
    (hPK : ∀ m, P m ⊆ K) (hKP : ∀ m, K ⊆ scale m • P m) :
    TendstoUniformlyOn (fun m u => brightness (P m) u) (brightness K) atTop (sphere 0 1) := by
  let C := euclideanUnitBallVolume (d - 1) * R ^ (d - 1)
  have hcont : Continuous (fun r : ℝ => (r ^ (d - 1) - 1) * C) := by fun_prop
  have hlim : Tendsto (fun m => (scale m ^ (d - 1) - 1) * C) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_pow, sub_self, zero_mul] using (hcont.tendsto 1).comp hscalelim
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (Iio_mem_nhds hε)] with m hm
  intro u hu
  have hunit : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
  have hb := approximation_brightness_bound hd (hP m) hK (hscale m) hR (hPK m) (hKP m) hKR u hunit
  rw [Real.dist_eq, abs_of_nonneg hb.1]
  exact hb.2.trans_lt hm

theorem tendsto_of_multiplicative_sandwich {f q : ℕ → ℝ} {L : ℝ}
    (hq : ∀ m, 0 < q m) (hqlim : Tendsto q atTop (𝓝 1))
    (hupper : ∀ m, f m ≤ L) (hlower : ∀ m, L ≤ q m * f m) :
    Tendsto f atTop (𝓝 L) := by
  have hlim : Tendsto (fun m => L / q m) atTop (𝓝 L) := by
    have hcont : ContinuousAt (fun x : ℝ => L / x) 1 := by fun_prop (disch := norm_num)
    simpa only [Function.comp_def, div_one] using hcont.tendsto.comp hqlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
  · intro m
    exact (div_le_iff₀ (hq m)).mpr (by simpa only [mul_comm] using hlower m)
  · exact hupper

theorem approximation_volume_tendsto {d : ℕ}
    {P : ℕ → Set (Euclidean d)} {K : Set (Euclidean d)}
    (hP : ∀ m, IsCompact (P m)) (hK : IsCompact K)
    {scale : ℕ → ℝ} (hscale : ∀ m, 0 < scale m) (hscalelim : Tendsto scale atTop (𝓝 1))
    (hPK : ∀ m, P m ⊆ K) (hKP : ∀ m, K ⊆ scale m • P m) :
    Tendsto (fun m => (volume (P m)).toReal) atTop (𝓝 (volume K).toReal) ∧
      Tendsto (fun m => (volume (projectionBody (P m))).toReal) atTop
        (𝓝 (volume (projectionBody K)).toReal) := by
  have hq (k : ℕ) : Tendsto (fun m => scale m ^ k) atTop (𝓝 1) := by
    have hcont : Continuous (fun x : ℝ => x ^ k) := by fun_prop
    simpa only [Function.comp_def, one_pow] using (hcont.tendsto 1).comp hscalelim
  constructor
  · apply tendsto_of_multiplicative_sandwich (fun m => pow_pos (hscale m) d) (hq d)
    · exact fun m => (approximation_volume_sandwich (hP m) hK (hscale m).le (hPK m) (hKP m)).1
    · exact fun m => (approximation_volume_sandwich (hP m) hK (hscale m).le (hPK m) (hKP m)).2
  · apply tendsto_of_multiplicative_sandwich (fun m => pow_pos (hscale m) (d * (d - 1)))
      (hq (d * (d - 1)))
    · exact fun m => (approximation_projectionBody_volume_sandwich (hP m) hK (hscale m) (hPK m) (hKP m)).1
    · exact fun m => (approximation_projectionBody_volume_sandwich (hP m) hK (hscale m) (hPK m) (hKP m)).2

end Paper092

end OAI
