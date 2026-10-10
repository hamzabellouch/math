import OAI.Geometry.Perimeter.Regularity.EllipticGradientLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem gradientEnergy_integrable {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    (p : Euc n) (r : ℝ) (q : Euc n) :
    IntegrableOn (fun x ↦ ‖gradient f x-q‖^2) (Metric.ball p r) volume :=
  ((((gradient_continuous_C1 hf).sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall p r)).mono_set Metric.ball_subset_closedBall

 theorem gradientEnergy_mono {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    {p p' : Euc n} {r r' : ℝ} (q : Euc n) (h : Metric.ball p r ⊆ Metric.ball p' r') :
    gradientEnergy f p r q ≤ gradientEnergy f p' r' q :=
  setIntegral_mono_set (gradientEnergy_integrable hf p' r' q)
    (ae_of_all _ (fun _ ↦ sq_nonneg _)) (ae_of_all _ (fun x ↦ show x∈Metric.ball p r → x∈Metric.ball p' r' from fun hx ↦ h hx))

 theorem constant_slopes_energy_bound {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    (p : Euc n) {r : ℝ} (hr : 0<r) (q q' : Euc n) :
    ‖q-q'‖^2*volume.real (Metric.ball p r) ≤
      2*gradientEnergy f p r q+2*gradientEnergy f p r q' := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball p r)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  calc
    _ = ∫ x in Metric.ball p r, ‖q-q'‖^2 := by
      simp [real_volume_ball_center, real_volume_ball_scale hr, mul_comm]
    _ ≤ ∫ x in Metric.ball p r, 2*‖gradient f x-q‖^2+2*‖gradient f x-q'‖^2 := by
      apply integral_mono (integrable_const _) (((gradientEnergy_integrable hf p r q).const_mul 2).add
        ((gradientEnergy_integrable hf p r q').const_mul 2))
      intro x
      have hh := norm_sub_le (q-gradient f x) (q'-gradient f x)
      have he : (q-gradient f x)-(q'-gradient f x)=q-q' := by abel
      rw [he,norm_sub_rev q (gradient f x),norm_sub_rev q' (gradient f x)] at hh
      have hh' := pow_le_pow_left₀ (norm_nonneg (q-q')) hh 2
      change ‖q-q'‖^2 ≤ 2*‖gradient f x-q‖^2+2*‖gradient f x-q'‖^2
      nlinarith [sq_nonneg (‖gradient f x-q‖-‖gradient f x-q'‖)]
    _ = _ := by rw [integral_add ((gradientEnergy_integrable hf p r q).const_mul 2)
        ((gradientEnergy_integrable hf p r q').const_mul 2),integral_const_mul,integral_const_mul]; rfl

 theorem scaled_slope_comparison {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    (p p' : Euc n) {r : ℝ} (hr : 0<r) (hd : dist p p'≤r/2) (q q' : Euc n) :
    volume.real (Metric.ball (0:Euc n) 1)*‖q-q'‖^2 ≤
      2^(n+1)*(scaledGradientEnergy f p r q+scaledGradientEnergy f p' r q') := by
  have hb : Metric.ball p' (r/2) ⊆ Metric.ball p r := by
    intro x hx
    have hh := dist_triangle x p' p
    rw [dist_comm p' p] at hh
    exact Metric.mem_ball.mpr (by linarith [Metric.mem_ball.mp hx])
  have hb' : Metric.ball p' (r/2) ⊆ Metric.ball p' r := Metric.ball_subset_ball (by linarith)
  have hh := constant_slopes_energy_bound hf p' (by positivity : 0<r/2) q q'
  have h1 := gradientEnergy_mono hf q hb
  have h2 := gradientEnergy_mono hf q' hb'
  have hh' : ‖q-q'‖^2*volume.real (Metric.ball p' (r/2)) ≤
      2*gradientEnergy f p r q+2*gradientEnergy f p' r q' := by linarith
  rw [real_volume_ball_center,real_volume_ball_scale (by positivity : 0<r/2)] at hh'
  have hm := mul_le_mul_of_nonneg_left hh' (by positivity : 0≤((r/2)^n)⁻¹)
  convert hm using 1 <;> first | rfl | (simp only [scaledGradientEnergy,div_pow,pow_succ,inv_div]; field_simp [hr.ne'])

end RPISingularHarnack

end

end OAI
