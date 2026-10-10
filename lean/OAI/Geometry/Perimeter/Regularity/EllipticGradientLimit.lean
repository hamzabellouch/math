import OAI.Geometry.Perimeter.Regularity.EllipticScaleStep

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem real_volume_ball_center (p : Euc n) (r : ℝ) :
    volume.real (Metric.ball p r)=volume.real (Metric.ball (0:Euc n) r) := by
  exact Measure.addHaar_real_ball_center volume p r

 theorem scaledGradientEnergy_lower {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    (p : Euc n) {r b : ℝ} (hr : 0<r) (q : Euc n)
    (hb : ∀ x∈Metric.ball p r, b≤‖gradient f x-q‖^2) :
    b*volume.real (Metric.ball (0:Euc n) 1) ≤ scaledGradientEnergy f p r q := by
  have hI : IntegrableOn (fun x ↦ ‖gradient f x-q‖^2) (Metric.ball p r) volume :=
    ((((gradient_continuous_C1 hf).sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall p r)).mono_set Metric.ball_subset_closedBall
  have : IsFiniteMeasure (volume.restrict (Metric.ball p r)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hh : (∫ x in Metric.ball p r, b) ≤ gradientEnergy f p r q := by
    apply integral_mono_ae (integrable_const _) hI
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hb x hx
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hh
  rw [real_volume_ball_center,real_volume_ball_scale hr] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (pow_nonneg hr.le n))
  change _ ≤ (r^n)⁻¹*gradientEnergy f p r q
  convert hh' using 1
  field_simp [hr.ne']

 theorem gradient_eq_of_scaled_energy {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f)
    (p : Euc n) {r ε : ℕ → ℝ} {q : ℕ → Euc n} {w : Euc n}
    (hr : ∀ j,0<r j) (hrlim : Tendsto r atTop (𝓝 0))
    (hε : Tendsto ε atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 w))
    (hE : ∀ j, scaledGradientEnergy f p (r j) (q j) ≤ ε j) : gradient f p=w := by
  by_contra hne
  let d := ‖gradient f p-w‖
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨s,hs,hgs⟩ := Metric.continuousAt_iff.mp (gradient_continuous_C1 hf).continuousAt (d/4) (by positivity)
  have hv : 0<volume.real (Metric.ball (0:Euc n) 1) := by
    exact ENNReal.toReal_pos (by exact ne_of_gt (Metric.measure_ball_pos volume _ (by norm_num))) measure_ball_lt_top.ne
  have hsmall := hε.eventually (gt_mem_nhds (show 0<(d/2)^2*volume.real (Metric.ball (0:Euc n) 1) by positivity))
  have hrsmall := hrlim.eventually (gt_mem_nhds hs)
  have hqsmall := (Metric.tendsto_atTop.mp hq) (d/4) (by positivity)
  obtain ⟨N,hN⟩ := hqsmall
  obtain ⟨j,hjE,hjr,hjq⟩ := (hsmall.and (hrsmall.and (eventually_ge_atTop N))).exists
  have hlo := scaledGradientEnergy_lower hf p (hr j) (q j) (b := (d/2)^2) (fun x hx ↦ by
    have hg : ‖gradient f x-gradient f p‖<d/4 := by
      rw [←dist_eq_norm]
      exact hgs (by exact (Metric.mem_ball.mp hx).trans hjr)
    have hq' : ‖q j-w‖<d/4 := by simpa only [dist_eq_norm] using hN j hjq
    have htri : d≤‖gradient f x-gradient f p‖+‖gradient f x-q j‖+‖q j-w‖ := by
      have hh := norm_add_le (gradient f p-gradient f x) (gradient f x-q j)
      have hh' := norm_add_le (gradient f p-q j) (q j-w)
      simp only [sub_add_sub_cancel,norm_sub_rev (gradient f p) (gradient f x)] at hh hh'
      dsimp [d]
      linarith
    have hn : d/2≤‖gradient f x-q j‖ := by linarith
    exact pow_le_pow_left₀ (by positivity) hn 2)
  linarith [hE j]

end RPISingularHarnack

end

end OAI
