import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! The fixed Cayley chart compactifies the closed upper half-plane by
sending infinity to `1`. It retains the real boundary pointwise as a
parameterized unit circle, for the relative crosscut construction. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

def halfPlaneCayley (z : ℂ) : ℂ := (z-I)/(z+I)

lemma halfPlaneCayley_den_ne {z : ℂ} (hz : 0 ≤ z.im) : z+I ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at hh
  linarith

lemma halfPlaneCayley_continuousOn :
    ContinuousOn halfPlaneCayley {z : ℂ | 0 ≤ z.im} :=
  (continuousOn_id.sub continuousOn_const).div
    (continuousOn_id.add continuousOn_const) (fun _ hz => halfPlaneCayley_den_ne hz)

lemma halfPlaneCayley_injOn : InjOn halfPlaneCayley {z : ℂ | 0 ≤ z.im} := by
  intro z hz w hw he
  have hh := (div_eq_div_iff (halfPlaneCayley_den_ne hz) (halfPlaneCayley_den_ne hw)).mp he
  have hzero : (z-w)*(2*I)=0 := by linear_combination hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (by norm_num))

lemma halfPlaneCayley_norm_le {z : ℂ} (hz : 0 ≤ z.im) : ‖halfPlaneCayley z‖ ≤ 1 := by
  rw [halfPlaneCayley,norm_div]
  apply (div_le_one (norm_pos_iff.mpr (halfPlaneCayley_den_ne hz))).mpr
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.I_re,sub_zero,
    Complex.sub_im,Complex.I_im,Complex.add_re,add_zero,Complex.add_im]
  nlinarith

lemma halfPlaneCayley_norm_lt {z : ℂ} (hz : 0 < z.im) : ‖halfPlaneCayley z‖ < 1 := by
  rw [halfPlaneCayley,norm_div]
  apply (div_lt_one (norm_pos_iff.mpr (halfPlaneCayley_den_ne hz.le))).mpr
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.I_re,sub_zero,
    Complex.sub_im,Complex.I_im,Complex.add_re,add_zero,Complex.add_im]
  nlinarith

lemma halfPlaneCayley_real_norm (x : ℝ) : ‖halfPlaneCayley (x : ℂ)‖ = 1 := by
  rw [halfPlaneCayley,norm_div]
  have he : ‖(x : ℂ)-I‖ = ‖(x : ℂ)+I‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
  rw [he,div_self (norm_ne_zero_iff.mpr (halfPlaneCayley_den_ne (by simp)))]

lemma halfPlaneCayley_ne_one {z : ℂ} (hz : 0 ≤ z.im) : halfPlaneCayley z ≠ 1 := by
  intro he
  have hh := (div_eq_one_iff_eq (halfPlaneCayley_den_ne hz)).mp he
  have hi := congrArg Complex.im hh
  simp only [Complex.sub_im,Complex.add_im,Complex.I_im] at hi
  linarith

lemma halfPlaneCayley_zero : halfPlaneCayley 0 = -1 := by
  norm_num [halfPlaneCayley]

theorem halfPlaneCayley_tendsto_infinity :
    Tendsto halfPlaneCayley (cocompact ℂ) (𝓝 1) := by
  have hadd : Tendsto (fun z : ℂ => z+I) (cocompact ℂ) (cocompact ℂ) :=
    le_of_eq (Homeomorph.addRight I).map_cocompact
  have hinv : Tendsto (fun z : ℂ => (z+I)⁻¹) (cocompact ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (hadd.mono_right Metric.cobounded_eq_cocompact.ge)
  have hn : ∀ᶠ z : ℂ in cocompact ℂ, z+I ≠ 0 := by
    filter_upwards [(tendsto_norm_cocompact_atTop.comp hadd).eventually_gt_atTop 0] with z hz
    exact norm_pos_iff.mp hz
  have he : halfPlaneCayley =ᶠ[cocompact ℂ] (fun z => 1-(2*I)*(z+I)⁻¹) := by
    filter_upwards [hn] with z hz
    dsimp [halfPlaneCayley]
    field_simp
    ring
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℂ => (1:ℂ))
    (cocompact ℂ) (𝓝 1)).sub (hinv.const_mul (2*I))
  simpa only [mul_zero,sub_zero] using hh.congr' he.symm

end SLEExactGauge

end

end OAI
