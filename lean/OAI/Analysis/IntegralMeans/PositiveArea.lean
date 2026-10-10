import OAI.Analysis.IntegralMeans.SmoothMeans

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma schlicht_bracketSq_growth {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    bracketSq (f z) ≤ 2*(1-‖z‖)^(-4:ℝ) := by
  have hr : ‖z‖ < 1 := by simpa [disk] using hz
  have hd : 0 < 1-‖z‖ := by linarith
  have hg := schlicht_growth_upper hf hz
  have hb : ‖f z‖ ≤ 1/(1-‖z‖)^2 := hg.trans (div_le_div_of_nonneg_right hr.le (sq_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hδ : (1-‖z‖)^4 ≤ 1 := pow_le_one₀ hd.le (by nlinarith [norm_nonneg z])
  rw [bracketSq_eq,Real.rpow_neg hd.le]
  norm_num only [Real.rpow_ofNat]
  rw [inv_eq_one_div]
  have hdiv : (1/(1-‖z‖)^2)^2 = 1/(1-‖z‖)^4 := by field_simp
  rw [hdiv] at hs
  have hh : 1 ≤ 1/(1-‖z‖)^4 := (le_div_iff₀ (pow_pos hd _)).mpr (by simpa using hδ)
  linarith

lemma continuousOn_smoothPower_comp {f : ℂ → ℂ} (hf : Schlicht f) (a : ℝ) :
    ContinuousOn (fun z => smoothPower a (f z)) disk :=
  (smoothPower_contDiff a 0).continuous.comp_continuousOn hf.1.1.continuousOn

lemma schlicht_function_area {f : ℂ → ℂ} (hf : Schlicht f) {a : ℝ} (ha : a < 1/2) :
    IntegrableOn (fun z => bracketSq (f z)^a) disk := by
  obtain ⟨q,hq0,hq4⟩ := exists_between (show max (0:ℝ) (a-1/4) < 1/4 by
    exact max_lt (by norm_num) (by linarith))
  have hq : 0 < q := (le_max_left _ _).trans_lt hq0
  have haq : a-q < 1/4 := by have hh := (le_max_right _ _).trans_lt hq0; linarith
  obtain ⟨C,hC,hmean⟩ := schlicht_smooth_means hf hq hq4
  have hc : ContinuousOn (fun z => bracketSq (f z)^a) disk := continuousOn_smoothPower_comp hf a
  have hm (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      IntervalIntegrable (fun θ => bracketSq (f (circlePoint r θ))^a) volume (-Real.pi) Real.pi :=
    (continuous_circle_smoothPower hf a r hr.le hr1).intervalIntegrable _ _
  have hqn (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      IntervalIntegrable (fun θ => smoothPower q (f (circlePoint r θ))) volume (-Real.pi) Real.pi :=
    (continuous_circle_smoothPower hf q r hr.le hr1).intervalIntegrable _ _
  by_cases haq0 : a ≤ q
  · apply integrableOn_disk_of_power_circle_bound hc (fun z _ => Real.rpow_nonneg (bracketSq_pos _).le _)
      (C := C) (a := 0) hC.le (by norm_num)
    intro r hr hr1
    rw [circle_lintegral_eq (F := fun z => bracketSq (f z)^a)
      (continuous_circle_smoothPower hf a r hr.le hr1)
      (fun θ => Real.rpow_nonneg (bracketSq_pos _).le _),Real.rpow_zero,mul_one]
    apply ENNReal.ofReal_le_ofReal
    refine (intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]) (hm r hr hr1) (hqn r hr hr1) ?_).trans (hmean r hr hr1)
    intro θ _
    exact Real.rpow_le_rpow_of_exponent_le (by rw [bracketSq_eq]; nlinarith [sq_nonneg ‖f (circlePoint r θ)‖]) haq0
  · have haqp : 0 < a-q := by linarith
    apply integrableOn_disk_of_power_circle_bound hc (fun z _ => Real.rpow_nonneg (bracketSq_pos _).le _)
      (C := (2:ℝ)^(a-q)*C) (a := -4*(a-q)) (by positivity) (by linarith)
    intro r hr hr1
    have hd : 0 < 1-r := by linarith
    rw [circle_lintegral_eq (F := fun z => bracketSq (f z)^a)
      (continuous_circle_smoothPower hf a r hr.le hr1)
      (fun θ => Real.rpow_nonneg (bracketSq_pos _).le _)]
    apply ENNReal.ofReal_le_ofReal
    have hi : (∫ θ in -Real.pi..Real.pi, bracketSq (f (circlePoint r θ))^a) ≤
        ∫ θ in -Real.pi..Real.pi, ((2:ℝ)^(a-q)*(1-r)^(-4*(a-q)))*smoothPower q (f (circlePoint r θ)) := by
      apply intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]) (hm r hr hr1) ((hqn r hr hr1).const_mul _)
      intro θ _
      have hz : circlePoint r θ ∈ disk := by simpa [disk,circlePoint_norm,abs_of_pos hr] using hr1
      have hg := schlicht_bracketSq_growth hf hz
      rw [circlePoint_norm,abs_of_pos hr] at hg
      have hp := Real.rpow_le_rpow (bracketSq_pos _).le hg haqp.le
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _),← Real.rpow_mul hd.le] at hp
      calc
        _ = bracketSq (f (circlePoint r θ))^(a-q)*bracketSq (f (circlePoint r θ))^q := by
          rw [← Real.rpow_add (bracketSq_pos _),sub_add_cancel]
        _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (bracketSq_pos _).le _)
    rw [intervalIntegral.integral_const_mul] at hi
    calc
      _ ≤ ((2:ℝ)^(a-q)*(1-r)^(-4*(a-q)))*(∫ θ in -Real.pi..Real.pi, smoothPower q (f (circlePoint r θ))) := hi
      _ ≤ ((2:ℝ)^(a-q)*(1-r)^(-4*(a-q)))*C := mul_le_mul_of_nonneg_left (hmean r hr hr1) (by positivity)
      _ = _ := by ring

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma bracketSq_negative_integrable {η : ℝ} (hη : 0 < η) :
    Integrable (fun z : ℂ => bracketSq z^(-1-η)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 2+2*η)
    (by norm_num [Complex.finrank_real_complex]; linarith)
  convert! h using 1
  ext z
  rw [bracketSq_eq]
  congr 1
  ring

lemma schlicht_weighted_derivative_integrable {f : ℂ → ℂ} (hf : Schlicht f) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun z => ‖deriv f z‖^2*bracketSq (f z)^(-1-η)) disk := by
  have hc : ContinuousOn (fun z => ‖deriv f z‖^2*bracketSq (f z)^(-1-η)) disk :=
    ((continuousOn_deriv_univalent hf.1).norm.pow 2).mul (continuousOn_smoothPower_comp hf _)
  have hn : ∀ z : ℂ, 0 ≤ ‖deriv f z‖^2*bracketSq (f z)^(-1-η) :=
    fun z => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _)
  refine ⟨hc.aestronglyMeasurable Metric.isOpen_ball.measurableSet,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mpr
  have hh := conformal_lintegral_le Metric.isOpen_ball.measurableSet
    (fun z hz => hf.1.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)) hf.1.2
    (fun w => ENNReal.ofReal (bracketSq w^(-1-η)))
  simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)] at hh
  refine lt_of_le_of_lt hh ?_
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun z : ℂ => Real.rpow_nonneg (bracketSq_pos z).le (-1-η)))).mp
      (bracketSq_negative_integrable hη).hasFiniteIntegral

lemma schlicht_positive_area {f : ℂ → ℂ} (hf : Schlicht f) {t : ℝ}
    (ht : 0 < t) (ht2 : t < 2/3) : IntegrableOn (fun z => ‖deriv f z‖^t) disk := by
  let q := t/2
  let η := (1-3*q)/(4*q)
  let a := (1+η)*q/(1-q)
  have hq : 0 < q := by dsimp [q]; linarith
  have hq3 : q < 1/3 := by dsimp [q]; linarith
  have hq1 : q < 1 := by linarith
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have ha : a < 1/2 := by
    dsimp [a]
    apply (div_lt_iff₀ (by linarith : 0 < 1-q)).mpr
    have he : (1+η)*q = (1+q)/4 := by dsimp [η]; field_simp; ring
    rw [he]
    linarith
  let A : ℂ → ℝ := fun z => ‖deriv f z‖^2*bracketSq (f z)^(-1-η)
  let B : ℂ → ℝ := fun z => bracketSq (f z)^a
  apply integrableOn_geometric_product Metric.isOpen_ball.measurableSet
    (A := A) (B := B) (schlicht_weighted_derivative_integrable hf hη)
    (schlicht_function_area hf ha)
    ((continuousOn_deriv_norm_rpow hf.1 t).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
    hq.le hq1.le
  · intro z _hz
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _)
  · intro z _hz
    exact Real.rpow_nonneg (bracketSq_pos _).le _
  · intro z _hz
    dsimp [A,B]
    rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _),
      ← Real.rpow_natCast ‖deriv f z‖ 2,← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_mul (bracketSq_pos _).le,← Real.rpow_mul (bracketSq_pos _).le]
    have he : (-1-η)*q+a*(1-q) = 0 := by
      dsimp [a]
      rw [div_mul_cancel₀ _ (by linarith : 1-q ≠ 0)]
      ring
    have htq : (2:ℝ)*q = t := by dsimp [q]; ring
    norm_num only [Nat.cast_ofNat] at *
    rw [htq]
    calc
      _ = ‖deriv f z‖^t*1 := by ring
      _ = ‖deriv f z‖^t*(bracketSq (f z)^((-1-η)*q)*bracketSq (f z)^(a*(1-q))) := by
        rw [← Real.rpow_add (bracketSq_pos _),he,Real.rpow_zero]
      _ = _ := by ring

end Brennan

end

end OAI
