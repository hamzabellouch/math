import OAI.Analysis.StrictMeans.AreaTails

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma im_lower_of_mem_ball {z w : ℂ} {r : ℝ} (hw : w ∈ ball z r) :
    z.im - r < w.im := by
  have hn : ‖w - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have h := (abs_le.mp (Complex.abs_im_le_norm (w - z))).1
  simp only [sub_im] at h
  linarith

lemma ball_halfplane_subset (z : UpperHalfPlane) :
    ball (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hh := im_lower_of_mem_ball hw
  change z.im - z.im / 2 < w.im at hh
  change 0 < w.im
  linarith [z.im_pos]

lemma norm_large_cayley {w : ℂ} (hw : 0 < w.im) (hn : 3 ≤ ‖w‖) :
    1 / 2 ≤ ‖cayleyToDisk w‖ := by
  rw [cayleyToDisk, norm_div, le_div_iff₀ (norm_pos_iff.mpr (add_I_ne_zero hw))]
  have ha : ‖w + I‖ ≤ ‖w‖ + 1 := by simpa using norm_add_le w I
  have hb : ‖w‖ - 1 ≤ ‖w - I‖ := by simpa using norm_sub_norm_le w I
  linarith

lemma far_ball_outside (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖) :
    ball (z : ℂ) (z.im / 2) ⊆ outsideCenter := by
  intro w hw
  have hp := ball_halfplane_subset z hw
  refine ⟨hp, norm_large_cayley hp ?_⟩
  have hn : ‖w - (z : ℂ)‖ < z.im / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
  have htri : ‖(z : ℂ)‖ ≤ ‖w‖ + ‖w - (z : ℂ)‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub w (z : ℂ)
  have hi : z.im ≤ ‖(z : ℂ)‖ := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  linarith

lemma omitted_local_quarter_bound {F : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ F (ball z r)) (hi : InjOn F (ball z r))
    (hne : deriv F z ≠ 0) (homit : 0 ∉ F '' ball z r) :
    r * ‖deriv F z‖ / 4 ≤ ‖F z‖ := by
  by_contra hh
  apply homit
  apply local_koebe_quarter hr hd hi hne
  simpa only [mem_ball, dist_zero_left] using lt_of_not_ge hh

lemma far_derivative_bound (f : DiskFamily) (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖) :
    z.im * ‖deriv (halfPlaneFunction f) z‖ ≤ 8 * ‖halfPlaneFunction f z‖ := by
  have hs := ball_halfplane_subset z
  have h := omitted_local_quarter_bound (F := halfPlaneFunction f) (z := z)
    (half_pos z.im_pos) ((halfPlaneFunction_differentiableOn f).mono hs)
    ((halfPlaneFunction_injOn f).mono hs) (halfPlaneFunction_deriv_ne_zero f z.im_pos) (by
      rintro ⟨w, hw, he⟩
      have hl := halfPlaneFunction_outside_norm_lower f (far_ball_outside z hz hw).1
        (far_ball_outside z hz hw).2
      rw [he, norm_zero] at hl
      norm_num at hl)
  linarith

lemma halfPlaneFunction_small_ball_bound (f : DiskFamily) {u : ℂ}
    (hu : u ∈ ball I (1 / 4)) : ‖halfPlaneFunction f u‖ ≤ 12 := by
  have hn : ‖u - I‖ < 1 / 4 := by simpa only [mem_ball, dist_eq_norm] using hu
  have him : 0 < u.im := by
    have hh := im_lower_of_mem_ball hu
    simp only [I_im] at hh
    linarith
  have hden : 7 / 4 ≤ ‖u + I‖ := by
    have hh := norm_add_le (u + I) (I - u)
    rw [show u + I + (I - u) = (2 : ℂ) * I by ring, norm_sub_rev] at hh
    norm_num at hh
    linarith
  have hm : ‖cayleyToDisk u‖ ≤ 1 / 2 := by
    rw [cayleyToDisk, norm_div, div_le_iff₀ (by linarith : 0 < ‖u + I‖)]
    linarith
  have h := disk_lipschitz_bound f.property.1 f.property.2.1 f.property.2.2.2
    (r := 1 / 2) (z := 0) (w := cayleyToDisk u) (by norm_num) (by norm_num) hm
  rw [f.property.2.2.1, sub_zero, sub_zero] at h
  norm_num at h
  have hb : ‖diskExtension f.val (cayleyToDisk u)‖ ≤ 6 := by linarith
  simp only [halfPlaneFunction, norm_mul, norm_ofNat, norm_I, mul_one]
  linarith

lemma nearbyFunction_bound (f : DiskFamily) (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖)
    {w : ℂ} (hw : w ∈ ball (z : ℂ) (z.im / 4)) :
    ‖halfPlaneFunction f w‖ ≤ 97 * ‖halfPlaneFunction f z‖ := by
  let u : ℂ := (w - (z.re : ℂ)) / (z.im : ℂ)
  have hye : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have heu : u - I = (w - (z : ℂ)) / (z.im : ℂ) := by
    dsimp [u]
    field_simp
    rw [← Complex.re_add_im (z : ℂ)]
    change w - (z.re : ℂ) - (z.im : ℂ) * I = w - ((z.re : ℂ) + (z.im : ℂ) * I)
    ring
  have hu : u ∈ ball I (1 / 4) := by
    simp only [mem_ball, dist_eq_norm, heu, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos z.im_pos]
    rw [div_lt_iff₀ z.im_pos]
    have hn : ‖w - (z : ℂ)‖ < z.im / 4 := by simpa only [mem_ball, dist_eq_norm] using hw
    linarith
  have huim : 0 < u.im := by
    have hh := im_lower_of_mem_ball hu
    simp only [I_im] at hh
    linarith
  have hew : affineAt z u = w := by dsimp [affineAt, u]; field_simp; ring
  have he := halfPlaneFunction_rebase f z huim
  rw [hew] at he
  have hb := halfPlaneFunction_small_ball_bound (rebase f z) hu
  rw [he, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos z.im_pos] at hb
  have hdn : 0 < ‖deriv (halfPlaneFunction f) z‖ :=
    norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  have hmul := (div_le_iff₀ (mul_pos z.im_pos hdn)).mp hb
  have hder := far_derivative_bound f z hz
  have htri := norm_le_norm_add_norm_sub (halfPlaneFunction f z) (halfPlaneFunction f w)
  rw [norm_sub_rev] at htri
  linarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma inverse_cube_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b⁻¹ ^ 3 ≤ a⁻¹ ^ 3 := by
  exact pow_le_pow_left₀ (inv_nonneg.mpr (ha.le.trans hab)) (inv_anti₀ ha hab) 3

lemma nearbyAreaDensity_lower (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖)
    {w : ℂ} (hw : w ∈ ball (z : ℂ) (z.im / 4)) :
    ENNReal.ofReal ((z.im / 2) ^ β * (97 * ‖halfPlaneFunction f z‖)⁻¹ ^ 3) ≤
      ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w) := by
  have hwhalf : w ∈ ball (z : ℂ) (z.im / 2) :=
    ball_subset_ball (by linarith [z.im_pos]) hw
  have hwo := far_ball_outside z hz hwhalf
  rw [halfPlaneProjection_of_pos hwo.1, inverseCubeValue,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hwo.1.le β)]
  apply ENNReal.ofReal_le_ofReal
  have hy : z.im / 2 ≤ w.im := by
    have hh := im_lower_of_mem_ball hw
    rw [UpperHalfPlane.coe_im] at hh
    linarith [z.im_pos]
  have hfpos : 0 < ‖halfPlaneFunction f w‖ := lt_of_lt_of_le (by norm_num)
    (halfPlaneFunction_outside_norm_lower f hwo.1 hwo.2)
  exact mul_le_mul (Real.rpow_le_rpow (by positivity) hy hβ)
    (inverse_cube_lower hfpos (nearbyFunction_bound f z hz hw)) (by positivity)
    (Real.rpow_nonneg hwo.1.le β)

lemma ball_lower_bound_area_tail (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖) :
    ENNReal.ofReal ((z.im / 2) ^ β * (97 * ‖halfPlaneFunction f z‖)⁻¹ ^ 3) *
      (ENNReal.ofReal (z.im / 4) ^ 2 * NNReal.pi) ≤
      ∫⁻ w in ball (z : ℂ) (z.im / 4),
        ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w) := by
  rw [← Complex.volume_ball, ← setLIntegral_const]
  exact setLIntegral_mono' measurableSet_ball (fun w hw => nearbyAreaDensity_lower f β hβ z hz hw)

lemma infinity_local_constant_identity (β y a : ℝ) (hy : 0 < y) (ha : 0 < a) :
    y ^ (β + 2) * a⁻¹ ^ 3 =
      (16 * 97 ^ (3 : ℕ) * (2 : ℝ) ^ β / Real.pi) *
        (((y / 2) ^ β * (97 * a)⁻¹ ^ 3) * ((y / 4) ^ (2 : ℕ) * Real.pi)) := by
  rw [Real.rpow_add hy, Real.rpow_two, Real.div_rpow hy.le (by norm_num)]
  have hp : (2 : ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) β).ne'
  field_simp
  ring

lemma ball_source_norm_lower (z : UpperHalfPlane) {w : ℂ}
    (hw : w ∈ ball (z : ℂ) (z.im / 4)) : ‖(z : ℂ)‖ / 2 ≤ ‖w‖ := by
  have hn : ‖w - (z : ℂ)‖ < z.im / 4 := by simpa only [mem_ball, dist_eq_norm] using hw
  have htri := norm_le_norm_add_norm_sub w (z : ℂ)
  have hi : z.im ≤ ‖(z : ℂ)‖ := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  linarith [z.im_pos]

lemma infinity_local_tail_bound (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖) :
    ENNReal.ofReal (z.im ^ (β + 2) * ‖halfPlaneFunction f z‖⁻¹ ^ 3) ≤
      ENNReal.ofReal (16 * 97 ^ (3 : ℕ) * (2 : ℝ) ^ β / Real.pi) *
        ∫⁻ w in outsideCenter ∩ {w : ℂ | ‖(z : ℂ)‖ / 2 ≤ ‖w‖},
          ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w) := by
  have hzout := far_ball_outside z hz (mem_ball_self (half_pos z.im_pos))
  have hzpos : 0 < ‖halfPlaneFunction f z‖ := lt_of_lt_of_le (by norm_num)
    (halfPlaneFunction_outside_norm_lower f hzout.1 hzout.2)
  have hv : ENNReal.ofReal ((z.im / 4) ^ (2 : ℕ) * Real.pi) =
      ENNReal.ofReal (z.im / 4) ^ 2 * NNReal.pi := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [infinity_local_constant_identity β z.im _ z.im_pos hzpos,
    ENNReal.ofReal_mul (p := 16 * 97 ^ (3 : ℕ) * (2 : ℝ) ^ β / Real.pi) (by positivity),
    ENNReal.ofReal_mul (p := (z.im / 2) ^ β * (97 * ‖halfPlaneFunction f z‖)⁻¹ ^ 3) (by positivity), hv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (ball_lower_bound_area_tail f β hβ z hz).trans
    (lintegral_mono_set (fun w hw => ⟨far_ball_outside z hz
      (ball_subset_ball (by linarith [z.im_pos]) hw), ball_source_norm_lower z hw⟩))

lemma tendsto_weighted_area_tail_zero (f : DiskFamily) (β : ℝ)
    (hfin : weightedAreaTail β f < ∞) :
    Tendsto (fun R : ℝ => ∫⁻ w in outsideCenter ∩ {w : ℂ | R ≤ ‖w‖},
      ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w)) atTop (𝓝 0) := by
  let d : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w)
  have hd : Measurable d := (measurable_areaTail_density β).comp
    (f := fun w : ℂ => (f, w)) (measurable_const.prodMk measurable_id)
  have hm (R : ℝ) : MeasurableSet {w : ℂ | R ≤ ‖w‖} :=
    measurableSet_le measurable_const (by fun_prop)
  have hh := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict outsideCenter)
    (l := atTop) (F := fun R : ℝ => {w : ℂ | R ≤ ‖w‖}.indicator d) (f := fun _ => 0)
    d (Eventually.of_forall (fun R => hd.indicator (hm R)))
    (Eventually.of_forall (fun _ => Eventually.of_forall (fun w => indicator_le_self' (fun _ _ => bot_le) w)))
    (ne_of_lt hfin) (Eventually.of_forall (fun w => ?_))
  · simpa only [lintegral_indicator (hm _), lintegral_zero,
      Measure.restrict_restrict (hm _), inter_comm] using hh
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop ‖w‖] with R hR
    exact (indicator_of_notMem (by simpa using not_le.mpr hR) d).symm

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

theorem escape_at_infinity (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ∞) {ι : Type*} {l : Filter ι}
    (Z : ι → UpperHalfPlane) (hZ : Tendsto (fun a => ‖(Z a : ℂ)‖) l atTop) :
    Tendsto (fun a => (Z a).im ^ ((β + 2) / 3) / ‖halfPlaneFunction f (Z a)‖) l (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (16 * 97 ^ (3 : ℕ) * (2 : ℝ) ^ β / Real.pi)
  have htail := (tendsto_weighted_area_tail_zero f β hfin).comp
    (hZ.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hu : Tendsto (fun a => C * ∫⁻ w in outsideCenter ∩ {w : ℂ | ‖(Z a : ℂ)‖ / 2 ≤ ‖w‖},
      ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w)) l (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using ENNReal.Tendsto.const_mul (a := C) htail
      (Or.inr ENNReal.ofReal_ne_top)
  have he : ∀ᶠ a in l, 6 ≤ ‖(Z a : ℂ)‖ := hZ.eventually (eventually_ge_atTop 6)
  have hsmall : Tendsto (fun a => ENNReal.ofReal
      ((Z a).im ^ (β + 2) * ‖halfPlaneFunction f (Z a)‖⁻¹ ^ 3)) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall (fun _ => bot_le))
      (he.mono (fun a ha => infinity_local_tail_bound f β hβ (Z a) ha))
  have hr : Tendsto (fun a => (Z a).im ^ (β + 2) * ‖halfPlaneFunction f (Z a)‖⁻¹ ^ 3) l (𝓝 0) := by
    have hh := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp hsmall
    simpa only [Function.comp_def, ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (Z _).im ^ (β + 2) * ‖halfPlaneFunction f (Z _)‖⁻¹ ^ 3)] using hh
  have hc (a : ι) : (Z a).im ^ (β + 2) * ‖halfPlaneFunction f (Z a)‖⁻¹ ^ 3 =
      ((Z a).im ^ ((β + 2) / 3) / ‖halfPlaneFunction f (Z a)‖) ^ (3 : ℕ) := by
    rw [div_pow, ← Real.rpow_mul_natCast (Z a).im_pos.le]
    rw [show (β + 2) / 3 * (3 : ℕ) = β + 2 by ring]
    simp only [div_eq_mul_inv, inv_pow]
  have hp := hr.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)
  convert hp using 1
  funext a
  rw [hc]
  exact (Real.pow_rpow_inv_natCast (n := 3) (by positivity) (by norm_num)).symm

theorem bounded_strip_preimage (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ∞) {ε R : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ z : UpperHalfPlane, ε ≤ z.im → ‖halfPlaneFunction f z‖ ≤ R → ‖(z : ℂ)‖ ≤ M := by
  by_contra h
  push Not at h
  choose Z hZ using fun n : ℕ => h (max 6 n)
  have hnorm : Tendsto (fun n => ‖(Z n : ℂ)‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_right (6 : ℝ) n).trans (hZ n).2.2.le)
      tendsto_natCast_atTop_atTop
  have he := escape_at_infinity f β hβ hfin Z hnorm
  have kpos : 0 < (β + 2) / 3 := by linarith
  have Rpos : 0 < R := by
    have hzfar : 6 ≤ ‖(Z 0 : ℂ)‖ := (le_max_left (6 : ℝ) ((0 : ℕ) : ℝ)).trans (hZ 0).2.2.le
    have hzo := far_ball_outside (Z 0) hzfar (mem_ball_self (half_pos (Z 0).im_pos))
    exact lt_of_lt_of_le ((by norm_num : (0 : ℝ) < 1 / 4).trans_le
      (halfPlaneFunction_outside_norm_lower f hzo.1 hzo.2)) (hZ 0).2.1
  have hpos : 0 < ε ^ ((β + 2) / 3) / R := div_pos (Real.rpow_pos_of_pos hε _) Rpos
  have hlo : ∀ n, ε ^ ((β + 2) / 3) / R ≤
      (Z n).im ^ ((β + 2) / 3) / ‖halfPlaneFunction f (Z n)‖ := by
    intro n
    have hzfar : 6 ≤ ‖(Z n : ℂ)‖ := (le_max_left 6 (n : ℝ)).trans (hZ n).2.2.le
    have hzo := far_ball_outside (Z n) hzfar (mem_ball_self (half_pos (Z n).im_pos))
    have hv : 0 < ‖halfPlaneFunction f (Z n)‖ := (by norm_num : (0 : ℝ) < 1 / 4).trans_le
      (halfPlaneFunction_outside_norm_lower f hzo.1 hzo.2)
    exact div_le_div₀ (by positivity) (Real.rpow_le_rpow hε.le (hZ n).1 kpos.le) hv (hZ n).2.1
  exact (not_le_of_gt hpos) (ge_of_tendsto' he hlo)

lemma bounded_preimage_height (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ∞) (R : ℝ) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : UpperHalfPlane, ‖halfPlaneFunction f z‖ ≤ R → z.im ≤ Y := by
  obtain ⟨M, hM⟩ := bounded_strip_preimage f β hβ hfin (ε := 1) (R := R) zero_lt_one
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun z hz => ?_⟩
  by_cases h : 1 ≤ z.im
  · exact ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans
      ((hM z h hz).trans (le_max_right _ _))
  · exact (le_of_not_ge h).trans (le_max_left _ _)

lemma compact_strip_preimage_plane (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ∞) {ε : ℝ} (hε : 0 < ε) {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {z : ℂ | ε ≤ z.im ∧ halfPlaneFunction f z ∈ K} := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨M, hM⟩ := bounded_strip_preimage f β hβ hfin (R := R) hε
  have hs : IsClosed {z : ℂ | ε ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hc : ContinuousOn (halfPlaneFunction f) {z : ℂ | ε ≤ z.im} :=
    (halfPlaneFunction_differentiableOn f).continuousOn.mono (fun z hz => hε.trans_le hz)
  apply (isCompact_closedBall (0 : ℂ) M).of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed hs hK.isClosed)
  intro z hz
  have hp : 0 < z.im := hε.trans_le hz.1
  have hn : ‖halfPlaneFunction f z‖ ≤ R := by
    simpa only [mem_closedBall, dist_zero_right] using hR hz.2
  simpa only [mem_closedBall, dist_zero_right] using hM ⟨z, hp⟩ hz.1 hn

end
end StrictInverseFirstPower

end

end OAI
