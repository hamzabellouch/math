import OAI.Analysis.StrictMeans.JacobianMoments

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
namespace StrictInverseFirstPower
noncomputable section

lemma omitted_mobius_normalized {f : ℂ → ℂ} {c : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 1 - c * f z ≠ 0) :
    DifferentiableOn ℂ (fun z => f z / (1 - c * f z)) (ball 0 1) ∧
    InjOn (fun z => f z / (1 - c * f z)) (ball 0 1) ∧
    (f 0 / (1 - c * f 0) = 0) ∧
    deriv (fun z => f z / (1 - c * f z)) 0 = 1 := by
  refine ⟨hd.div ((differentiableOn_const (1 : ℂ)).sub (hd.const_mul c)) hn, ?_, by simp [h0], ?_⟩
  · intro z hz w hw he
    apply hi hz hw
    have he' := (div_eq_div_iff (hn z hz) (hn w hw)).mp he
    linear_combination he'
  · have hdf : HasDerivAt f 1 0 := by
      simpa only [h1] using (hd.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))).hasDerivAt
    have he := hdf.div ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) (hn 0 (by simp))
    convert he.deriv using 1; first | rfl | simp [h0]

lemma omitted_mobius_coefficient {f : ℂ → ℂ} {c : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    deriv (dslope (fun z => f z / (1 - c * f z)) 0) 0 =
      deriv (dslope f 0) 0 + c := by
  let g : ℂ → ℂ := fun z => f z / (1 - c * f z)
  have hd0 := hd.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hdf : HasDerivAt f 1 0 := by simpa only [h1] using hd0.hasDerivAt
  have hn0 : 1 - c * f 0 ≠ 0 := by simp [h0]
  have hgd : HasDerivAt g 1 0 := by
    convert hdf.div ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) hn0 using 1
    all_goals first | rfl | simp [h0]
  have hg0 : g 0 = 0 := by simp [g, h0]
  have he (z : ℂ) : dslope g 0 z = dslope f 0 z / (1 - c * f z) := by
    by_cases hz : z = 0
    · simp [hz, hgd.deriv, h0, h1]
    · simp only [dslope_of_ne _ hz, slope_def_field, sub_zero, hg0, h0]
      dsimp only [g]
      ring
  have hdU := ((Complex.differentiableOn_dslope
    (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))).mpr hd).differentiableAt
      (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hp := hdU.hasDerivAt.div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hdf.const_mul c)) hn0
  have hpe : HasDerivAt (dslope g 0) (deriv (dslope f 0) 0 + c) 0 := by
    convert hp using 1
    all_goals first | rfl | exact funext he | simp [h0, h1]
  exact hpe.deriv

theorem omitted_value_quarter {f : ℂ → ℂ} {w : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (hw : w ∉ f '' ball 0 1) :
    (1 / 4 : ℝ) ≤ ‖w‖ := by
  have hw0 : w ≠ 0 := by
    intro he
    apply hw
    exact ⟨0, by simp, by rw [h0, he]⟩
  have hn (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 1 - w⁻¹ * f z ≠ 0 := by
    intro he
    apply hw
    refine ⟨z, hz, ?_⟩
    have ha : w⁻¹ * f z = 1 := (sub_eq_zero.mp he).symm
    calc f z = w * (w⁻¹ * f z) := by rw [← mul_assoc, mul_inv_cancel₀ hw0, one_mul]
         _ = w := by rw [ha, mul_one]
  obtain ⟨hgd, hgi, hg0, hg1⟩ := omitted_mobius_normalized hd hi h0 h1 hn
  have ha := second_coefficient_le_two hd hi h0 h1
  have hb := second_coefficient_le_two hgd hgi hg0 hg1
  rw [omitted_mobius_coefficient hd h0 h1] at hb
  have hc : ‖w⁻¹‖ ≤ 4 := by
    calc ‖w⁻¹‖ = ‖(deriv (dslope f 0) 0 + w⁻¹) - deriv (dslope f 0) 0‖ := by ring_nf
         _ ≤ ‖deriv (dslope f 0) 0 + w⁻¹‖ + ‖deriv (dslope f 0) 0‖ := norm_sub_le _ _
         _ ≤ 4 := by linarith
  rw [norm_inv] at hc
  have hnpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hh := mul_le_mul_of_nonneg_right hc hnpos.le
  rw [inv_mul_cancel₀ (ne_of_gt hnpos)] at hh
  linarith

theorem koebe_quarter {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ball (0 : ℂ) (1 / 4) ⊆ f '' ball 0 1 := by
  intro w hw
  by_contra hn
  have hh := omitted_value_quarter hd hi h0 h1 hn
  simp only [mem_ball, dist_zero_right] at hw
  linarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma scale_disk_mem {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball 0 1) :
    (r : ℂ) * w ∈ ball (0 : ℂ) r := by
  simp only [mem_ball, dist_zero_right] at hw ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_lt_of_lt_one_right hr hw

theorem local_koebe_quarter {F : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ F (ball a r)) (hi : InjOn F (ball a r))
    (hn : deriv F a ≠ 0) :
    ball (F a) (r * ‖deriv F a‖ / 4) ⊆ F '' ball a r := by
  let d : ℂ := (r : ℂ) * deriv F a
  have hdne : d ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hn
  let g : ℂ → ℂ := fun w => (F (a + (r : ℂ) * w) - F a) / d
  have hm : MapsTo (fun w : ℂ => a + (r : ℂ) * w) (ball 0 1) (ball a r) := by
    intro w hw
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using scale_disk_mem hr hw
  have hcomp : DifferentiableOn ℂ (fun w => F (a + (r : ℂ) * w)) (ball 0 1) :=
    hd.comp (by fun_prop) hm
  have hgd : DifferentiableOn ℂ g (ball 0 1) := hcomp.sub_const _ |>.div_const _
  have hgi : InjOn g (ball 0 1) := by
    intro w hw u hu he
    have hh := hi (hm hw) (hm hu) (by
      have he' := (div_left_inj' hdne).mp he
      exact sub_left_injective he')
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') (add_left_cancel hh)
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : deriv g 0 = 1 := by
    have ha := (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    have hb : HasDerivAt (fun w : ℂ => a + (r : ℂ) * w) (r : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add a
    have he : a + (r : ℂ) * 0 = a := by simp
    rw [← he] at ha
    have h := ((ha.comp 0 hb).sub_const (F a)).div_const d
    have hh : HasDerivAt g (deriv F (a + (r : ℂ) * 0) * (r : ℂ) / d) 0 := h
    rw [hh.deriv, he]
    dsimp [d]
    field_simp [hn, Complex.ofReal_ne_zero.mpr hr.ne']
  intro ξ hξ
  have hnorm : ‖d‖ = r * ‖deriv F a‖ := by simp [d, abs_of_pos hr]
  have hh : (ξ - F a) / d ∈ ball (0 : ℂ) (1 / 4) := by
    simp only [mem_ball, dist_eq_norm] at hξ
    simp only [mem_ball, dist_zero_right, norm_div]
    rw [div_lt_iff₀ (norm_pos_iff.mpr hdne), hnorm]
    linarith
  obtain ⟨w, hw, he⟩ := koebe_quarter hgd hgi hg0 hg1 hh
  refine ⟨a + r * w, hm hw, ?_⟩
  exact sub_left_injective ((div_left_inj' hdne).mp he)

lemma disk_outside_half_norm_lower {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {z : ℂ}
    (hz : z ∈ ball 0 1) (hhalf : 1 / 2 ≤ ‖z‖) : 1 / 8 ≤ ‖f z‖ := by
  by_contra hh
  have hsub : ball (0 : ℂ) (1 / 2) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have him := local_koebe_quarter (F := f) (a := 0) (r := 1 / 2) (by norm_num)
    (hd.mono hsub) (hi.mono hsub) (by rw [h1]; exact one_ne_zero)
  have hball : f z ∈ ball (f 0) ((1 / 2) * ‖deriv f 0‖ / 4) := by
    simp only [h0, h1, norm_one, mul_one, mem_ball, dist_zero_right]
    exact lt_of_lt_of_le (lt_of_not_ge hh) (by norm_num)
  obtain ⟨w, hw, he⟩ := him hball
  have hwz : w = z := hi (hsub hw) hz he
  rw [hwz, mem_ball, dist_zero_right] at hw
  exact (not_lt_of_ge hhalf) hw

lemma halfPlaneFunction_outside_norm_lower (f : DiskFamily) {z : ℂ} (hz : 0 < z.im)
    (hhalf : 1 / 2 ≤ ‖cayleyToDisk z‖) : 1 / 4 ≤ ‖halfPlaneFunction f z‖ := by
  have hh := disk_outside_half_norm_lower f.property.1 f.property.2.1
    f.property.2.2.1 f.property.2.2.2 (cayleyToDisk_mem hz) hhalf
  simp only [halfPlaneFunction, norm_mul, norm_ofNat, norm_I, mul_one]
  linarith

end
end StrictInverseFirstPower

end

end OAI
