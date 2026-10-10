import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelTorus

namespace OAI

/-! The explicit arithmetic model is an actual L2 function on the
high cusp, including its nonzero constant term. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaStrip_height_rpow_integrable {r : ℝ} (hr : r<2) :
    IntegrableOn (fun p : CubicThetaPoint => p.val.2^r)
      (cubicThetaCuspStrip 2) cubicThetaPointMeasure := by
  have hh : IntegrableOn (fun _ : ℂ => (1:ℝ)) cubicThetaHorizontalCell :=
    integrableOn_const cubicThetaHorizontalCell_measure_ne_top
  have hv : IntegrableOn (fun v : ℝ => v^(r-3)) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hm := hh.mul_prod hv
  rw [Measure.prod_restrict] at hm
  apply (cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)
    (fun y => y.2^r)).mpr
  rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)]
  apply hm.congr
  filter_upwards [ae_restrict_mem
    (cubicThetaHorizontalCell_measurable.prod measurableSet_Ioi)] with y hy
  rw [one_mul,Real.rpow_sub (by have hp : (2:ℝ)<y.2 := hy.2; linarith)]
  simpa only [Nat.cast_ofNat] using
    congrArg (fun t : ℝ => y.2^r/t) (Real.rpow_natCast y.2 3)

lemma cubicThetaArithmeticModel_constant_memLp :
    MemLp (fun p : CubicThetaPoint => ((cubicThetaConstant*p.val.2^(2/3:ℝ):ℝ):ℂ))
      2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  have hc : Continuous (fun p : CubicThetaPoint =>
      ((cubicThetaConstant*p.val.2^(2/3:ℝ):ℝ):ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact Complex.continuous_ofReal.continuousAt.comp
      (((continuousAt_snd.comp continuous_subtype_val.continuousAt).rpow_const
        (Or.inl p.property.ne')).const_mul cubicThetaConstant)
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  apply ((cubicThetaStrip_height_rpow_integrable (r:=(4/3:ℝ)) (by norm_num)).const_mul
    (cubicThetaConstant^2)).congr
  filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp
  have hv : 0<p.val.2 := p.property
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow,
    ←Real.rpow_mul_natCast hv.le]
  norm_num

lemma cubicThetaArithmeticModel_remainder_memLp :
    MemLp (fun p : CubicThetaPoint => cubicThetaNonconstant cubicThetaArithmeticCoefficient p.val)
      2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) := by
  have hc : Continuous (fun p : CubicThetaPoint =>
      cubicThetaNonconstant cubicThetaArithmeticCoefficient p.val) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaNonconstant_continuousAt (by norm_num : (0:ℝ)≤81)
      cubicThetaArithmeticCoefficient_bound p.property).comp continuous_subtype_val.continuousAt
  apply MemLp.of_bound hc.aestronglyMeasurable (cubicThetaExpConstant 81)
  filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable 2)] with p hp
  have hv : 1≤p.val.2 := by have h : (2:ℝ)<p.val.2 := hp.1; linarith
  have he := cubicThetaAuxiliarySeries_exponential_bound 0 p.val.1 hv
  rw [cubicThetaAuxiliarySeries,cubicThetaCuspCoefficient_zero] at he
  apply he.trans
  apply mul_le_of_le_one_right
  · have hb := cubicThetaAuxiliarySeries_exponential_bound 0 0 (v:=1) (by norm_num)
    exact nonneg_of_mul_nonneg_left ((_root_.norm_nonneg _).trans hb)
      (Real.exp_pos _)
  · apply Real.exp_le_one_iff.mpr
    have := Real.pi_pos
    nlinarith

lemma cubicThetaArithmeticModel_memLp (A : ℂ) :
    MemLp (fun p : CubicThetaPoint => cubicThetaArithmeticModel A p.val)
      2 (cubicThetaPointMeasure.restrict (cubicThetaCuspStrip 2)) :=
  cubicThetaArithmeticModel_constant_memLp.add
    (cubicThetaArithmeticModel_remainder_memLp.const_mul A)

def cubicThetaArithmeticModelStrip (A : ℂ) : CubicThetaStripL2 :=
  (cubicThetaArithmeticModel_memLp A).toLp _

end CubicFirstMoment

end

end OAI
