import OAI.Analysis.LipschitzHilbert.Fourier.ShortVerticalDifference

namespace OAI

/-! The short vertical FTC error is controlled in L1 by the vertical
Schwartz derivative and the explicit sampling distortion. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortVerticalDifference_l1 (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (t : ℝ) (ht : |t|≤1/4) :
    Integrable (shortVerticalDifference f u t) planeMeasure ∧
      (∫ z, ‖shortVerticalDifference f u t z‖ ∂planeMeasure)≤
        4*|t| *(∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure) := by
  let nu : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
  let G := fun p : ℝ×(ℝ×ℝ) =>
    verticalSchwartzDeriv f (p.2.1-t,p.2.2-p.1*t*u p.2)
  have hum := hu.continuous.measurable
  have hGm : Measurable G := (verticalSchwartzDeriv f).continuous.measurable.comp (by fun_prop)
  have htheta : ∀ᵐ theta ∂nu, theta∈Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hslice (theta : ℝ) (hth : theta∈Ioc (0:ℝ) 1) :
      Integrable (fun z => ‖G (theta,z)‖) planeMeasure ∧
      (∫ z, ‖G (theta,z)‖ ∂planeMeasure)≤4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure := by
    have hs := scaledSlope_lipschitz u hu theta hth.1.le hth.2
    have h := planar_integral_comp_le_four (verticalSampling (fun z => theta*u z) t t 0)
      (verticalSampling_measurable _ hs.continuous.measurable t t 0)
      (verticalSampling_antilipschitz _ hs t t 0 ht)
      (fun z => ‖verticalSchwartzDeriv f z‖) (verticalSchwartzDeriv f).integrable.norm
      (fun _ => norm_nonneg _)
    simpa only [G,Function.comp_def,verticalSampling,sub_zero,mul_assoc,mul_left_comm t theta] using h
  have hGi : Integrable G (nu.prod planeMeasure) := by
    apply (integrable_prod_iff hGm.aestronglyMeasurable).2
    constructor
    · filter_upwards [htheta] with theta hth
      exact (integrable_norm_iff (hGm.comp (by fun_prop)).aestronglyMeasurable).1 (hslice theta hth).1
    · apply (integrable_const (4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure)).mono'
        hGm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [htheta] with theta hth
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hslice theta hth).2
  have hDm : Measurable (shortVerticalDifference f u t) := by
    unfold shortVerticalDifference
    exact (f.continuous.measurable.comp (by fun_prop)).sub
      (f.continuous.measurable.comp (by fun_prop))
  have hp (z : ℝ×ℝ) : ‖shortVerticalDifference f u t z‖≤|t| *(∫ theta, ‖G (theta,z)‖ ∂nu) :=
    shortVerticalDifference_norm f u hub t z
  have hdom := hGi.norm.integral_prod_right.const_mul |t|
  have hDi := hdom.mono' hDm.aestronglyMeasurable (Filter.Eventually.of_forall hp)
  refine ⟨hDi,?_⟩
  have htotal : (∫ theta, ∫ z, ‖G (theta,z)‖ ∂planeMeasure ∂nu)≤
      4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure := by
    have h := integral_mono_ae hGi.norm.integral_prod_left
      (integrable_const (4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure))
      (htheta.mono fun theta hth => (hslice theta hth).2)
    simpa only [integral_const,nu,measureReal_def,Measure.restrict_apply_univ,
      Real.volume_Ioc,sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul] using h
  calc
    _ ≤ ∫ z, |t| *(∫ theta, ‖G (theta,z)‖ ∂nu) ∂planeMeasure := integral_mono hDi.norm hdom hp
    _ = |t| *(∫ theta, ∫ z, ‖G (theta,z)‖ ∂planeMeasure ∂nu) := by
      rw [integral_const_mul]
      exact congrArg (fun b : ℝ => |t| *b)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (theta : ℝ) => ‖G (theta,z)‖) hGi.norm.swap)
    _ ≤ |t| *(4*∫ z, ‖verticalSchwartzDeriv f z‖ ∂planeMeasure) :=
      mul_le_mul_of_nonneg_left htotal (abs_nonneg _)
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
