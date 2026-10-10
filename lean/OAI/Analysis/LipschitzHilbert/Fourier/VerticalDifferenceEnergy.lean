import OAI.Analysis.LipschitzHilbert.Fourier.VerticalSamplingDifference

namespace OAI

/-! The actual L2 error when a vertical translation passes through a short
variable-direction sampling map. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalSamplingDifference_energy (f : SchwartzMap (ℝ×ℝ) ℂ)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (t s : ℝ) (ht : |t|≤1/4) :
    MemLp (verticalSamplingDifference f u t s) 2 planeMeasure ∧
      (∫ z, ‖verticalSamplingDifference f u t s z‖^2 ∂planeMeasure)≤
        16*t^2*s^2*(∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure) := by
  let mu : Measure ℝ := volume.restrict (Ioc 0 1)
  let H := fun p : ℝ×(ℝ×ℝ) =>
    ‖verticalSchwartzDeriv f (verticalSampling (verticalBlend u s p.1) t t s p.2)‖^2
  let E := ∫ z, ‖verticalSchwartzDeriv f z‖^2 ∂planeMeasure
  have hum := hu.continuous.measurable
  have hdfm := (verticalSchwartzDeriv f).continuous.measurable
  have hHm : Measurable H := by
    dsimp [H,verticalSampling,verticalBlend,verticalTranslation]
    fun_prop
  have hH0 (p) : 0≤H p := sq_nonneg _
  have hs (theta : ℝ) (htheta : theta∈Ioc (0:ℝ) 1) :
      Integrable (fun z => H (theta,z)) planeMeasure ∧
        (∫ z, H (theta,z) ∂planeMeasure)≤4*E := by
    have h := verticalSampling_energy (verticalBlend u s theta)
      (verticalBlend_lipschitz u hu s theta htheta.1.le htheta.2) t t s ht
      (verticalSchwartzDeriv f) hdfm ((verticalSchwartzDeriv f).memLp 2 planeMeasure)
    exact ⟨h.1.integrable_norm_pow (by decide : 2≠0),h.2⟩
  have hIoc : ∀ᵐ theta ∂mu, theta∈Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hi : Integrable H (mu.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    refine ⟨hIoc.mono (fun theta htheta => (hs theta htheta).1),?_⟩
    apply (integrable_const (4*E)).mono' hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hIoc] with theta htheta
    have heq : (∫ z, ‖H (theta,z)‖ ∂planeMeasure)=∫ z, H (theta,z) ∂planeMeasure := by
      simp only [Real.norm_of_nonneg (hH0 _)]
    rw [heq,Real.norm_of_nonneg (integral_nonneg (fun z => hH0 (theta,z)))]
    exact (hs theta htheta).2
  have hDm : Measurable (verticalSamplingDifference f u t s) := by
    change Measurable (fun z : ℝ×ℝ => f (z.1-t,z.2-s-t*u (z.1,z.2-s))-
      f (z.1-t,z.2-s-t*u z))
    fun_prop
  have hp (z : ℝ×ℝ) : ‖verticalSamplingDifference f u t s z‖^2≤
      (2*|t| *|s|)^2*∫ theta, H (theta,z) ∂mu := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,H,mu] using
      verticalSamplingDifference_energy_pointwise f u hu t s z
  have hdom : Integrable (fun z => (2*|t| *|s|)^2*∫ theta, H (theta,z) ∂mu) planeMeasure :=
    hi.integral_prod_right.const_mul _
  have hDi : Integrable (fun z => ‖verticalSamplingDifference f u t s z‖^2) planeMeasure :=
    hdom.mono' (hDm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hp z))
  refine ⟨(memLp_two_iff_integrable_sq_norm hDm.aestronglyMeasurable).2 hDi,?_⟩
  have htotal : (∫ theta, ∫ z, H (theta,z) ∂planeMeasure ∂mu)≤4*E := by
    have hb := integral_mono_ae hi.integral_prod_left (integrable_const (4*E))
      (hIoc.mono (fun theta htheta => (hs theta htheta).2))
    have hmass : mu.real univ=1 := by
      dsimp [mu]
      rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioc]
      norm_num
    simpa only [integral_const,hmass,one_smul] using hb
  calc
    _ ≤ ∫ z, (2*|t| *|s|)^2*∫ theta, H (theta,z) ∂mu ∂planeMeasure :=
      integral_mono hDi hdom hp
    _ = (2*|t| *|s|)^2*(∫ theta, ∫ z, H (theta,z) ∂planeMeasure ∂mu) := by
      rw [integral_const_mul]
      exact congrArg (fun a => (2*|t| * |s|)^2*a)
        (integral_integral_swap (f:=fun (z : ℝ×ℝ) (theta : ℝ) => H (theta,z)) hi.swap)
    _ ≤ (2*|t| *|s|)^2*(4*E) := mul_le_mul_of_nonneg_left htotal (sq_nonneg _)
    _ = _ := by dsimp only [E]; simp only [mul_pow,sq_abs]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
