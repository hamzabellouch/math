import OAI.MeasureTheory.Falconer.Angular.AngularIntegrability
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def sourceProjection (θ : ℝ) (z : Plane) : ℝ :=
  -Real.sin θ * z 0 + Real.cos θ * z 1

noncomputable def planePhase (z : Plane) : ℝ :=
  Complex.arg (Complex.orthonormalBasisOneI.repr.symm z)

@[fun_prop] theorem continuous_sourceProjection :
    Continuous (fun p : ℝ × Plane => sourceProjection p.1 p.2) := by
  unfold sourceProjection
  fun_prop

theorem sourceProjection_sub (θ : ℝ) (x y : Plane) :
    sourceProjection θ (x-y) = sourceProjection θ x - sourceProjection θ y := by
  simp only [sourceProjection,PiLp.sub_apply]
  ring

theorem abs_sourceProjection (θ : ℝ) {z : Plane} (hz : z ≠ 0) :
    |sourceProjection θ z| = ‖z‖ * |Real.sin (θ-planePhase z)| := by
  let w := Complex.orthonormalBasisOneI.repr.symm z
  have hw : w ≠ 0 := by
    intro h
    have hn := congrArg norm h
    simp only [w,LinearIsometryEquiv.norm_map,norm_zero] at hn
    exact hz (norm_eq_zero.mp hn)
  have hn : ‖w‖ = ‖z‖ := LinearIsometryEquiv.norm_map _ _
  have hre : w.re = z 0 := by simp [w,Complex.orthonormalBasisOneI_repr_symm_apply]
  have him : w.im = z 1 := by simp [w,Complex.orthonormalBasisOneI_repr_symm_apply]
  have he : sourceProjection θ z = -‖z‖ * Real.sin (θ-planePhase z) := by
    rw [Real.sin_sub]
    change -Real.sin θ*z 0+Real.cos θ*z 1 =
      -‖z‖*(Real.sin θ*Real.cos (Complex.arg w)-Real.cos θ*Real.sin (Complex.arg w))
    rw [Complex.cos_arg hw,Complex.sin_arg,hre,him,hn]
    field_simp [norm_ne_zero_iff.mpr hz]
    ring
  rw [he,abs_mul,abs_neg,abs_norm]

theorem sourceProjection_angular_kernel {v : ℝ} (hv : 0 < v) (hv1 : v < 1)
    {z : Plane} (hz : z ≠ 0) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi),
      (ENNReal.ofReal |sourceProjection θ z|)^(-v)) =
        (ENNReal.ofReal ‖z‖)^(-v) * angularEnergyConstant v := by
  have he (θ : ℝ) : (ENNReal.ofReal |sourceProjection θ z|)^(-v) =
      (ENNReal.ofReal ‖z‖)^(-v) * sineKernel v (θ-planePhase z) := by
    rw [abs_sourceProjection θ hz,ENNReal.ofReal_mul (norm_nonneg _),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    rfl
  simp_rw [he]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hz)).ne' ENNReal.ofReal_ne_top),
    sineKernel_shift_integral hv hv1]

theorem sourceProjection_kernel_factor {t : ℝ} (ht : 0 < t) (θ : ℝ) (z : Plane) :
    (ENNReal.ofReal |sourceProjection θ z|)^(-t) =
      (ENNReal.ofReal ‖z‖)^(-t) * sineKernel t (θ-planePhase z) := by
  by_cases hz : z = 0
  · subst z
    simp only [sourceProjection,PiLp.zero_apply,mul_zero,add_zero,abs_zero,norm_zero,
      ENNReal.ofReal_zero,ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr ht)]
    exact (ENNReal.top_mul (ne_of_gt (zero_lt_one.trans_le
      (one_le_sineKernel ht.le _)))).symm
  · rw [abs_sourceProjection θ hz,ENNReal.ofReal_mul (norm_nonneg _),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    rfl

noncomputable def projectedMeasure (μ : Measure Plane) (θ : ℝ) : Measure ℝ :=
  μ.map (sourceProjection θ)

instance projectedMeasure_finite (μ : Measure Plane) [IsFiniteMeasure μ] (θ : ℝ) :
    IsFiniteMeasure (projectedMeasure μ θ) := by unfold projectedMeasure; infer_instance

theorem projected_energy_formula (μ : Measure Plane) [IsFiniteMeasure μ] (t θ : ℝ) :
    rieszEnergyOn (projectedMeasure μ θ) t =
      ∫⁻ z : Plane × Plane, (ENNReal.ofReal |sourceProjection θ (z.1-z.2)|)^(-t) ∂μ.prod μ := by
  have hm : Measurable (sourceProjection θ) := by unfold sourceProjection; fun_prop
  rw [rieszEnergyOn,projectedMeasure,Measure.map_prod_map μ μ hm hm,
    lintegral_map (by fun_prop) (hm.prodMap hm)]
  apply lintegral_congr
  intro z
  simp only [Prod.map,edist_dist,Real.dist_eq,sourceProjection_sub]

noncomputable def differenceEnergyMeasure (μ : Measure Plane) (t : ℝ) : Measure (Plane × Plane) :=
  (μ.prod μ).withDensity (fun z => (edist z.1 z.2)^(-t))

theorem differenceEnergyMeasure_mass (μ : Measure Plane) (t : ℝ) :
    differenceEnergyMeasure μ t univ = rieszEnergyOn μ t := by
  rw [differenceEnergyMeasure,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
  rfl

theorem projected_energy_weighted_formula (μ : Measure Plane) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    rieszEnergyOn (projectedMeasure μ θ) t =
      ∫⁻ z : Plane × Plane, sineKernel t (θ-planePhase (z.1-z.2))
        ∂differenceEnergyMeasure μ t := by
  rw [projected_energy_formula,differenceEnergyMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (by unfold sineKernel planePhase; fun_prop)]
  apply lintegral_congr
  intro z
  simp only [Pi.mul_apply]
  rw [sourceProjection_kernel_factor ht,edist_dist,dist_eq_norm]

end PlanarFalconer

end OAI
