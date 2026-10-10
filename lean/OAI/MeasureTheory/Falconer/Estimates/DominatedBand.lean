import OAI.MeasureTheory.Falconer.Fourier.DistanceBandKernelBound
import OAI.MeasureTheory.Falconer.Geometry.BinEstimates

namespace OAI

/-! # A positive dominated-measure bound on a real frequency band

Scalar real-line binning and sinc estimates control the frequency band.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem dominated_real_frequency_band (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c)
    (hdom : μ ≤ ENNReal.ofReal c • ν) :
    ∫ r in Icc (-A) A, ‖charFun μ r‖^2 ≤
      32*A*c^2*PlanarFalconer.binKernelConstant.toReal *
        (ν.prod ν).real {z : ℝ × ℝ | |z.1-z.2| ≤ 1/A} := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (1/(1+A*|z.1-z.2|)^2)
  have hp := Measure.prod_mono hdom hdom
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul] at hp
  have hk := lintegral_mono' hp (fun z => le_refl (F z))
  rw [lintegral_smul_measure] at hk
  simp only [smul_eq_mul] at hk
  have hb := PlanarFalconer.real_bin_decaying_self_kernel_bound ν (one_div_pos.mpr hA)
  have he : (fun z : ℝ × ℝ => ENNReal.ofReal (1/(1+|z.1-z.2|/(1/A))^2)) = F := by
    funext z
    simp only [F,div_eq_mul_inv,one_mul,mul_one,inv_inv,mul_comm]
  rw [he] at hb
  have hk' := hk.trans (mul_le_mul_right hb (ENNReal.ofReal c*ENNReal.ofReal c))
  have hh := (PlanarFalconer.distance_band_kernel_bound_ennreal μ hA).trans
    (mul_le_mul_right hk' (ENNReal.ofReal (32*A)))
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top PlanarFalconer.binKernelConstant_ne_top (measure_ne_top (ν.prod ν) _)))) hh
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun r => sq_nonneg ‖charFun μ r‖))] at hr
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,
    ENNReal.toReal_ofReal (show 0 ≤ 32*A by positivity),measureReal_def,pow_two,mul_assoc] using hr

end Falconer

end OAI
