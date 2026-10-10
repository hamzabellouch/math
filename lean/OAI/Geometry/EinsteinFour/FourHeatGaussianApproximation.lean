import OAI.Geometry.EinsteinFour.FourHeatGaussian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

/-! Gaussian dilation and its actual approximate-identity limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Topology

noncomputable section

theorem fourHeatGaussian_dilate (t : ℝ) (ht : 0 < t) (z : FourSpace) :
    t ^ 2 * fourHeatGaussian t (Real.sqrt t • z) = fourHeatGaussian 1 z := by
  have hs : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have he : -(4 * t)⁻¹ * ‖Real.sqrt t • z‖ ^ 2 = -(4 : ℝ)⁻¹ * ‖z‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs]
    field_simp
  unfold fourHeatGaussian
  rw [he]
  norm_num only [mul_one]
  field_simp [Real.pi_ne_zero]

theorem fourHeatGaussian_rescaled_measurable (f : FourSpace → ℝ) (hf : Continuous f)
    (x : FourSpace) (t : ℝ) : AEStronglyMeasurable
    (fun z : FourSpace => fourHeatGaussian 1 z * f (x - Real.sqrt t • z)) volume := by
  have hs : Continuous (fun z : FourSpace => Real.sqrt t • z) :=
    (ContinuousLinearMap.lsmul ℝ ℝ (E := FourSpace) (Real.sqrt t)).continuous
  have hx : Continuous (fun z : FourSpace => x - Real.sqrt t • z) :=
    continuous_const.sub hs
  have hfx : Continuous (fun z : FourSpace => f (x - Real.sqrt t • z)) := hf.comp hx
  exact ((fourHeatGaussian_continuous 1).mul hfx).aestronglyMeasurable

theorem fourHeatGaussian_rescaled_bound (f : FourSpace → ℝ)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : FourSpace) (t : ℝ) (z : FourSpace) :
    ‖fourHeatGaussian 1 z * f (x - Real.sqrt t • z)‖ ≤ fourHeatGaussian 1 z * C := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (fourHeatGaussian_pos 1 zero_lt_one z)]
  exact mul_le_mul_of_nonneg_left (hC _) (fourHeatGaussian_pos 1 zero_lt_one z).le

theorem fourHeatGaussian_rescaled_pointwise (f : FourSpace → ℝ) (hf : Continuous f)
    (x z : FourSpace) :
    Tendsto (fun t : ℝ => fourHeatGaussian 1 z * f (x - Real.sqrt t • z))
      (𝓝 0) (𝓝 (fourHeatGaussian 1 z * f x)) := by
  have hs : Tendsto (fun t : ℝ => x - Real.sqrt t • z) (𝓝 0) (𝓝 x) := by
    simpa only [Real.sqrt_zero, zero_smul, sub_zero] using
      (tendsto_const_nhds.sub (Real.continuous_sqrt.continuousAt.tendsto.smul
        tendsto_const_nhds) : Tendsto (fun t : ℝ => x - Real.sqrt t • z)
          (𝓝 0) (𝓝 (x - Real.sqrt 0 • z)))
  exact tendsto_const_nhds.mul ((hf.tendsto x).comp hs)

theorem fourHeatGaussian_rescaled_limit (f : FourSpace → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : FourSpace) :
    Tendsto (fun t : ℝ => ∫ z : FourSpace,
      fourHeatGaussian 1 z * f (x - Real.sqrt t • z)) (𝓝 0) (𝓝 (f x)) := by
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure FourSpace)) (l := 𝓝 (0 : ℝ))
    (F := fun t z => fourHeatGaussian 1 z * f (x - Real.sqrt t • z))
    (f := fun z => fourHeatGaussian 1 z * f x)
    (fun z : FourSpace => fourHeatGaussian 1 z * C)
    (Eventually.of_forall (fourHeatGaussian_rescaled_measurable f hf x))
    (Eventually.of_forall fun t => Eventually.of_forall
      (fourHeatGaussian_rescaled_bound f C hC x t))
    ((fourHeatGaussian_integrable 1 zero_lt_one).mul_const C)
    (Eventually.of_forall (fourHeatGaussian_rescaled_pointwise f hf x))
  simpa only [integral_mul_const, fourHeatGaussian_mass 1 zero_lt_one, one_mul] using hd

theorem fourHeatGaussian_integral_dilate (t : ℝ) (ht : 0 < t)
    (f : FourSpace → ℝ) (x : FourSpace) :
    (∫ z : FourSpace, fourHeatGaussian t z * f (x - z)) =
      ∫ z : FourSpace, fourHeatGaussian 1 z * f (x - Real.sqrt t • z) := by
  have hs : (Real.sqrt t) ^ 4 = t ^ 2 := by
    calc
      (Real.sqrt t) ^ 4 = ((Real.sqrt t) ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [Real.sq_sqrt ht.le]
  have h := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure FourSpace))
    (fun z => fourHeatGaussian t z * f (x - z)) (Real.sqrt t)
      (hR := Real.sqrt_nonneg _)
  have hdim : Module.finrank ℝ FourSpace = 4 := by simp [FourSpace]
  rw [hdim, hs, smul_eq_mul] at h
  have he (z : FourSpace) : fourHeatGaussian t (Real.sqrt t • z) *
      f (x - Real.sqrt t • z) = (t ^ 2)⁻¹ *
        (fourHeatGaussian 1 z * f (x - Real.sqrt t • z)) := by
    have hk := fourHeatGaussian_dilate t ht z
    have hk' : fourHeatGaussian t (Real.sqrt t • z) = (t ^ 2)⁻¹ * fourHeatGaussian 1 z := by
      calc
        _ = (t ^ 2)⁻¹ * (t ^ 2 * fourHeatGaussian t (Real.sqrt t • z)) := by
          field_simp
        _ = _ := by rw [hk]
    rw [hk']
    ring
  simp_rw [he] at h
  rw [integral_const_mul] at h
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 ht.ne')) h.symm

theorem fourHeatGaussian_approximate_identity (f : FourSpace → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : FourSpace) :
    Tendsto (fun t : ℝ => ∫ z : FourSpace, fourHeatGaussian t z * f (x - z))
      (𝓝[Set.Ioi 0] 0) (𝓝 (f x)) := by
  apply ((fourHeatGaussian_rescaled_limit f hf C hC x).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (fourHeatGaussian_integral_dilate t ht f x).symm

end
end PositiveEinsteinFour.Geometry

end OAI
