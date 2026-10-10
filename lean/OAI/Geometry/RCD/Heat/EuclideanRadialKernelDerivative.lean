import OAI.Geometry.RCD.Heat.EuclideanRadialKernel

namespace OAI

/-! # Second derivative bounds for radial averaging -/

open Set Metric MeasureTheory
open scoped ContDiff Convolution

noncomputable section
namespace RegularPointCoordinates

/-- Only one fixed compact kernel contributes to the dimensional constant;
every change of radius contributes exactly its inverse square. -/
theorem euclideanRadialKernel_second_bound (n : ℕ) :
    ∃ J : ℝ, 0 < J ∧ ∀ r : ℝ, 0 < r → ∀ x : Euclidean n,
      ‖iteratedFDeriv ℝ 2 (euclideanRadialKernel n r) x‖ ≤ J/r^2 := by
  have hcont := (euclideanRadialWeight_smooth n).continuous_iteratedFDeriv (m := 2) (by simp)
  obtain ⟨B,hB⟩ := hcont.bounded_above_of_compact_support
    ((euclideanRadialWeight_compact n).iteratedFDeriv 2)
  let J := 1+|B|
  refine ⟨J,by positivity,?_⟩
  intro r hr x
  let L : Euclidean n →L[ℝ] Euclidean n := r⁻¹ • ContinuousLinearMap.id ℝ _
  have hL : ‖L‖ ≤ r⁻¹ := by
    dsimp only [L]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le :
      ‖ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ 1) (inv_nonneg.mpr hr.le)
  have h0 : ‖iteratedFDeriv ℝ 2 (euclideanRadialWeight n) (L x)‖ ≤ J :=
    (hB _).trans ((le_abs_self B).trans (by dsimp only [J]; linarith [abs_nonneg B]))
  have he := norm_iteratedFDeriv_comp_affine_le L (euclideanRadialWeight n) 0 x 2
    ((euclideanRadialWeight_smooth n).of_le (by simp)).contDiffAt
  have hbound : ‖iteratedFDeriv ℝ 2 (euclideanRadialKernel n r) x‖ ≤
      ‖iteratedFDeriv ℝ 2 (euclideanRadialWeight n) (L x)‖*‖L‖^2 := by
    simpa only [zero_add] using! he
  calc
    _ ≤ J*(r⁻¹)^2 := hbound.trans (mul_le_mul h0
      (pow_le_pow_left₀ (norm_nonneg L) hL 2) (sq_nonneg _) (by positivity))
    _ = _ := by rw [div_eq_mul_inv,inv_pow]

/-- The Hessian of an actual convolution is bounded using the L¹ mass of
its first factor and the inverse-square kernel estimate. -/
theorem euclideanRadialConvolution_hessian_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ f : Euclidean n → ℝ, Integrable f volume → ∀ x : Euclidean n,
      ‖fderiv ℝ (fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] euclideanRadialKernel n r)) x‖ ≤
        (C/r^2)*(∫ y, |f y|) := by
  obtain ⟨J,hJ,hbound⟩ := euclideanRadialKernel_second_bound n
  let L := ContinuousLinearMap.mul ℝ ℝ
  let C := 1+‖L‖*J
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro r hr f hf x
  have hh := norm_iteratedFDeriv_convolution_le 2 L hf (euclideanRadialKernel_smooth n r)
    (euclideanRadialKernel_compact n hr) (by positivity : 0 ≤ J/r^2) (hbound r hr) x
  rw [← norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_one] at hh
  calc
    _ ≤ ‖L‖*(J/r^2)*(∫ y, ‖f y‖) := hh
    _ ≤ (C/r^2)*(∫ y, |f y|) := by
      simp only [Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun y => abs_nonneg _)
      dsimp only [C]
      rw [div_eq_mul_inv,div_eq_mul_inv]
      nlinarith [inv_nonneg.mpr (sq_nonneg r)]

end RegularPointCoordinates

end

end OAI
