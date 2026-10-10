import OAI.Geometry.EinsteinFour.FourHeatGaussian

namespace OAI

/-! Actual coordinate derivatives of the Euclidean heat kernel in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators

noncomputable section

theorem fourHeatGaussian_hasFDerivAt (t : ℝ) (x : FourSpace) :
    HasFDerivAt (fourHeatGaussian t)
      (fourHeatGaussian t x • (-(4 * t)⁻¹ • (2 • innerSL ℝ x))) x := by
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul
    (-(4 * t)⁻¹)).exp).const_mul (((4 * Real.pi * t) ^ 2)⁻¹)
  unfold fourHeatGaussian
  simpa only [smul_smul, mul_assoc] using h

theorem fourHeatGaussian_partial (t : ℝ) (ht : t ≠ 0) (i : Fin 4) (x : FourSpace) :
    partialDeriv (fourHeatGaussian t) i x =
      (-x i / (2 * t)) * fourHeatGaussian t x := by
  unfold partialDeriv
  rw [(fourHeatGaussian_hasFDerivAt t x).fderiv]
  have hb : coordinateVector i = (EuclideanSpace.basisFun (Fin 4) ℝ) i := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [smul_apply, innerSL_apply_apply, hb, EuclideanSpace.inner_basisFun_real,
    smul_eq_mul]
  field_simp
  ring

theorem fourHeatGaussian_coordinate_hasFDerivAt (i : Fin 4) (x : FourSpace) :
    HasFDerivAt (fun y : FourSpace => y i)
      (innerSL ℝ ((EuclideanSpace.basisFun (Fin 4) ℝ) i)) x := by
  convert (innerSL ℝ ((EuclideanSpace.basisFun (Fin 4) ℝ) i)).hasFDerivAt (x := x) using 1
  funext y
  rw [innerSL_apply_apply, real_inner_comm, EuclideanSpace.inner_basisFun_real]

theorem fourHeatGaussian_partial_partial (t : ℝ) (ht : t ≠ 0)
    (i j : Fin 4) (x : FourSpace) :
    partialDeriv (partialDeriv (fourHeatGaussian t) i) j x =
      (x i * x j / (4 * t ^ 2) - (if i = j then 1 else 0) / (2 * t)) *
        fourHeatGaussian t x := by
  have heq : partialDeriv (fourHeatGaussian t) i =
      fun y => (-y i / (2 * t)) * fourHeatGaussian t y := by
    funext y
    exact fourHeatGaussian_partial t ht i y
  rw [heq]
  have hc := ((fourHeatGaussian_coordinate_hasFDerivAt i x).neg.mul_const ((2 * t)⁻¹))
  have hd := hc.mul (fourHeatGaussian_hasFDerivAt t x)
  simp only [← div_eq_mul_inv, Pi.neg_apply] at hd
  change HasFDerivAt (fun y : FourSpace => -y i / (2 * t) * fourHeatGaussian t y) _ x at hd
  unfold partialDeriv
  rw [hd.fderiv]
  have hb : coordinateVector j = (EuclideanSpace.basisFun (Fin 4) ℝ) j := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [add_apply, smul_apply, innerSL_apply_apply, hb, neg_apply]
  simp only [EuclideanSpace.inner_basisFun_real]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    field_simp
    ring
  · simp only [hij, Ne.symm hij, ite_false]
    field_simp
    ring

theorem fourHeatGaussian_spatial_laplacian (t : ℝ) (ht : t ≠ 0) (x : FourSpace) :
    (∑ i : Fin 4, partialDeriv (partialDeriv (fourHeatGaussian t) i) i x) =
      (‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) * fourHeatGaussian t x := by
  simp_rw [fourHeatGaussian_partial_partial t ht]
  simp only [ite_true]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  simp only [← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hn : (∑ i : Fin 4, x i * x i) = ‖x‖ ^ 2 := by
    simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq x).symm
  rw [hn]
  congr 1
  field_simp
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
