import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFourierJets

namespace OAI

/-! # The classical gradient and Laplacian of the actual Y realization -/

open MeasureTheory
open scoped RealInnerProductSpace Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem fderiv_homogeneousPhysical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (x v : E) :
    fderiv ℝ (fun z : E => homogeneousPhysicalCLM a k ha ha1 hk u z) x v =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) *
        ∫ ξ : E, Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) *
          (Complex.I * (⟪ξ, v⟫ : ℂ)) * u ξ := by
  simpa only [iteratedFDeriv_one_apply, Fin.prod_univ_one, pow_one] using
    iteratedFDeriv_homogeneousPhysical a k ha ha1 hk u 1 (by norm_num) x (fun _ => v)

private theorem integrable_physicalSquare (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k)
    (x : E) (j : Fin 12) :
    Integrable (fun ξ : E => Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) *
      (-((⟪ξ, EuclideanSpace.basisFun (Fin 12) ℝ j⟫ : ℝ) : ℂ) ^ 2) * u ξ) := by
  have hu := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)).1
  have hm : AEStronglyMeasurable (fun ξ : E =>
      Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) *
        (-((⟪ξ, EuclideanSpace.basisFun (Fin 12) ℝ j⟫ : ℝ) : ℂ) ^ 2) * u ξ) volume := by
    apply AEStronglyMeasurable.mul _ hu.aestronglyMeasurable
    apply Continuous.aestronglyMeasurable
    fun_prop
  apply (integrable_homogeneousFourier_secondMoment a k ha ha1 hk u).mono' hm
  filter_upwards [] with ξ
  have hi : |⟪ξ, EuclideanSpace.basisFun (Fin 12) ℝ j⟫| ≤ ‖ξ‖ := by
    simpa only [(EuclideanSpace.basisFun (Fin 12) ℝ).norm_eq_one, mul_one] using
      abs_real_inner_le_norm ξ (EuclideanSpace.basisFun (Fin 12) ℝ j)
  have hs : |⟪ξ, EuclideanSpace.basisFun (Fin 12) ℝ j⟫| ^ 2 ≤ ‖ξ‖ ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hi
  simp only [norm_mul, norm_neg, norm_pow, Complex.norm_real, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul]
  exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)

theorem laplacian_homogeneousPhysical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (x : E) :
    Δ (fun z : E => homogeneousPhysicalCLM a k ha ha1 hk u z) x =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) *
        ∫ ξ : E, Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) *
          (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * u ξ := by
  let e := EuclideanSpace.basisFun (Fin 12) ℝ
  have hj (j : Fin 12) :
      iteratedFDeriv ℝ 2 (fun z : E => homogeneousPhysicalCLM a k ha ha1 hk u z)
        x ![e j, e j] =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) *
        ∫ ξ : E, Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) *
          (-((⟪ξ, e j⟫ : ℝ) : ℂ) ^ 2) * u ξ := by
    simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.I_sq, neg_one_mul, Complex.ofReal_mul, ← pow_two, Complex.ofReal_pow] using
      iteratedFDeriv_homogeneousPhysical a k ha ha1 hk u 2 (by norm_num) x ![e j, e j]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e]
  simp_rw [hj]
  rw [← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum _ (fun j _ => integrable_physicalSquare a k ha ha1 hk u x j)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hs : ∑ j : Fin 12, (⟪ξ, e j⟫ : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using e.sum_sq_norm_inner_left ξ
  have hc : ∑ j : Fin 12, ((⟪ξ, e j⟫ : ℝ) : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast hs
  calc
    _ = Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) *
        (-(∑ j : Fin 12, ((⟪ξ, e j⟫ : ℝ) : ℂ) ^ 2)) * u ξ := by
      rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [hc]

end DefocusingNLS

end OAI
