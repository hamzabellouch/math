import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalC2
import Mathlib.Analysis.InnerProductSpace.Laplacian

namespace OAI

/-! # Cartesian jets of the actual physical representative

Up to order two, derivatives are ordinary inverse Fourier integrals. The
restriction n ≤ 2 is exactly what k > 8 supplies in dimension twelve.
-/

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem physical_fourier_phase (ξ x : E) :
    -2 * Real.pi * ⟪ξ, (-(2 * Real.pi)⁻¹ : ℝ) • x⟫ = ⟪ξ, x⟫ := by
  rw [real_inner_smul_right]
  field_simp

private theorem physical_fourier_scalar :
    (((-(2 * Real.pi)⁻¹ : ℝ) : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I))) = Complex.I := by
  push_cast
  field_simp

theorem iteratedFDeriv_homogeneousPhysical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k)
    (n : ℕ) (hn : n ≤ 2) (x : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun z : E => homogeneousPhysicalCLM a k ha ha1 hk u z) x v =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) *
        ∫ ξ : E, Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) *
          (Complex.I ^ n * ((∏ j : Fin n, ⟪ξ, v j⟫ : ℝ) : ℂ)) * u ξ := by
  have hm (j : ℕ) (hj : j ≤ (2 : ℕ∞)) :
      Integrable (fun ξ : E => ‖ξ‖ ^ j * ‖u ξ‖) :=
    integrable_homogeneousFourier_moment_le_two a k ha ha1 hk u j (by exact_mod_cast hj)
  have hu := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)).1
  have hF2 : ContDiff ℝ 2 (𝓕 (u : E → ℂ)) := Real.contDiff_fourier hm
  have hFn : ContDiff ℝ n (𝓕 (u : E → ℂ)) := hF2.of_le (by exact_mod_cast hn)
  let r : ℝ := -(2 * Real.pi)⁻¹
  let c : ℂ := (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ)
  have hc : (fun z : E => homogeneousPhysicalCLM a k ha ha1 hk u z) =
      c • (fun z : E => 𝓕 (u : E → ℂ) (r • z)) := by
    funext z
    change inverseRadianFourier (u : E → ℂ) z = c * 𝓕 (u : E → ℂ) (r • z)
    rw [inverseRadianFourier, radianFourierIntegral_eq_fourier]
    simp only [c, r, neg_smul, smul_neg]
  have hcomp : ContDiff ℝ n (fun z : E => 𝓕 (u : E → ℂ) (r • z)) :=
    hFn.comp (contDiff_const.fun_smul contDiff_id)
  rw [hc, iteratedFDeriv_const_smul_apply hcomp.contDiffAt]
  rw [congrFun (iteratedFDeriv_comp_const_smul r hFn) x]
  rw [Real.iteratedFDeriv_fourier hm hu.aestronglyMeasurable (by exact_mod_cast hn)]
  simp only [smul_apply]
  rw [Real.fourier_continuousMultilinearMap_apply
    (VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (hm n (by exact_mod_cast hn))
      hu.aestronglyMeasurable)]
  rw [Real.fourier_eq']
  simp only [Complex.real_smul, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [VectorFourier.fourierPowSMulRight_apply,
    Complex.real_smul, smul_eq_mul, r, Complex.ofReal_pow]
  rw [physical_fourier_phase]
  have hpow : (((-(2 * Real.pi)⁻¹ : ℝ) : ℂ) ^ n *
      (-(2 * (Real.pi : ℂ) * Complex.I)) ^ n) = Complex.I ^ n := by
    rw [← mul_pow, physical_fourier_scalar]
  dsimp only [c]
  push_cast
  push_cast at hpow
  have hi : (∏ j : Fin n, (((innerSL ℝ) ξ (v j) : ℝ) : ℂ)) =
      ∏ j : Fin n, ((⟪ξ, v j⟫ : ℝ) : ℂ) := rfl
  rw [hi]
  calc
    _ = (((2 * (Real.pi : ℂ)) ^ (12 : ℕ))⁻¹) *
        Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I) *
        (((-(2 * (Real.pi : ℂ))⁻¹) ^ n * (-(2 * (Real.pi : ℂ) * Complex.I)) ^ n) *
          ∏ j : Fin n, ((⟪ξ, v j⟫ : ℝ) : ℂ)) * u ξ := by ring
    _ = _ := by rw [hpow]; ring

end DefocusingNLS

end OAI
