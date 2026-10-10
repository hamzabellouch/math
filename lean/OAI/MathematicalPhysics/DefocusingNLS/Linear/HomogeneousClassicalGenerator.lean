import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalGeneratorIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalLaplacian

namespace OAI

/-! # The actual strong free generator is the classical differential operator -/

open Set MeasureTheory
open scoped RealInnerProductSpace Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private noncomputable def physicalPhase (x ξ : E) : ℂ :=
  Complex.exp (((⟪ξ, x⟫ : ℝ) : ℂ) * Complex.I)

private theorem physicalPhase_norm (x ξ : E) : ‖physicalPhase x ξ‖ = 1 := by
  simp [physicalPhase, Complex.norm_exp]

private theorem physicalPhase_continuous (x : E) : Continuous (physicalPhase x) := by
  unfold physicalPhase
  fun_prop

private theorem physicalGenerator_integrable (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (x : E) :
    Integrable (fun ξ : E => physicalPhase x ξ * u ξ) ∧
      Integrable (fun ξ : E => physicalPhase x ξ * (Complex.I * (⟪ξ, x⟫ : ℂ)) * u ξ) ∧
      Integrable (fun ξ : E => physicalPhase x ξ * (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * u ξ) := by
  have hu := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)).1
  have h₀ : Integrable (fun ξ : E => physicalPhase x ξ * u ξ) := by
    apply hu.norm.mono' ((physicalPhase_continuous x).aestronglyMeasurable.mul hu.aestronglyMeasurable)
    filter_upwards [] with ξ
    simp only [Pi.mul_apply, norm_mul, physicalPhase_norm, one_mul]
    exact le_rfl
  have h₁ : Integrable (fun ξ : E => physicalPhase x ξ * (Complex.I * (⟪ξ, x⟫ : ℂ)) * u ξ) := by
    have hm : AEStronglyMeasurable
        (fun ξ : E => physicalPhase x ξ * (Complex.I * (⟪ξ, x⟫ : ℂ)) * u ξ) volume := by
      apply AEStronglyMeasurable.mul _ hu.aestronglyMeasurable
      apply Continuous.aestronglyMeasurable
      unfold physicalPhase
      fun_prop
    apply ((integrable_homogeneousFourier_moment_le_two a k ha ha1 hk u 1 (by norm_num)).const_mul ‖x‖).mono' hm
    filter_upwards [] with ξ
    simp only [norm_mul, physicalPhase_norm, Complex.norm_I, Complex.norm_real, one_mul, pow_one]
    calc
      |⟪ξ, x⟫| * ‖u ξ‖ ≤ (‖ξ‖ * ‖x‖) * ‖u ξ‖ :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm ξ x) (norm_nonneg _)
      _ = _ := by ring
  have h₂ : Integrable (fun ξ : E => physicalPhase x ξ * (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * u ξ) := by
    have hm : AEStronglyMeasurable
        (fun ξ : E => physicalPhase x ξ * (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * u ξ) volume := by
      apply AEStronglyMeasurable.mul _ hu.aestronglyMeasurable
      apply Continuous.aestronglyMeasurable
      unfold physicalPhase
      fun_prop
    apply (integrable_homogeneousFourier_secondMoment a k ha ha1 hk u).mono' hm
    filter_upwards [] with ξ
    simpa only [norm_mul, physicalPhase_norm, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ‖), one_mul] using
      (le_refl (‖ξ‖ ^ 2 * ‖u ξ‖))
  exact ⟨h₀, h₁, h₂⟩

theorem homogeneousFree_generator_classical (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u v : HomogeneousY a k)
    (hu : HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk u)
      v (Ici 0) 0) (x : E) :
    homogeneousPhysicalCLM a k ha ha1 hk v x =
      Complex.I * Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x -
        (1 / 2 : ℂ) * fderiv ℝ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x x +
        (-(a : ℂ) + Complex.I * (b : ℂ)) * homogeneousPhysicalCLM a k ha ha1 hk u x := by
  let P := physicalPhase x
  let F₀ : E → ℂ := fun ξ => P ξ * u ξ
  let F₁ : E → ℂ := fun ξ => P ξ * (Complex.I * (⟪ξ, x⟫ : ℂ)) * u ξ
  let F₂ : E → ℂ := fun ξ => P ξ * (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * u ξ
  let c : ℂ := -(a : ℂ) + Complex.I * (b : ℂ)
  let N : ℂ := (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ)
  obtain ⟨h₀, h₁, h₂⟩ := physicalGenerator_integrable a k ha ha1 hk u x
  change Integrable F₀ at h₀
  change Integrable F₁ at h₁
  change Integrable F₂ at h₂
  have hval : homogeneousPhysicalCLM a k ha ha1 hk u x = N * ∫ ξ, F₀ ξ := by
    change inverseRadianFourier (u : E → ℂ) x = _
    simp only [inverseRadianFourier, radianFourierIntegral, inner_neg_right, neg_neg]
    rfl
  have hgrad : fderiv ℝ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x x =
      N * ∫ ξ, F₁ ξ := by
    simpa only [N, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_ofNat, F₁, P, physicalPhase] using
      fderiv_homogeneousPhysical a k ha ha1 hk u x x
  have hlap : Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x =
      N * ∫ ξ, F₂ ξ := by
    simpa only [N, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_ofNat, F₂, P, physicalPhase] using
      laplacian_homogeneousPhysical a k ha ha1 hk u x
  have hD : (fun ξ : E => homogeneousPhysicalFreeKernelDerivative a b 0 x ξ * u ξ) =
      (fun ξ : E => c * F₀ ξ + Complex.I * F₂ ξ - (1 / 2 : ℂ) * F₁ ξ) := by
    funext ξ
    simp only [homogeneousPhysicalFreeKernelDerivative, homogeneousPhysicalFreeKernel,
      homogeneousPhysicalAmplitude_eq, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      neg_zero, zero_div, Real.exp_zero, sub_self, zero_mul, zero_add, one_mul, one_div,
      F₀, F₁, F₂, P, physicalPhase, c]
    push_cast
    ring
  have hadd : (∫ ξ, c * F₀ ξ + Complex.I * F₂ ξ) =
      (∫ ξ, c * F₀ ξ) + ∫ ξ, Complex.I * F₂ ξ := by
    simpa only [Pi.add_apply] using integral_add (h₀.const_mul c) (h₂.const_mul Complex.I)
  have hsub : (∫ ξ, c * F₀ ξ + Complex.I * F₂ ξ - (1 / 2 : ℂ) * F₁ ξ) =
      (∫ ξ, c * F₀ ξ + Complex.I * F₂ ξ) - ∫ ξ, (1 / 2 : ℂ) * F₁ ξ := by
    simpa only [Pi.add_apply] using
      integral_sub ((h₀.const_mul c).add (h₂.const_mul Complex.I)) (h₁.const_mul (1 / 2 : ℂ))
  rw [homogeneousFree_generator_physical_integral a b k ha ha1 hk u v hu x, hD,
    hsub, hadd, integral_const_mul, integral_const_mul, integral_const_mul, hval, hgrad, hlap]
  dsimp only [N, c]
  push_cast
  ring

end DefocusingNLS

end OAI
