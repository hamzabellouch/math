import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalC2
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreePhysical

namespace OAI

/-! # The actual free flow as one physical Fourier kernel

This formula isolates all time dependence in a smooth scalar kernel. The
second Fourier moment supplies an integrable bound for its derivative.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousPhysicalFreeKernel (a b t : ℝ) (y ξ : E) : ℂ :=
  homogeneousPhysicalAmplitude a b t * Complex.exp
    (((-(1 - Real.exp (-t)) * ‖ξ‖ ^ 2 + Real.exp (-t / 2) * ⟪ξ, y⟫ : ℝ) : ℂ) * Complex.I)

theorem homogeneousFreeOperator_physical_integral (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousFreeOperator a b k t ha ha1 hk u) y =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) *
        ∫ ξ : E, homogeneousPhysicalFreeKernel a b t y ξ * u ξ := by
  rw [homogeneousFreeOperator_physical, homogeneousSchrodingerOperator_physical,
    inverseRadianFourier]
  unfold radianFourierIntegral
  have he : (∫ ξ : E,
      Complex.exp (((-⟪ξ, -(Real.exp (-t / 2) • y)⟫ : ℝ) : ℂ) * Complex.I) *
        (homogeneousSchrodingerPhase (1 - Real.exp (-t)) ξ * u ξ)) =
      ∫ ξ : E, Complex.exp
        (((-(1 - Real.exp (-t)) * ‖ξ‖ ^ 2 + Real.exp (-t / 2) * ⟪ξ, y⟫ : ℝ) : ℂ) * Complex.I) * u ξ := by
    apply integral_congr_ae
    filter_upwards [] with ξ
    have hi : -⟪ξ, -(Real.exp (-t / 2) • y)⟫ = Real.exp (-t / 2) * ⟪ξ, y⟫ := by
      simp only [inner_neg_right, inner_smul_right, neg_neg]
    rw [hi, homogeneousSchrodingerPhase]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he]
  unfold homogeneousPhysicalFreeKernel
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

end DefocusingNLS

end OAI
