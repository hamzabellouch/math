import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalInjective
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalLaplacian

namespace OAI

/-! # The Fourier representative of a classical Laplacian in Y -/

open MeasureTheory
open scoped Laplacian RealInnerProductSpace

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_laplacian_frequency (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (q qL : HomogeneousY a k)
    (hL : ∀ x, homogeneousPhysicalCLM a k ha ha1 hk qL x =
      Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) x) :
    (qL : E → ℂ) =ᵐ[volume] (fun ξ => (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * q ξ) := by
  have hq := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp q)).1
  have hm : Integrable (fun ξ : E => (-(‖ξ‖ ^ 2 : ℝ) : ℂ) * q ξ) := by
    apply (integrable_homogeneousFourier_secondMoment a k ha ha1 hk q).mono'
      ((by fun_prop : Continuous (fun ξ : E => (-(‖ξ‖ ^ 2 : ℝ) : ℂ))).aestronglyMeasurable.mul
        hq.aestronglyMeasurable)
    filter_upwards [] with ξ
    change ‖(-((‖ξ‖ ^ 2 : ℝ) : ℂ)) * q ξ‖ ≤ ‖ξ‖ ^ 2 * ‖q ξ‖
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖ξ‖), le_refl]
  apply inverseRadianFourier_injective_ae
    (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp qL)).1 hm
  funext x
  change homogeneousPhysicalCLM a k ha ha1 hk qL x = _
  rw [hL, laplacian_homogeneousPhysical]
  simp only [inverseRadianFourier, radianFourierIntegral, inner_neg_right, neg_neg]
  push_cast
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

end DefocusingNLS

end OAI
