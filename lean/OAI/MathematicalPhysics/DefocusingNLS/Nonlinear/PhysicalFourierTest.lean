import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzFrequencyCutoff
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalDuality

namespace OAI

/-! # A physical Schwartz test for every Fourier Schwartz test -/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def physicalFourierTest (φ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  radianInverseKernel
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) φ)

@[simp] theorem physicalFourierTest_kernel (φ : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (physicalFourierTest φ) (-ξ) = φ ξ := by
  rw [physicalFourierTest, radianFourierKernel_inverseKernel]
  change φ (- -ξ) = φ ξ
  rw [neg_neg]

theorem homogeneousFourierPairing_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (φ : 𝓢(E, ℂ)) (v : HomogeneousY a k) :
    (∫ y : E, physicalFourierTest φ y * homogeneousPhysicalCLM a k ha ha1 hk v y) =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) * homogeneousFourierPairing a k ha ha1 hk φ v := by
  change (∫ y : E, physicalFourierTest φ y * inverseRadianFourier v y) = _
  rw [integral_inverseRadianFourier_test v
    (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp v)).1]
  simp only [physicalFourierTest_kernel, homogeneousFourierPairing_apply]

end DefocusingNLS

end OAI
