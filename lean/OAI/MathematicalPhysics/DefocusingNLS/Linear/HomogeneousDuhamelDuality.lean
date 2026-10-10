import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMeasurableDuhamel
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeDuality

namespace OAI

/-! # Schwartz testing commutes with the measurable whole-space Duhamel integral -/

open Set MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousDuhamel_fourier_duality (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ht : 0 ≤ t)
    (φ : 𝓢(E, ℂ)) (r : ℝ → HomogeneousY a k)
    (hr : StronglyMeasurable r) (hir : IntegrableOn r (Icc 0 t)) :
    homogeneousFourierPairing a k ha ha1 hk φ (homogeneousDuhamel a b k ha ha1 hk t r) =
      ∫ s in Icc 0 t, homogeneousFourierPairing a k ha ha1 hk
        (homogeneousFreeDualTest a b (t - s) φ) (r s) := by
  rw [homogeneousDuhamel, intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
  rw [← (homogeneousFourierPairing a k ha ha1 hk φ).integral_comp_comm
    (integrableOn_homogeneousDuhamelIntegrand a b k t ha ha1 hk r hr hir)]
  simp only [homogeneousFreeOperator_fourier_duality]

end DefocusingNLS

end OAI
