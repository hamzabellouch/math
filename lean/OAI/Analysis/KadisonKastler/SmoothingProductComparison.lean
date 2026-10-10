import OAI.Analysis.KadisonKastler.PoissonBoundaryLimit

namespace OAI

/-! # Products of smoothing comparisons -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem norm_unitary_product_sub_le (u v : unitary A) (a b : A) {d B : ℝ}
    (hB : 0 ≤ B) (hu : ‖(u : A) - a‖ ≤ d)
    (hv : ‖(v : A) - b‖ ≤ d) (ha : ‖a‖ ≤ B) :
    ‖(u : A) * star (v : A) - a * star b‖ ≤ (1 + B) * d := by
  have he : (u : A) * star (v : A) - a * star b =
      ((u : A) - a) * star (v : A) + a * star ((v : A) - b) := by
    rw [star_sub, sub_mul, mul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖((u : A) - a) * star (v : A)‖ + ‖a * star ((v : A) - b)‖ := norm_add_le _ _
    _ = ‖(u : A) - a‖ + ‖a * star ((v : A) - b)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ d + B * d := add_le_add hu
      ((norm_mul_le _ _).trans (mul_le_mul ha (by simpa only [norm_star] using hv)
        (norm_nonneg _) hB))
    _ = _ := by ring

end

end KadisonKastler

end OAI
