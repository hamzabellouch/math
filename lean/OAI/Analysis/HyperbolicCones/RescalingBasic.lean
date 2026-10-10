import OAI.Analysis.HyperbolicCones.MatrixLinear

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem linear_coefficient_zero_of_quadratic_nonneg (a b : ℝ)
    (h : ∀ s : ℝ, 0 ≤ a * s ^ 2 + b * s) : b = 0 := by
  have ha : 0 ≤ a := by nlinarith [h 1, h (-1)]
  rcases eq_or_lt_of_le ha with hzero | hpos
  · have ht := h (-b)
    rw [← hzero] at ht
    nlinarith [sq_nonneg b]
  · have ht := h (-b / (2 * a))
    have heq : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) =
        -b ^ 2 / (4 * a) := by
      field_simp
      ring
    rw [heq] at ht
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * a)).mp ht
    nlinarith [sq_nonneg b]

theorem linear_term_zero_of_quadratic_posSemidef {n : ℕ} (E G : Sym n)
    (h : ∀ s : ℝ, (s ^ 2 • (E : Mat n ℝ) + s • (G : Mat n ℝ)).PosSemidef) :
    G = 0 := by
  have hq (v : Fin n → ℝ) : v ⬝ᵥ ((G : Mat n ℝ) *ᵥ v) = 0 := by
    apply linear_coefficient_zero_of_quadratic_nonneg (v ⬝ᵥ ((E : Mat n ℝ) *ᵥ v))
    intro s
    have hs := (h s).dotProduct_mulVec_nonneg v
    simpa only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul, mul_comm] using hs
  have hg : (G : Mat n ℝ).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg G.property
    intro v
    simpa only [star_trivial, hq] using (le_refl (0 : ℝ))
  have hneg : (-(G : Mat n ℝ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg G.property.neg
    intro v
    simpa only [star_trivial, neg_mulVec, dotProduct_neg, hq, neg_zero]
      using (le_refl (0 : ℝ))
  apply Subtype.ext
  exact le_antisymm (neg_nonneg.mp hneg.nonneg) hg.nonneg

end Paper256

end

end OAI
