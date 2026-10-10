import OAI.Geometry.SurfaceImmersion.Geometry.TensorPerturbationOperator

namespace OAI

/-! The smallness hypotheses convert the polynomial mixed and cubic terms
to the common delta-cubed/wavelength error scale. -/
noncomputable section
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma polynomial_mixed_scale {E ε A B δ τ : ℝ} {p : ℕ}
    (hE : 0 ≤ E) (_hε : 0 ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hsmall : ε / τ ^ p ≤ 1) :
    E * ε * (A * δ * τ) * (B * δ ^ 2) / τ ^ p ≤ E * A * B * (δ ^ 3 / τ) := by
  have hτ2 : τ ^ 2 ≤ 1 := pow_le_one₀ hτ.le hτ1
  calc
    _ = (E * A * B * (δ ^ 3 / τ)) * ((ε / τ ^ p) * τ ^ 2) := by field_simp
    _ ≤ (E * A * B * (δ ^ 3 / τ)) * 1 := by gcongr; exact (mul_le_of_le_one_left (sq_nonneg τ) hsmall).trans hτ2
    _ = _ := mul_one _

lemma polynomial_self_scale {E ε B δ τ : ℝ} {p : ℕ}
    (hE : 0 ≤ E) (_hε : 0 ≤ ε) (_hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδτ : δ ≤ τ) (hsmall : ε / τ ^ p ≤ 1) :
    E * ε * (B * δ ^ 2) * (B * δ ^ 2) / τ ^ p ≤ E * B ^ 2 * (δ ^ 3 / τ) := by
  have hδ1 : δ ≤ 1 := hδτ.trans hτ1
  have hdt : δ * τ ≤ 1 := (mul_le_of_le_one_left hτ.le hδ1).trans hτ1
  calc
    _ = (E * B ^ 2 * (δ ^ 3 / τ)) * ((ε / τ ^ p) * (δ * τ)) := by field_simp
    _ ≤ (E * B ^ 2 * (δ ^ 3 / τ)) * 1 := by gcongr; exact (mul_le_of_le_one_left (mul_nonneg hδ hτ.le) hsmall).trans hdt
    _ = _ := mul_one _

lemma polynomial_cubic_scale {E ε A δ τ : ℝ} {p : ℕ}
    (hE : 0 ≤ E) (_hε : 0 ≤ ε) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hsmall : ε / τ ^ p ≤ 1) :
    E * ε * (A * δ * τ) ^ 3 / τ ^ p ≤ E * A ^ 3 * (δ ^ 3 / τ) := by
  have hτ4 : τ ^ 4 ≤ 1 := pow_le_one₀ hτ.le hτ1
  calc
    _ = (E * A ^ 3 * (δ ^ 3 / τ)) * ((ε / τ ^ p) * τ ^ 4) := by field_simp
    _ ≤ (E * A ^ 3 * (δ ^ 3 / τ)) * 1 := by gcongr; exact (mul_le_of_le_one_left (pow_nonneg hτ.le _) hsmall).trans hτ4
    _ = _ := mul_one _

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
