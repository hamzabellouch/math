import OAI.Analysis.KadisonKastler.GraphReciprocal

namespace OAI

/-! # Uniform comparison of the two rescaled graph projections

Directional bounds proved at scales at least one extend to every
positive scale by the reciprocal graph symmetry. The two directions
then bound the norm of the difference of orthogonal projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The norm of a directional projection product bounds all defining
graph vectors in that direction. -/
theorem graph_directional_vector_le_of_norm
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c B : ℝ)
    (hbound : ‖(1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c‖ ≤ B)
    (x : Algebra M) :
    ‖(1 - rescaledGraphProjection N J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
      B * ‖rescaledGraphVector J Ω c x.val‖ := by
  have he : ((1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c)
      (rescaledGraphVector J Ω c x.val) =
      (1 - rescaledGraphProjection N J Ω c) (rescaledGraphVector J Ω c x.val) := by
    rw [mul_apply_eq_comp, rescaledGraphProjection_vector M J Ω c x]
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))

/-- A large-scale directional bound controls every positive scale. -/
theorem graph_directional_all_positive
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) (B : ℝ)
    (hlarge : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c‖ ≤ B)
    {c : ℝ} (hc : 0 < c) (x : Algebra M) :
    ‖(1 - rescaledGraphProjection N J Ω c) (rescaledGraphVector J Ω c x.val)‖ ≤
      B * ‖rescaledGraphVector J Ω c x.val‖ := by
  by_cases hc1 : 1 ≤ c
  · exact graph_directional_vector_le_of_norm M N J Ω c B (hlarge c hc1) x
  · have hi : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr (le_of_not_ge hc1)
    exact graph_directional_reciprocal M N J hJ Ω hc
      (graph_directional_vector_le_of_norm M N J Ω c⁻¹ B (hlarge c⁻¹ hi)) x

/-- Two large-scale directional estimates give a uniform norm estimate
for the actual closed graph projections at every positive scale. -/
theorem uniform_rescaledGraphProjection_comparison
    (M N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (Ω : H) {B : ℝ} (hB : 0 ≤ B)
    (hMN : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection N J Ω c) * rescaledGraphProjection M J Ω c‖ ≤ B)
    (hNM : ∀ c : ℝ, 1 ≤ c →
      ‖(1 - rescaledGraphProjection M J Ω c) * rescaledGraphProjection N J Ω c‖ ≤ B)
    {c : ℝ} (hc : 0 < c) :
    ‖rescaledGraphProjection M J Ω c - rescaledGraphProjection N J Ω c‖ ≤ 2 * B :=
  norm_rescaledGraphProjection_sub_le M N J Ω c hB
    (graph_directional_all_positive M N J hJ Ω B hMN hc)
    (graph_directional_all_positive N M J hJ Ω B hNM hc)

end

end KadisonKastler

end OAI
