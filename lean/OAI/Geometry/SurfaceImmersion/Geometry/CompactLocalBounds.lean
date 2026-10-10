import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
