import OAI.Analysis.PureInfiniteness.NonunitalSampledRow
import OAI.Analysis.PureInfiniteness.SpectralCopies

namespace OAI

/-! Repeating spectral cells changes only the finite overlap constant, not
its independence from the mesh. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {D M J : Type*} [NonUnitalCStarAlgebra D] [Fintype M] [Fintype J]

lemma repeated_sampledQuadratic_norm_le (a : D) (f : J → D) (t : J → ℝ)
    (K : ℝ) (hK : ‖∑ j, sampledQuadraticError a (f j) (t j)‖ ≤ K) :
    ‖∑ p : M × J, sampledQuadraticError a (f p.2) (t p.2)‖ ≤ (Fintype.card M : ℝ) * K := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  exact norm_nsmul_le.trans
    (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _))

end WeakPureInfiniteness

end

end OAI
