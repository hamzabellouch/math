import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MinMax

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff BigOperators

namespace WeakMTWTransport

lemma scaled_quadratic_bound_of_eigenvalues {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : E →ₗ[ℝ] E} (hK : K.IsSymmetric) {δ u : ℝ}
    {n : ℕ} (hn : Module.finrank ℝ E=n)
    (h : ∀ i : Fin n, δ*hK.eigenvalues hn i ≤ u) (v : E) :
    δ*inner ℝ (K v) v ≤ u*‖v‖^2 := by
  rw [eigenvalue_quadratic_expansion hK hn,eigenbasis_norm_expansion (hK.eigenvectorBasis hn),
    Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (h i)
    (sq_nonneg ((hK.eigenvectorBasis hn).repr v i))

end WeakMTWTransport
end
end
end

end OAI
