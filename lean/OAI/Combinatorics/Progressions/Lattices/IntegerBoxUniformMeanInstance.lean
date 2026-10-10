import OAI.Combinatorics.Progressions.Geometry.BoxPairDivisibility

namespace OAI

section

namespace Erdos3
open scoped Classical

theorem integerBoxUniformWeights_mean_decidableEq {J : Type*} [Fintype J]
    (dec₁ dec₂ : DecidableEq J) (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (f : (∀ j, Finset.Ico (lo j) (hi j)) → ℝ) :
    (letI := dec₁; (integerBoxUniformWeights lo hi hlen).mean f) =
      (letI := dec₂; (integerBoxUniformWeights lo hi hlen).mean f) := by
  cases Subsingleton.elim dec₁ dec₂
  rfl

end Erdos3

end

end OAI
