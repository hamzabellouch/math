import OAI.Analysis.MetricEntropy.Basic
import OAI.Analysis.MetricEntropy.Parameters

namespace OAI

universe uι

/-!
# The output of the concrete counterexample construction

Every field below concerns the actual finite-dimensional body, its literal
cube and polar, or their covering numbers. The construction theorem supplies
this record from only the numerical inputs `a`, `r`, and `B`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

/-- The actual quotient of dual covering entropy by primal covering entropy. -/
def entropyRatio {ι : Type uι} [Fintype ι] (a : ℝ)
    (K : Set (RealSpace ι)) : ℝ :=
  Real.log (coveringNumber (polar (cube ι)) (a⁻¹ • polar K) : ℝ) /
    Real.log (coveringNumber K (cube ι) : ℝ)

/-- The scalar upper bound, with radius and pivot count fixed by `a` alone. -/
def entropyBudget (a : ℝ) (r : ℕ) (B : ℝ) : ℝ :=
  2 * (compressionRadius a : ℝ) ^ 2 * (pivotSlots (accuracy a) : ℝ) /
    ((r : ℝ) + (compressionRadius a : ℝ) - 1) + 2 / B

/-- A constructed body with its actual geometric and entropy properties.
No matrix, compression theorem, or abstract entropy function is a field. -/
structure EntropyPair (a : ℝ) (r : ℕ) (B : ℝ) where
  dimension : ℕ
  dimension_pos : 0 < dimension
  rank_le_dimension : r ≤ dimension
  body : Set (RealSpace (Fin dimension))
  body_isSymmetricConvexBody : IsSymmetricConvexBody body
  cube_isSymmetricConvexBody : IsSymmetricConvexBody (cube (Fin dimension))
  primal_coverable : Coverable body (cube (Fin dimension))
  dual_coverable : Coverable (polar (cube (Fin dimension))) (a⁻¹ • polar body)
  primal_one_lt : 1 < coveringNumber body (cube (Fin dimension))
  dual_pos : 0 < coveringNumber (polar (cube (Fin dimension))) (a⁻¹ • polar body)
  primal_log_pos : 0 < Real.log (coveringNumber body (cube (Fin dimension)) : ℝ)
  ratio_nonneg : 0 ≤ entropyRatio a body
  ratio_lt : entropyRatio a body < entropyBudget a r B

end MetricEntropyDuality

end

end OAI
