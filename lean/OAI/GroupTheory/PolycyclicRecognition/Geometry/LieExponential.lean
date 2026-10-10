import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Exponential maps of actual real Lie groups

The differential and one-parameter-subgroup characterization identifies the
ordinary Lie-group exponential without requiring a pre-existing library
construction of its global flow.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The intrinsic exponential, characterized by its one-parameter subgroups
and their tangent vectors at the identity. The Lie algebra here is the actual
tangent Lie algebra of `G`, with its invariant-vector-field bracket. -/
structure IsGroupExponential (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) : Prop where
  map_zero : Exp 0 = 1
  map_add_smul : ∀ (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s t : ℝ),
    Exp ((s + t) • v) = Exp (s • v) * Exp (t • v)
  hasMFDerivAt_zero : ∀ v : GroupLieAlgebra (𝓘(ℝ, E)) G,
    HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ => Exp (t • v)) 0
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v)

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem IsGroupExponential.map_neg
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : Exp (-v) = (Exp v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have h := hExp.map_add_smul v (-1) 1
  simpa only [neg_add_cancel, zero_smul, neg_one_smul, one_smul, hExp.map_zero] using h.symm

end PolycyclicRecognition

end

end OAI
