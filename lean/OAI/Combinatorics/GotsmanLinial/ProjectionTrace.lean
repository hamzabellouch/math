import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace

namespace OAI

/-!
# Traces of actual orthogonal projections

The trace calculation uses the algebraic theorem for a projection onto a
submodule. In particular, no spectral decomposition or matrix norm instance
is needed. Matrix transport is valid in every basis, and hence in the
orthonormal basis used for the weighted grading.
-/

noncomputable section

namespace LeanBlast.GotsmanLinial

section General

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The actual orthogonal projection is algebraically a projection onto its
specified submodule. -/
theorem starProjection_isProj (K : Submodule 𝕜 E) :
    LinearMap.IsProj K K.starProjection.toLinearMap where
  map_mem := K.starProjection_apply_mem
  map_id := fun _ hx => Submodule.starProjection_eq_self_iff.mpr hx

/-- The trace of the actual orthogonal projection is the dimension of its range. -/
theorem trace_starProjection (K : Submodule 𝕜 E) :
    LinearMap.trace 𝕜 E K.starProjection.toLinearMap = (Module.finrank 𝕜 K : 𝕜) :=
  (starProjection_isProj K).trace

variable [Fintype ι] [DecidableEq ι]

/-- The matrix trace of an orthogonal projection is independent of the chosen basis. -/
theorem trace_toMatrix_starProjection (b : Module.Basis ι 𝕜 E) (K : Submodule 𝕜 E) :
    Matrix.trace (LinearMap.toMatrix b b K.starProjection.toLinearMap) =
      (Module.finrank 𝕜 K : 𝕜) := by
  rw [← LinearMap.trace_eq_matrix_trace 𝕜 b, trace_starProjection]

/-- The orthonormal matrix representation used by the grading has the correct trace. -/
theorem trace_toMatrixOrthonormal_starProjection (b : OrthonormalBasis ι 𝕜 E)
    (K : Submodule 𝕜 E) :
    Matrix.trace (LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap) =
      (Module.finrank 𝕜 K : 𝕜) :=
  trace_toMatrix_starProjection b.toBasis K

end General

section Complex

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

/-- The real trace required by Hilbert--Schmidt block-mass computations. -/
theorem re_trace_toMatrixOrthonormal_starProjection (b : OrthonormalBasis ι ℂ E)
    (K : Submodule ℂ E) :
    (Matrix.trace (LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap)).re =
      (Module.finrank ℂ K : ℝ) := by
  rw [trace_toMatrixOrthonormal_starProjection]
  simp

end Complex

end LeanBlast.GotsmanLinial

end

end OAI
