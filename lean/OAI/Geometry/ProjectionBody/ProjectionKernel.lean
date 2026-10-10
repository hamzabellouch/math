import OAI.Geometry.ProjectionBody.Definitions

namespace OAI

noncomputable section

namespace ProjectionCounterexample

@[simp] theorem project_self {d : ℕ} (u : E d) : project u u = 0 :=
  Submodule.starProjection_orthogonalComplement_singleton_eq_zero u

theorem project_ker {d : ℕ} (u : E d) :
    (project u).toLinearMap.ker = Submodule.span ℝ {u} := by
  change (ℝ ∙ u)ᗮ.starProjection.ker = ℝ ∙ u
  rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]

end ProjectionCounterexample

end

end OAI
