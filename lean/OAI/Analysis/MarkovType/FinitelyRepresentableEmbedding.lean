import OAI.Analysis.MarkovType.FinitelyRepresentable
import OAI.Analysis.MarkovType.FiniteRepresentation

namespace OAI

namespace MarkovSuperreflexivity

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem FinitelyRepresentable.source_linearIsometry (h : FinitelyRepresentable Z X)
    (T : Y →ₗᵢ[ℝ] Z) : FinitelyRepresentable Y X := by
  intro E hE η hη
  let S : E →ₗ[ℝ] Z := T.toLinearMap.comp E.subtype
  let F : Submodule ℝ Z := LinearMap.range S
  let : FiniteDimensional ℝ F := LinearMap.finiteDimensional_range S
  obtain ⟨R, hR⟩ := h F η hη
  refine ⟨R.comp S.rangeRestrict, ?_⟩
  intro z
  have hnorm : ‖S.rangeRestrict z‖ = ‖z‖ := T.norm_map (z : Y)
  simpa only [LinearMap.comp_apply, hnorm] using hR (S.rangeRestrict z)

theorem orderedSpace_finitelyRepresentable_of_coordinates {N : OrderedNorm}
    (h : CoordinatesRepresentable X N) : FinitelyRepresentable (OrderedSpace N) X := by
  have hc : FinitelyRepresentable (UniformSpace.Completion (OrderedSpace N)) X :=
    finitelyRepresentable_completion_of_coordinates N.toSeminorm N.definite h
  exact hc.source_linearIsometry UniformSpace.Completion.toComplₗᵢ

end MarkovSuperreflexivity

end OAI
