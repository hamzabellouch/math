import OAI.Analysis.MarkovType.OrderedJColumns
import OAI.Analysis.MarkovType.OrderedBoundedCubes
import OAI.Analysis.MarkovType.JamesCubeImprovement
import OAI.Analysis.MarkovType.CubeNotJConvex
import OAI.Analysis.MarkovType.SpreadingConstruction
import OAI.Analysis.MarkovType.SubdivisionOrderedNorm
import OAI.Analysis.MarkovType.FinitelyRepresentableEmbedding
import OAI.Analysis.MarkovType.JConvexityFiniteRepresentability
import OAI.Analysis.MarkovType.TriangularRepresentability

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

theorem OrderedNorm.not_ambientJConvex_of_scaled_subdivision (N : OrderedNorm)
    (hsub : ∀ q : ℕ, 0 < q → ∀ x : C00,
      N ((q : ℝ) • C00.uniformSubdivision q x) = (q : ℝ) * N x) :
    ¬ AmbientJConvex (OrderedSpace N) := by
  classical
  by_cases hb : BddAbove (Set.range N.alternatingNorm)
  · obtain ⟨L, hL, hcopies⟩ := N.exists_uniform_cubes_of_bounded_alternating hb
    apply not_ambientJConvex_of_nearIsometric_cubes
    intro n η hη
    exact james_cube_improvement L hL hcopies n hη
  · intro hJ
    obtain ⟨n, hn, δ, hδ, _hδ1, hw⟩ := hJ
    obtain ⟨x, hx, hcuts⟩ := N.exists_unit_jColumns_of_unbounded hsub hb n (by omega) hδ
    let y : Fin n → OrderedSpace N := fun j => x j
    have hy (j : Fin n) : ‖y j‖ ≤ 1 := by
      change N (x j) ≤ 1
      exact (hx j).le
    obtain ⟨r, hr⟩ := hw y hy
    have hstrict := hcuts r
    change (n : ℝ) * (1 - δ) < ‖cutSum y r‖ at hstrict
    exact (not_lt_of_ge hr) hstrict

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem not_ambientJConvex_of_not_canonicallyReflexive [CompleteSpace Y]
    (hNR : ¬ CanonicallyReflexive Y) : ¬ AmbientJConvex Y := by
  obtain ⟨S⟩ := exists_spreadingModel_of_nonreflexive hNR
  intro hJ
  have hrep : FinitelyRepresentable (OrderedSpace S.orderedNorm) Y :=
    orderedSpace_finitelyRepresentable_of_coordinates S.orderedNorm_representable
  have hordered : AmbientJConvex (OrderedSpace S.orderedNorm) :=
    hJ.finitelyRepresentable hrep
  exact S.orderedNorm.not_ambientJConvex_of_scaled_subdivision
    (fun q hq x => S.orderedNorm_scaled_uniform q hq x) hordered

theorem AmbientJConvex.finiteTriangularObstruction
    (hX : AmbientJConvex X) : FiniteTriangularObstruction X := by
  by_contra hnot
  obtain ⟨θ, hθ, s, hrep, hNR⟩ :=
    exists_nonreflexive_finitelyRepresentable_of_not_obstruction hnot
  exact not_ambientJConvex_of_not_canonicallyReflexive hNR
    (hX.finitelyRepresentable hrep)

end MarkovSuperreflexivity

end

end OAI
