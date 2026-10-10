import OAI.Analysis.MarkovType.StructuralL2Estimates
import OAI.Analysis.MarkovType.FiniteLowerL2Cotype
import OAI.Analysis.MarkovType.TriangularReflexivity
import OAI.Analysis.MarkovType.TriangularRepresentability

namespace OAI

namespace MarkovSuperreflexivity

universe u v
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem hasEquivalentUCNorm_of_finiteTriangularObstruction
    (h : FiniteTriangularObstruction X) : HasEquivalentUCNorm X := by
  obtain ⟨s, hs, χ, hχ, hLower⟩ := finiteLowerL2_of_obstruction h
  exact hasEquivalentUCNorm_of_finiteLowerL2 hs hχ hLower

theorem hasEquivalentUCNorm_iff_finiteTriangularObstruction :
    HasEquivalentUCNorm X ↔ FiniteTriangularObstruction X :=
  ⟨finiteTriangularObstruction_of_hasEquivalentUCNorm,
    hasEquivalentUCNorm_of_finiteTriangularObstruction⟩

theorem hasEquivalentUCNorm_of_hasEquivalentUSNorm (h : HasEquivalentUSNorm X) :
    HasEquivalentUCNorm X :=
  hasEquivalentUCNorm_of_finiteTriangularObstruction
    (finiteTriangularObstruction_of_hasEquivalentUSNorm h)

theorem HasEquivalentUCNorm.canonicallyReflexive_of_finitelyRepresentable
    [CompleteSpace Y] (h : HasEquivalentUCNorm X) (hYX : FinitelyRepresentable Y X) :
    CanonicallyReflexive Y :=
  canonicallyReflexive_of_finitelyRepresentable_of_triangularObstruction
    (finiteTriangularObstruction_of_hasEquivalentUCNorm h) hYX

theorem exists_nonreflexive_finitelyRepresentable_of_not_hasEquivalentUCNorm
    (h : ¬ HasEquivalentUCNorm X) :
    ∃ (θ : ℝ) (hθ : 0 < θ) (s : ∀ n, TriangularSystem X n θ),
      FinitelyRepresentable (TriangularLimit.Space s hθ) X ∧
        ¬ CanonicallyReflexive (TriangularLimit.Space s hθ) := by
  apply exists_nonreflexive_finitelyRepresentable_of_not_obstruction
  exact fun hObstruction => h (hasEquivalentUCNorm_of_finiteTriangularObstruction hObstruction)

theorem hasEquivalentUCNorm_of_reflexive_finitelyRepresentable
    (h : ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z],
      FinitelyRepresentable Z X → CanonicallyReflexive Z) : HasEquivalentUCNorm X := by
  by_contra hnot
  obtain ⟨θ, hθ, s, hrep, hNR⟩ :=
    exists_nonreflexive_finitelyRepresentable_of_not_hasEquivalentUCNorm hnot
  exact hNR (h (TriangularLimit.Space s hθ) hrep)

end MarkovSuperreflexivity

end OAI
