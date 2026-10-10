import OAI.Analysis.MarkovType.FailureJTriangular
import OAI.Analysis.MarkovType.TriangularRepresentability

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def failureJSystems (h : ¬ AmbientJConvex X) :
    ∀ n : ℕ, TriangularSystem X n (1 / 2) :=
  fun n => Classical.choice (exact_triangular_system_of_not_jConvex h n)

abbrev FailureJSpace (h : ¬ AmbientJConvex X) :=
  TriangularLimit.Space (failureJSystems h) (by norm_num : (0 : ℝ) < 1 / 2)

theorem failureJSpace_finitelyRepresentable (h : ¬ AmbientJConvex X) :
    FinitelyRepresentable (FailureJSpace h) X :=
  TriangularLimit.finitelyRepresentable (failureJSystems h) (by norm_num)

theorem failureJSpace_not_canonicallyReflexive (h : ¬ AmbientJConvex X) :
    ¬ CanonicallyReflexive (FailureJSpace h) :=
  TriangularLimit.not_canonicallyReflexive (failureJSystems h) (by norm_num)

theorem exists_nonreflexive_finitelyRepresentable_of_not_jConvex
    (h : ¬ AmbientJConvex X) :
    ∃ (θ : ℝ) (hθ : 0 < θ) (s : ∀ n : ℕ, TriangularSystem X n θ),
      FinitelyRepresentable (TriangularLimit.Space s hθ) X ∧
        ¬ CanonicallyReflexive (TriangularLimit.Space s hθ) :=
  ⟨1 / 2, by norm_num, failureJSystems h,
    failureJSpace_finitelyRepresentable h, failureJSpace_not_canonicallyReflexive h⟩

end MarkovSuperreflexivity

end

end OAI
