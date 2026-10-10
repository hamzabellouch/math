import Mathlib
import OAI.Analysis.Commutator.FreePositionObstruction
import OAI.Analysis.Commutator.TracialGeneratedAlgebra

namespace OAI

noncomputable section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

open Filter

namespace Kadison.VectorFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma functional_star (x : H) (T : H →L[ℂ] H) : functional x (star T)=star (functional x T) :=
  map_star (functional x) T

end Kadison.VectorFunctional

namespace Kadison.TracialSequence

open FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (D : VonNeumannAlgebra (boundedSubspace τ ω))
  (hfaith : ∀ a : A,τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include hfaith h1 in
theorem constant_in_free_subalgebra_scalar
    (hfree : Free (GeneratedFreePair.ambient D (constantAction τ ω))
      (VectorFunctional.functional (sequenceVacuum τ ω)).toLinearMap)
    (a : A) (ha : constantAction τ ω a∈D) : a=τ a • (1:A) := by
  apply mapped_intersection_scalar
    (GeneratedFreePair.ambient D (constantAction τ ω)) τ.toLinearMap
    (VectorFunctional.functional (sequenceVacuum τ ω)).toLinearMap
    (constantAction τ ω) (trace_constant τ ω)
    (VectorFunctional.functional_star (sequenceVacuum τ ω))
    hfaith h1 hfree (show (false:Bool)≠true by decide) a
  · exact ha
  · exact Set.mem_range_self a

include hfaith h1 in
theorem not_free_of_nonscalar_constant
    (a : A) (ha : constantAction τ ω a∈D) (hne : a≠τ a • (1:A)) :
    ¬Free (GeneratedFreePair.ambient D (constantAction τ ω))
      (VectorFunctional.functional (sequenceVacuum τ ω)).toLinearMap := by
  intro hfree
  exact hne (constant_in_free_subalgebra_scalar τ ω D hfaith h1 hfree a ha)

end Kadison.TracialSequence
end
end

end OAI
