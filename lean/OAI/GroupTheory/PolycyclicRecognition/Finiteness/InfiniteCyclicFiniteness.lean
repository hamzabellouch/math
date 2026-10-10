import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InfiniteCyclicResolution

namespace OAI

/-! # Finiteness of the two-term infinite cyclic resolution -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped MonoidAlgebra

theorem integralRepresentationFinite_leftRegular (G : Type) [Group G] :
    IntegralRepresentationFinite G (Rep.leftRegular ℤ G) := by
  exact Module.Finite.equiv
    (Representation.ofMulActionSelfAsModuleEquiv (k := ℤ) (G := G)).symm

variable (G : Type) [CommGroup G] [Infinite G]

omit [Infinite G] in
theorem infiniteCyclicComplex_isZero (g : G) (i : ℕ) (hi : 1 < i) :
    IsZero ((infiniteCyclicComplex G g).X i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  exact isZero_zero _

theorem finiteProjectiveResolution_of_infinite_cyclic (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : HasFiniteProjectiveResolution G := by
  refine ⟨infiniteCyclicResolution G g hg, 1, ?_, infiniteCyclicComplex_isZero G g⟩
  intro i
  rcases i with _ | _ | i
  · exact integralRepresentationFinite_leftRegular G
  · exact integralRepresentationFinite_leftRegular G
  · exact integralRepresentationFinite_of_isZero G _ (isZero_zero _)

theorem typeFPInfinity_of_infinite_cyclic (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : TypeFPInfinity G :=
  (finiteProjectiveResolution_of_infinite_cyclic G g hg).typeFPInfinity G

theorem finiteCohomologicalDimension_of_infinite_cyclic (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : HasFiniteIntegralCohomologicalDimension G :=
  (finiteProjectiveResolution_of_infinite_cyclic G g hg).finiteCohomologicalDimension G

end PolycyclicRecognition

end

end OAI
