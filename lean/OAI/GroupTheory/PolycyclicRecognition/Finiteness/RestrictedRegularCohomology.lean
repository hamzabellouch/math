import OAI.GroupTheory.PolycyclicRecognition.Algebra.RestrictedRegular
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InductionCochains
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

namespace OAI

/-! # Cohomology of the restricted regular module in a duality group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def restrictedRegularCohomologyIso
    (P : ProjectiveResolution (trivialIntegral N))
    (hP : ∀ i, IntegralRepresentationFinite N (P.complex.X i)) (i : ℕ) :
    groupCohomology (Rep.res N.subtype (Rep.leftRegular ℤ G)) i ≅
      (integralFinsuppFunctor (G ⧸ N)).obj
        (groupCohomology (Rep.leftRegular ℤ N) i) :=
  (groupCohomology.functor ℤ N i).mapIso (restrictedRegularIso ℤ N) ≪≫
    finsuppCohomologyIso ℤ N (G ⧸ N) P hP (Rep.leftRegular ℤ N) i

theorem restrictedRegularCohomology_isZero {n : ℕ}
    (hN : IsIntegralPoincareDualityGroup N n) (i : ℕ) (hi : i ≠ n) :
    IsZero (groupCohomology (Rep.res N.subtype (Rep.leftRegular ℤ G)) i) := by
  obtain ⟨P, d, hP, hd⟩ := hN.1
  exact IsZero.of_iso ((integralFinsuppFunctor (G ⧸ N)).map_isZero (hN.2.1 i hi))
    (restrictedRegularCohomologyIso N P hP i)

theorem restrictedRegularCohomology_top {n : ℕ}
    (hN : IsIntegralPoincareDualityGroup N n) :
    Nonempty (groupCohomology (Rep.res N.subtype (Rep.leftRegular ℤ G)) n ≅
      ModuleCat.of ℤ ((G ⧸ N) →₀ ℤ)) := by
  obtain ⟨P, d, hP, hd⟩ := hN.1
  obtain ⟨e⟩ := hN.2.2
  exact ⟨restrictedRegularCohomologyIso N P hP n ≪≫
    (integralFinsuppFunctor (G ⧸ N)).mapIso e⟩

def inducedRegularCohomologyIso
    (P : ProjectiveResolution (trivialIntegral N))
    (hP : ∀ i, IntegralRepresentationFinite N (P.complex.X i)) (i : ℕ) :
    ((normalInducedResolution ℤ N P).complex.linearYonedaObj ℤ
      (Rep.leftRegular ℤ G)).homology i ≅
        (integralFinsuppFunctor (G ⧸ N)).obj
          (groupCohomology (Rep.leftRegular ℤ N) i) :=
  (normalInducedCohomologyIso N P (Rep.leftRegular ℤ G) i).symm ≪≫
    restrictedRegularCohomologyIso N P hP i

end PolycyclicRecognition

end

end OAI
