import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ResolutionCoefficientSequence

namespace OAI

/-! # Connecting homomorphisms commute with the chosen-resolution comparison -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

def coefficientNaturalCochainMap (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (A : Rep.{0} ℤ G) :
    groupCohomology.inhomogeneousCochains A ⟶ P.complex.linearYonedaObj ℤ A :=
  (groupCohomology.inhomogeneousCochainsIso A).hom ≫
    repCochainPrecomp ℤ (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)).hom A

theorem coefficientNaturalCochainMap_naturality
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    groupCohomology.cochainsMap (MonoidHom.id G) f ≫ coefficientNaturalCochainMap P B =
      coefficientNaturalCochainMap P A ≫ repCochainPostcomp ℤ P.complex f := by
  dsimp [coefficientNaturalCochainMap]
  erw [← Category.assoc, inhomogeneousCochainsIso_coefficient,
    Category.assoc, ← repCochainPrecomp_postcomp, ← Category.assoc]

theorem coefficientNaturalCochainMap_homology
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ)) (A : Rep.{0} ℤ G) (n : ℕ) :
    homologyMap (coefficientNaturalCochainMap P A) n =
      (coefficientNaturalCohomologyIso P A n).hom := by
  change homologyMap ((groupCohomology.inhomogeneousCochainsIso A).hom ≫
      repCochainPrecomp ℤ (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)).hom A) n =
    homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n ≫
      homologyMap (repCochainPrecomp ℤ
        (ProjectiveResolution.homotopyEquiv P (Rep.barResolution ℤ G)).hom A) n
  exact homologyMap_comp _ _ _

def coefficientComparisonSequenceMap (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (S : ShortComplex (Rep.{0} ℤ G)) :
    S.map (groupCohomology.cochainsFunctor ℤ G) ⟶ resolutionCoefficientSequence P S where
  τ₁ := coefficientNaturalCochainMap P S.X₁
  τ₂ := coefficientNaturalCochainMap P S.X₂
  τ₃ := coefficientNaturalCochainMap P S.X₃
  comm₁₂ := (coefficientNaturalCochainMap_naturality P S.f).symm
  comm₂₃ := (coefficientNaturalCochainMap_naturality P S.g).symm

theorem coefficientNaturalCohomologyIso_connecting
    (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) (n : ℕ) :
    groupCohomology.δ hS n (n + 1) rfl ≫ (coefficientNaturalCohomologyIso P S.X₁ (n + 1)).hom =
      (coefficientNaturalCohomologyIso P S.X₃ n).hom ≫
        (resolutionCoefficientSequence_shortExact P S hS).δ n (n + 1) rfl := by
  have h := HomologicalComplex.HomologySequence.δ_naturality
    (coefficientComparisonSequenceMap P S)
    (groupCohomology.map_cochainsFunctor_shortExact hS)
    (resolutionCoefficientSequence_shortExact P S hS) n (n + 1) rfl
  change groupCohomology.δ hS n (n + 1) rfl ≫
      homologyMap (coefficientNaturalCochainMap P S.X₁) (n + 1) =
    homologyMap (coefficientNaturalCochainMap P S.X₃) n ≫
      (resolutionCoefficientSequence_shortExact P S hS).δ n (n + 1) rfl at h
  erw [coefficientNaturalCochainMap_homology, coefficientNaturalCochainMap_homology] at h
  exact h

end PolycyclicRecognition

end

end OAI
