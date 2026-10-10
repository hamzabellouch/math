import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace PiExponent.CompactJetIdeal

universe u
variable {U X S : Scheme.{u}}

def extend (I : U.IdealSheafData) (j : U ⟶ X) : X.IdealSheafData := I.map j

theorem restrict_extend (I : U.IdealSheafData) (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] : (extend I j).comap j = I := by
  apply Scheme.IdealSheafData.ext
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have hsq : IsPullback I.subschemeι (𝟙 I.subscheme) j (I.subschemeι ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (I.subschemeι ≫ j) I.subschemeι (𝟙 I.subscheme) j hsq W
  simpa only [Scheme.IdealSheafData.ker_subschemeι, extend, Scheme.IdealSheafData.map] using h.symm

theorem section_isClosedImmersion (π : X ⟶ S) [IsSeparated π]
    (p : S ⟶ X) (hp : p ≫ π = 𝟙 S) : IsClosedImmersion p := by
  have : IsClosedImmersion (p ≫ π) := by rw [hp]; infer_instance
  exact IsClosedImmersion.of_comp p π

theorem image_support_isClosed {J : Type*} [Finite J]
    (I : U.IdealSheafData) (j : U ⟶ X)
    (π : X ⟶ S) [IsSeparated π]
    (p : J → (S ⟶ U)) (hp : ∀ a, (p a ≫ j) ≫ π = 𝟙 S)
    (hsupport : (I.support : Set U) = ⋃ a, Set.range (p a)) :
    IsClosed (j '' (I.support : Set U)) := by
  have heq : j '' (I.support : Set U) = ⋃ a, Set.range (p a ≫ j) := by
    rw [hsupport, Set.image_iUnion]
    congr 1
    funext a
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro a
  have := section_isClosedImmersion π (p a ≫ j) (hp a)
  exact (p a ≫ j).isClosedEmbedding.isClosed_range

theorem support_extend {J : Type*} [Finite J]
    (I : U.IdealSheafData) (j : U ⟶ X) [QuasiCompact j]
    (π : X ⟶ S) [IsSeparated π]
    (p : J → (S ⟶ U)) (hp : ∀ a, (p a ≫ j) ≫ π = 𝟙 S)
    (hsupport : (I.support : Set U) = ⋃ a, Set.range (p a)) :
    ((extend I j).support : Set X) = j '' (I.support : Set U) := by
  change ((I.map j).support : Set X) = _
  rw [Scheme.IdealSheafData.support_map]
  exact (image_support_isClosed I j π p hp hsupport).closure_eq

theorem restrict_eq_top_of_disjoint (I : X.IdealSheafData)
    {V : Scheme.{u}} (f : V ⟶ X)
    (havoid : ∀ v, f v ∉ I.support) : I.comap f = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff (I.comap f)).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext v
  exact ⟨fun h => (havoid v h).elim, False.elim⟩

abbrev affineBlowup {R : Type u} [CommRing R] (I : Ideal R) : Scheme.{u} :=
  PiExponentSeshadri.ReesGrading.affineBlowup I

end PiExponent.CompactJetIdeal
end

end OAI
