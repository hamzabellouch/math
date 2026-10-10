import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ConeHomology
import OAI.GroupTheory.SimpleAmenable.Homology.TotalFiniteness

namespace OAI

section

section
open CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalComparison

universe u
variable {R : Type u} [CommRing R]
abbrev c := ComplexShape.down ℕ
variable {K L : HomologicalComplex₂ (ModuleCat.{u} R) c c} (φ : K ⟶ L)
noncomputable def rowMap (q : ℕ) : TotalFiniteness.row K q ⟶ TotalFiniteness.row L q :=
  ((homologyFunctor (ModuleCat.{u} R) c q).mapHomologicalComplex c).map φ
lemma rowMap_isIso (q : ℕ) (hφ : ∀ p,IsIso (homologyMap (φ.f p) q)) : IsIso (rowMap φ q) := by
  have : ∀ p,IsIso ((rowMap φ q).f p) := hφ
  exact HomologicalComplex.Hom.isIso_of_components _
noncomputable def rowConeIso (q : ℕ) :
    TotalFiniteness.row (TotalCone.B φ) q ≅ homotopyCofiber (rowMap φ q) :=
  homotopyCofiber.mapHomologicalComplexObjIso φ (homologyFunctor (ModuleCat.{u} R) c q)
lemma rowCone_zero (hφ : ∀ p q,IsIso (homologyMap (φ.f p) q)) (p q : ℕ) :
    Subsingleton ((TotalFiniteness.row (TotalCone.B φ) q).homology p) := by
  have := rowMap_isIso φ q (fun p => hφ p q)
  have := ConeCoordinates.cone_subsingleton_of_iso (rowMap φ q) p
  let e := (homologyFunctor (ModuleCat.{u} R) c p).mapIso (rowConeIso φ q) ≪≫
    ConcreteHomology.iso _ p
  exact e.toLinearEquiv.injective.subsingleton
lemma cone_zero (hφ : ∀ p q,IsIso (homologyMap (φ.f p) q)) (n : ℕ) :
    Subsingleton (ConcreteHomology.H (homotopyCofiber (total.map φ c)) n) := by
  have := TotalFiniteness.subsingleton (TotalCone.B φ) n (fun p q _ => rowCone_zero φ hφ p q)
  let e := (ConcreteHomology.functor (R:=R) n).mapIso (TotalCone.iso φ) ≪≫
    (ConcreteHomology.iso ((TotalCone.B φ).total c) n).symm
  exact e.toLinearEquiv.injective.subsingleton
lemma total_homology_isIso (hφ : ∀ p q,IsIso (homologyMap (φ.f p) q)) (n : ℕ) :
    IsIso (homologyMap (total.map φ c) n) := by
  have := cone_zero φ hφ n
  have := cone_zero φ hφ (n+1)
  have : IsIso ((ConcreteHomology.functor n).map (total.map φ c)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨ConeCoordinates.injective_of_cone_zero _ n,ConeCoordinates.surjective_of_cone_zero _ n⟩
  exact (NatIso.isIso_map_iff (ConcreteHomology.naturalIso (R:=R) n) (total.map φ c)).mpr inferInstance
end TotalComparison

end

end

end OAI
