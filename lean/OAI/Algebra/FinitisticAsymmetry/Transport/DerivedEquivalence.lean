import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
section DerivedTransport
universe w₁ w₂ v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
open CategoryTheory.Limits CategoryTheory.Functor

lemma mapDerivedCategory_isEquivalence (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] :
    e.functor.mapDerivedCategory.IsEquivalence := by
  let f := e.functor.mapHomologicalComplex (ComplexShape.up ℤ)
  let g := e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)
  let qC := DerivedCategory.Q (C := C)
  let qD := DerivedCategory.Q (C := D)
  let α : (f ⋙ qD) ⋙ e.inverse.mapDerivedCategory ≅ qC :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft f e.inverse.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (e.mapHomologicalComplex (ComplexShape.up ℤ)).unitIso.symm qC ≪≫
    Functor.leftUnitor qC
  let β : (g ⋙ qC) ⋙ e.functor.mapDerivedCategory ≅ qD :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft g e.functor.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (e.mapHomologicalComplex (ComplexShape.up ℤ)).counitIso qD ≪≫
    Functor.leftUnitor qD
  exact Localization.isEquivalence qC (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    qD (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (f ⋙ qD) e.functor.mapDerivedCategory
    (g ⋙ qC) e.inverse.mapDerivedCategory α β

end DerivedTransport

end LittleFinitistic
end
end
end

end OAI
