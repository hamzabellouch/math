import OAI.Algebra.AuslanderReiten.HomComplex.FullHomLinear
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

namespace OAI

open CategoryTheory CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit

universe u v w

section Homotopy

variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ) (n : ℤ)

noncomputable def fullHomHomotopyLinearEquiv :
    CohomologyClass K L n ≃ₗ[k]
      ((HomotopyCategory.quotient C _).obj K ⟶
        (HomotopyCategory.quotient C _).obj (L⟦n⟧)) :=
  { CohomologyClass.homAddEquiv with
    map_smul' := by
      intro a x
      obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
      change CohomologyClass.toHom (CohomologyClass.mk (a • x)) =
        a • CohomologyClass.toHom (CohomologyClass.mk x)
      rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk,
        CompleteComparison.cocycleHom_smul, Functor.map_smul] }

end Homotopy

section Triangle

variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)

include hT

theorem triangleHom_middle_exact :
    LinearMap.range (Linear.rightComp k X T.mor₁) =
      LinearMap.ker (Linear.rightComp k X T.mor₂) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change (g ≫ T.mor₁) ≫ T.mor₂ = 0
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, Limits.comp_zero]
  · intro h
    obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT f h
    exact ⟨g, hg.symm⟩

theorem triangleHom_top_exact :
    LinearMap.range (Linear.rightComp k X T.mor₂) =
      LinearMap.ker (Linear.rightComp k X T.mor₃) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change (g ≫ T.mor₂) ≫ T.mor₃ = 0
    rw [Category.assoc, comp_distTriang_mor_zero₂₃ T hT, Limits.comp_zero]
  · intro h
    obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT f h
    exact ⟨g, hg.symm⟩

theorem triangleHom_bottom_exact :
    LinearMap.range (Linear.rightComp k X T.mor₃) =
      LinearMap.ker (Linear.rightComp k X (T.mor₁⟦(1 : ℤ)⟧')) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change (g ≫ T.mor₃) ≫ T.mor₁⟦(1 : ℤ)⟧' = 0
    rw [Category.assoc, comp_distTriang_mor_zero₃₁ T hT, Limits.comp_zero]
  · intro h
    obtain ⟨g, hg⟩ := T.coyoneda_exact₁ hT f h
    exact ⟨g, hg.symm⟩

theorem shiftedTriangleHom_middle_exact (n : ℤ) :
    LinearMap.range (Linear.rightComp k X (T⟦n⟧).mor₁) =
      LinearMap.ker (Linear.rightComp k X (T⟦n⟧).mor₂) :=
  triangleHom_middle_exact k _ (T.shift_distinguished hT n) X

theorem shiftedTriangleHom_top_exact (n : ℤ) :
    LinearMap.range (Linear.rightComp k X (T⟦n⟧).mor₂) =
      LinearMap.ker (Linear.rightComp k X (T⟦n⟧).mor₃) :=
  triangleHom_top_exact k _ (T.shift_distinguished hT n) X

theorem shiftedTriangleHom_bottom_exact (n : ℤ) :
    LinearMap.range (Linear.rightComp k X (T⟦n⟧).mor₃) =
      LinearMap.ker (Linear.rightComp k X ((T⟦n⟧).mor₁⟦(1 : ℤ)⟧')) :=
  triangleHom_bottom_exact k _ (T.shift_distinguished hT n) X

end Triangle
end ArExplicit

end OAI
