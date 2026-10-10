import Mathlib.CategoryTheory.Triangulated.Pretriangulated

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Pretriangulated
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (T : Triangle C) {Y : C} (e : T.obj₂ ≅ Y)

def triangleReplaceMiddle : Triangle C :=
  Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃

def triangleReplaceMiddleIso : T ≅ triangleReplaceMiddle T e :=
  Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
    (by
      change T.mor₁ ≫ e.hom = 𝟙 _ ≫ (T.mor₁ ≫ e.hom)
      rw [Category.id_comp])
    (by
      change T.mor₂ ≫ 𝟙 _ = e.hom ≫ (e.inv ≫ T.mor₂)
      rw [Category.comp_id, Iso.hom_inv_id_assoc])
    (by
      change T.mor₃ ≫ (CategoryTheory.shiftFunctor C 1).map (𝟙 _) = 𝟙 _ ≫ T.mor₃
      rw [(CategoryTheory.shiftFunctor C 1).map_id, Category.id_comp, Category.comp_id])

variable [Preadditive C] [Limits.HasZeroObject C]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

theorem triangleReplaceMiddle_distinguished (hT : T ∈ distTriang C) :
    triangleReplaceMiddle T e ∈ distTriang C :=
  (distinguished_iff_of_iso (triangleReplaceMiddleIso T e)).mp hT

end ArExplicit

end

end OAI
