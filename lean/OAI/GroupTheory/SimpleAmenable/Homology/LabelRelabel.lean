import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.LabelledMonoidal

namespace OAI

section
open CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled

variable {a n m : ℕ}
abbrev Reduced (g : Fin n → CutRing × CutRing) : Prop :=
  ∀ i, orbitRepresentative (g i)=g i
variable (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
  (hf : ∀g, Reduced g → Reduced (f g))
noncomputable def relabel : Labelled a n ⥤ Labelled a m where
  obj U := ⟨U.polygon,fun k => f (U.label k),fun k => hf _ (U.reduced k)⟩
  map g := ⟨g.arrow,g.positional,fun x => congrArg f (g.labelled x)⟩
  map_id _ := Hom.ext _ _ rfl
  map_comp _ _ := Hom.ext _ _ rfl
noncomputable def relabelUnit : 𝟙_ (Labelled a m) ⟶ (relabel f hf).obj (𝟙_ (Labelled a n)) where
  arrow := 𝟙 _
  positional _ := rfl
  labelled x := by
    change Point PolygonObject.empty at x
    exact isEmptyElim x
noncomputable def relabelTensor (U V : Labelled a n) :
    (relabel f hf).obj U ⊗ (relabel f hf).obj V ⟶ (relabel f hf).obj (U ⊗ V) where
  arrow := 𝟙 _
  positional _ := rfl
  labelled x := by
    change f ((sum U V).label x.val.1) =
      (sum ((relabel f hf).obj U) ((relabel f hf).obj V)).label x.val.1
    obtain ⟨y,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective x
    cases y <;> simp only [relabel,sumPointEquiv_inl,sumPointEquiv_inr,Fin.addCases_left,Fin.addCases_right]
noncomputable instance relabelMonoidal : (relabel (a:=a) f hf).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso (relabelUnit f hf)
    μIso U V := asIso (relabelTensor f hf U V)
    μIso_hom_natural_left := by
      intros; apply Hom.ext
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id]
      rfl
    μIso_hom_natural_right := by
      intros; apply Hom.ext
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id]
      rfl
    associativity := by
      intros; apply Hom.ext
      change sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ _ = _ ≫ sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _
      simp only [sumArrow_id,Category.id_comp,Category.comp_id]
      rfl
    left_unitality := by
      intros; apply Hom.ext
      change _ = sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ _
      simp only [sumArrow_id,Category.id_comp]
      rfl
    right_unitality := by
      intros; apply Hom.ext
      change _ = sumArrow (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ _
      simp only [sumArrow_id,Category.id_comp]
      rfl }
noncomputable instance relabelBraided : (relabel (a:=a) f hf).Braided where
  braided U V := by
    apply Hom.ext
    change 𝟙 _ ≫ sumSwap U.polygon V.polygon = sumSwap U.polygon V.polygon ≫ 𝟙 _
    simp only [Category.id_comp,Category.comp_id]
@[simp] lemma relabel_map_arrow {U V : Labelled a n} (g:U⟶V) :
    ((relabel f hf).map g).arrow=g.arrow := rfl
@[simp] lemma relabel_ε_arrow : (Functor.LaxMonoidal.ε (relabel (a:=a) f hf)).arrow=𝟙 _ := rfl
@[simp] lemma relabel_μ_arrow (U V : Labelled a n) :
    (Functor.LaxMonoidal.μ (relabel f hf) U V).arrow=𝟙 _ := rfl
end SimpleAmenable.PolygonObject.Labelled

end

end OAI
