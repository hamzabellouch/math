import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Discrete.Basic

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) [G.EssSurj] (F : Discrete ℕ ⥤ C) (s : Cocone F) (hs : IsColimit s)
  (hp : ∀ T : C, Function.Bijective (G.map : (s.pt ⟶ T) → (G.obj s.pt ⟶ G.obj T)))
  (hF : ∀ (r : Discrete ℕ) (T : C),
    Function.Bijective (G.map : (F.obj r ⟶ T) → (G.obj (F.obj r) ⟶ G.obj T)))

def homBijectionCoconeLift (t : Cocone (F ⋙ G)) : Cocone F where
  pt := G.objPreimage t.pt
  ι := Discrete.natTrans (fun r =>
    (Equiv.ofBijective _ (hF r (G.objPreimage t.pt))).symm
      (t.ι.app r ≫ (G.objObjPreimageIso t.pt).inv))

theorem homBijectionCoconeLift_map (t : Cocone (F ⋙ G)) (r : Discrete ℕ) :
    G.map ((homBijectionCoconeLift G F hF t).ι.app r) =
      t.ι.app r ≫ (G.objObjPreimageIso t.pt).inv :=
  (Equiv.ofBijective _ (hF r (G.objPreimage t.pt))).apply_symm_apply _

/-- A coproduct's full Hom universal property transfers through an essentially
surjective functor when Hom is bijective on its summands and its point. -/
def mapCoproductOfHomBijections : IsColimit (G.mapCocone s) where
  desc t := G.map (hs.desc (homBijectionCoconeLift G F hF t)) ≫ (G.objObjPreimageIso t.pt).hom
  fac t r := by
    change G.map (s.ι.app r) ≫ G.map (hs.desc (homBijectionCoconeLift G F hF t)) ≫
      (G.objObjPreimageIso t.pt).hom = t.ι.app r
    erw [← Category.assoc, ← Functor.map_comp, hs.fac, homBijectionCoconeLift_map]
    change (t.ι.app r ≫ (G.objObjPreimageIso t.pt).inv) ≫ (G.objObjPreimageIso t.pt).hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  uniq t m hm := by
    let e := G.objObjPreimageIso t.pt
    let u := (Equiv.ofBijective _ (hp (G.objPreimage t.pt))).symm (m ≫ e.inv)
    have hu : G.map u=m ≫ e.inv :=
      (Equiv.ofBijective _ (hp (G.objPreimage t.pt))).apply_symm_apply _
    have heq : u=hs.desc (homBijectionCoconeLift G F hF t) := by
      apply hs.hom_ext
      intro r
      erw [hs.fac]
      apply (hF r (G.objPreimage t.pt)).injective
      have hmr := hm r
      change G.map (s.ι.app r) ≫ m = t.ι.app r at hmr
      have hleft : G.map (s.ι.app r ≫ u) = t.ι.app r ≫ e.inv := by
        rw [Functor.map_comp, hu, ← Category.assoc, hmr]
      exact hleft.trans (homBijectionCoconeLift_map G F hF t r).symm
    calc
      m = G.map u ≫ e.hom := by rw [hu]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = _ := by rw [heq]; rfl
end DerivedBar

end

end OAI
