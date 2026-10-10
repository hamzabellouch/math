import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FilteredHomology

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace StageProductColimit

variable {C D : Type} [Category.{0} C] [Category.{0} D] (κ ι : Type)
noncomputable instance (F : C ⥤ D) [F.Full] : (powerMap κ F).Full where
  map_surjective f := ⟨fun i => F.preimage (f i),by funext i; exact F.map_preimage (f i)⟩
noncomputable instance (F : C ⥤ D) [F.EssSurj] : (powerMap κ F).EssSurj where
  mem_essImage X := ⟨fun i => F.objPreimage (X i),⟨{
    hom i := (F.objObjPreimageIso (X i)).hom
    inv i := (F.objObjPreimageIso (X i)).inv
    hom_inv_id := by funext i; exact Iso.hom_inv_id _
    inv_hom_id := by funext i; exact Iso.inv_hom_id _ }⟩⟩
noncomputable instance (F : C ⥤ D) [F.IsEquivalence] : (powerMap κ F).IsEquivalence where

def uncurry : (κ → ι → C) ⥤ (κ × ι → C) where
  obj U i := U i.1 i.2
  map f i := f i.1 i.2
def curry : (κ × ι → C) ⥤ (κ → ι → C) where
  obj U i j := U (i,j)
  map f i j := f (i,j)
noncomputable def curryEquiv : (κ → ι → C) ≌ (κ × ι → C) where
  functor := uncurry κ ι
  inverse := curry κ ι
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom]
    erw [Category.id_comp, Category.comp_id]
    rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp only [Iso.refl_hom]
    erw [Category.id_comp, Category.comp_id]
    rfl)
  functor_unitIso_comp := by
    intro X
    funext i
    change 𝟙 (X i.1 i.2) ≫ 𝟙 (X i.1 i.2) = 𝟙 (X i.1 i.2)
    exact Category.id_comp _
instance : (uncurry (C:=C) κ ι).IsEquivalence := (curryEquiv κ ι).isEquivalence_functor
end StageProductColimit
namespace IntervalBar.Diagram
open StageProductColimit MonoidalCategory

variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
noncomputable def eval₂ (m n:ℕ) : Diagram (Diagram C (Fin (n+1))) (Fin (m+1)) ⥤
    (Fin m × Fin n → C) := eval m ⋙ powerMap (Fin m) (eval n) ⋙ uncurry (Fin m) (Fin n)
noncomputable def eval₃ (l m n:ℕ) : Diagram (Diagram (Diagram C (Fin (n+1))) (Fin (m+1)))
    (Fin (l+1)) ⥤ (Fin l × (Fin m × Fin n) → C) :=
  eval l ⋙ powerMap (Fin l) (eval₂ m n) ⋙ uncurry (Fin l) (Fin m × Fin n)
noncomputable instance (m n:ℕ) : (eval₂ (C:=C) m n).IsEquivalence := by
  dsimp [eval₂]; infer_instance
noncomputable instance (l m n:ℕ) : (eval₃ (C:=C) l m n).IsEquivalence := by
  dsimp [eval₃]; infer_instance
lemma eval₂_natural (F : C ⥤ D) [F.Braided] (m n:ℕ) :
    map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F) ⋙ eval₂ m n =
      eval₂ m n ⋙ powerMap (Fin m × Fin n) F := rfl
lemma eval₃_natural (F : C ⥤ D) [F.Braided] (l m n:ℕ) :
    map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F)) ⋙ eval₃ l m n =
      eval₃ l m n ⋙ powerMap (Fin l × (Fin m × Fin n)) F := rfl
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace ColimitTransfer

universe u v w z
variable {J : Type u} [Category.{v} J] {C : Type w} [Category.{z} C]
noncomputable def ofIsos {F G : J ⥤ C} (s : Cocone F) (t : Cocone G)
    (u : F ⟶ G) [IsIso u] (f : s.pt ⟶ t.pt) [IsIso f]
    (comm : ∀j,s.ι.app j ≫ f=u.app j ≫ t.ι.app j) (ht : IsColimit t) : IsColimit s := by
  let e := asIso u
  have hnat (j:J) : (((Cocone.precompose e.inv).obj s).ι.app j) ≫ f=t.ι.app j := by
    change ((inv u).app j ≫ s.ι.app j) ≫ f = _
    rw [Category.assoc,comm]
    simp
  exact (IsColimit.equivOfNatIsoOfIso e s t (Cocone.ext (asIso f) hnat)).symm ht
noncomputable abbrev H (q:ℕ) : Cat.{0,0} ⥤ ModuleCat ℤ :=
  nerveFunctor ⋙ SSet.homologyFunctor (ModuleCat.of ℤ ℤ) q
noncomputable def ofEquivalences {J : Type} [Category.{0} J] {F G : J ⥤ Cat.{0,0}}
    (s : Cocone F) (t : Cocone G) (u : F ⟶ G) (f : s.pt ⟶ t.pt)
    [∀j,(u.app j).toFunctor.IsEquivalence] [f.toFunctor.IsEquivalence]
    (comm : ∀j,s.ι.app j ≫ f=u.app j ≫ t.ι.app j) (q:ℕ)
    (ht : IsColimit ((H q).mapCocone t)) : IsColimit ((H q).mapCocone s) := by
  haveI (j:J) : IsIso ((Functor.whiskerRight u (H q)).app j) := by
    change IsIso (SSet.homologyMap (nerveMap (u.app j).toFunctor) (ModuleCat.of ℤ ℤ) q)
    infer_instance
  haveI : IsIso (Functor.whiskerRight u (H q)) := (NatTrans.isIso_iff_isIso_app _).mpr (fun _ => inferInstance)
  haveI : IsIso ((H q).map f) := by
    change IsIso (SSet.homologyMap (nerveMap f.toFunctor) (ModuleCat.of ℤ ℤ) q)
    infer_instance
  apply ofIsos ((H q).mapCocone s) ((H q).mapCocone t) (Functor.whiskerRight u (H q)) ((H q).map f) _ ht
  intro j
  exact (Functor.map_comp _ _ _).symm.trans ((congrArg (H q).map (comm j)).trans (Functor.map_comp _ _ _))
end ColimitTransfer

end OAI
