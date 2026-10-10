import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleReindex
import OAI.GroupTheory.SimpleAmenable.Configurations.EmptyStage
import OAI.GroupTheory.SimpleAmenable.Simplicial.FiberSum

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace BarFiberProduct

universe homSource homTarget
variable {A C D:Type} [Category.{homSource} A] [Category.{homTarget} C]
  [Category.{homTarget} D]
  [MonoidalCategory A] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory A] [BraidedCategory C] [BraidedCategory D]
noncomputable instance prodFunctorBraided (F:A⥤C) (G:A⥤D) [F.Braided] [G.Braided] :
    (F.prod' G).Braided where
  braided X Y := by
    apply CategoryTheory.Prod.hom_ext
    · simp only [CategoryTheory.prod_comp_fst,Functor.prod'_μ_fst]
      change Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
        (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X
      exact Functor.Braided.braided (F:=F) X Y
    · simp only [CategoryTheory.prod_comp_snd,Functor.prod'_μ_snd]
      change Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
        (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X
      exact Functor.Braided.braided (F:=G) X Y
end BarFiberProduct
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar₃Map_id_homology (j:ℕ) :
    SSet.homologyMap (bar₃Map (𝟭 C)) DiagonalResolution.Z j=𝟙 _ := by
  have := bar₃Map_homology_isIso (𝟭 C) j
  apply (cancel_epi (SSet.homologyMap (bar₃Map (𝟭 C)) DiagonalResolution.Z j)).mp
  rw [Category.comp_id,← SSet.homologyMap_comp,←bar₃Map_comp]
  exact bar₃Map_eq_of_monoidalNatTrans (Functor.leftUnitor (𝟭 C)).hom j
end IntervalBar.Diagram
namespace SimpleAmenable.PolygonObject.FiniteSetGroupoid
open BarFiberProduct IntervalBar.Diagram BarFinitePower
open LabelledStage.Stage

noncomputable def merge : (Bool → FiniteSetGroupoid) ⥤ FiniteSetGroupoid :=
  (project Bool true).prod' (project Bool false) ⋙ tensor FiniteSetGroupoid
noncomputable instance : merge.Braided := by unfold merge; infer_instance
noncomputable def selected (b k:Bool) : FiniteSetGroupoid ⥤ FiniteSetGroupoid :=
  match b,k with
  | false,false => 𝟭 _
  | true,true => 𝟭 _
  | _,_ => terminal.{0} ⋙ emptyFunctor.{0}
noncomputable instance selectedMonoidal (b k:Bool) : (selected b k).Monoidal := by
  cases b <;> cases k <;> unfold selected <;> infer_instance
noncomputable instance selectedBraided (b k:Bool) : (selected b k).Braided := by
  cases b <;> cases k <;> unfold selected <;> infer_instance
noncomputable def insertFiber (b:Bool) : FiniteSetGroupoid ⥤ (Bool→FiniteSetGroupoid) :=
  Functor.pi' (selected b)
noncomputable instance (b:Bool) : (insertFiber b).Braided := by unfold insertFiber; infer_instance
noncomputable def insertCoordinate (b k:Bool) : insertFiber b ⋙ project Bool k ≅ selected b k := Iso.refl _
noncomputable instance (b k:Bool) : NatTrans.IsMonoidal (insertCoordinate b k).hom where
  unit := by
    simp [insertCoordinate,insertFiber,project,toEquiv]
    cases b <;> cases k <;> rfl
  tensor U V := by
    change Functor.LaxMonoidal.μ (selected b k) U V ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ Functor.LaxMonoidal.μ (selected b k) U V
    rw [id_tensorHom_id,Category.comp_id,Category.id_comp]
lemma selected_homology (b k:Bool) (j:ℕ) (hj:0<j) :
    SSet.homologyMap (bar₃Map (selected b k)) DiagonalResolution.Z j =
      if b=k then 𝟙 _ else 0 := by
  cases b <;> cases k
  · exact bar₃Map_id_homology j
  · change SSet.homologyMap (bar₃Map (terminal.{0} ⋙ emptyFunctor.{0})) DiagonalResolution.Z j=0
    rw [bar₃Map_comp,SSet.homologyMap_comp]
    have hz := bar₃_acyclic (C:=Terminal.{0}) (fun x y => ⟨eqToHom (Subsingleton.elim x y)⟩) j hj
    rw [hz.eq_of_src (SSet.homologyMap (bar₃Map emptyFunctor.{0}) DiagonalResolution.Z j) 0,comp_zero]
  · change SSet.homologyMap (bar₃Map (terminal.{0} ⋙ emptyFunctor.{0})) DiagonalResolution.Z j=0
    rw [bar₃Map_comp,SSet.homologyMap_comp]
    have hz := bar₃_acyclic (C:=Terminal.{0}) (fun x y => ⟨eqToHom (Subsingleton.elim x y)⟩) j hj
    rw [hz.eq_of_src (SSet.homologyMap (bar₃Map emptyFunctor.{0}) DiagonalResolution.Z j) 0,comp_zero]
  · exact bar₃Map_id_homology j
noncomputable def mergeInsertIso (b:Bool) : insertFiber b ⋙ merge ≅ 𝟭 FiniteSetGroupoid := by
  cases b
  · exact NatIso.ofComponents (fun U => asIso (C := FiniteSetGroupoid)
      (X := sum empty U) (Y := U) (left U)) (by
      intro U V f
      change sumHom (𝟙 empty) f ≫ left V = left U ≫ f
      exact (leftUnitor_naturality f))
  · exact NatIso.ofComponents (fun U => asIso (C := FiniteSetGroupoid)
      (X := sum U empty) (Y := U) (right U)) (by
      intro U V f
      change sumHom f (𝟙 empty) ≫ right V = right U ≫ f
      exact (rightUnitor_naturality f))
lemma merge_μ (U V:Bool→FiniteSetGroupoid) :
    Functor.LaxMonoidal.μ merge U V=tensorμ (U true) (U false) (V true) (V false) := by
  unfold merge
  rw [Functor.LaxMonoidal.comp_μ]
  change tensorμ (U true) (U false) (V true) (V false) ≫
      sumHom (Functor.LaxMonoidal.μ ((project Bool true).prod' (project Bool false)) U V).1
        (Functor.LaxMonoidal.μ ((project Bool true).prod' (project Bool false)) U V).2 = _
  rw [Functor.prod'_μ_fst,Functor.prod'_μ_snd]
  change tensorμ (U true) (U false) (V true) (V false) ≫ sumHom (𝟙 _) (𝟙 _) = _
  rw [sumHom_id]
  apply Equiv.ext; intro x; rfl
lemma mergeInsert_false_μ (U V:FiniteSetGroupoid) :
    Functor.LaxMonoidal.μ (insertFiber false ⋙ merge) U V = tensorμ empty U empty V := by
  rw [Functor.LaxMonoidal.comp_μ,merge_μ]
  change tensorμ _ _ _ _ ≫ sumHom (𝟙 _) (𝟙 _) = _
  rw [sumHom_id]
  apply Equiv.ext; intro x; rfl
lemma mergeInsert_true_μ (U V:FiniteSetGroupoid) :
    Functor.LaxMonoidal.μ (insertFiber true ⋙ merge) U V = tensorμ U empty V empty := by
  rw [Functor.LaxMonoidal.comp_μ,merge_μ]
  change tensorμ _ _ _ _ ≫ sumHom (𝟙 _) (𝟙 _) = _
  rw [sumHom_id]
  apply Equiv.ext; intro x; rfl
noncomputable instance mergeInsertMonoidal (b:Bool) : NatTrans.IsMonoidal (mergeInsertIso b).hom where
  unit := by cases b <;> apply Equiv.ext <;> intro x <;> exact Fin.elim0 x
  tensor U V := by
    cases b
    · rw [mergeInsert_false_μ]
      change tensorμ empty U empty V ≫ left (sum U V) = sumHom (left U) (left V) ≫ 𝟙 _
      rw [Category.comp_id,tensorμ_eq]
      dsimp only [CategoryStruct.comp,instGroupoid,toEquiv]
      apply Equiv.ext; intro x
      obtain ⟨z,rfl⟩ := (sumEquiv (sum empty U) (sum empty V)).surjective x
      cases z with
      | inl z =>
        obtain ⟨t,rfl⟩ := (sumEquiv empty U).surjective z
        cases t with
        | inl t => exact Fin.elim0 t
        | inr t =>
          simp [toEquiv,sumHom,assoc,swap,left,inv_eq,Equiv.trans_apply,MonoidalCategory.tensorObj]
          dsimp only [sum,empty]
          rw [Equiv.symm_apply_apply]
          rfl
      | inr z =>
        obtain ⟨t,rfl⟩ := (sumEquiv empty V).surjective z
        cases t with
        | inl t => exact Fin.elim0 t
        | inr t =>
          simp [toEquiv,sumHom,assoc,swap,left,inv_eq,Equiv.trans_apply,MonoidalCategory.tensorObj]
          dsimp only [sum,empty]
          rw [Equiv.symm_apply_apply]
          rfl
    · rw [mergeInsert_true_μ]
      change tensorμ U empty V empty ≫ right (sum U V) = sumHom (right U) (right V) ≫ 𝟙 _
      rw [Category.comp_id,tensorμ_eq]
      dsimp only [CategoryStruct.comp,instGroupoid,toEquiv]
      apply Equiv.ext; intro x
      obtain ⟨z,rfl⟩ := (sumEquiv (sum U empty) (sum V empty)).surjective x
      cases z with
      | inl z =>
        obtain ⟨t,rfl⟩ := (sumEquiv U empty).surjective z
        cases t with
        | inr t => exact Fin.elim0 t
        | inl t =>
          simp [toEquiv,sumHom,assoc,swap,right,inv_eq,Equiv.trans_apply,MonoidalCategory.tensorObj]
          dsimp only [sum,empty]
          rw [Equiv.symm_apply_apply]
          rfl
      | inr z =>
        obtain ⟨t,rfl⟩ := (sumEquiv V empty).surjective z
        cases t with
        | inr t => exact Fin.elim0 t
        | inl t =>
          simp [toEquiv,sumHom,assoc,swap,right,inv_eq,Equiv.trans_apply,MonoidalCategory.tensorObj]
          dsimp only [sum,empty]
          rw [Equiv.symm_apply_apply]
          rfl
end SimpleAmenable.PolygonObject.FiniteSetGroupoid

end OAI
