import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageRefinement
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageMonoidal

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open UniformObject BarFinitePower

variable {a n : ℕ} {S T : Stage a n} (h : S≤T)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : Fin T.partition.size × Fin T.support.card)
    (hp : S.partition.color (T.partition.point c.1)=b.1)
    (hl : S.L b.2=T.L c.2)

lemma refineFiber_sum_inl (U V : S.Obj) (x : Fiber U b) :
    refineFiber h b c hp hl (UniformObject.sum U V) (fiberSum U V b (.inl x)) =
      fiberSum ((inclusion h).obj U) ((inclusion h).obj V) c
        (.inl (refineFiber h b c hp hl U x)) := rfl
lemma refineFiber_sum_inr (U V : S.Obj) (x : Fiber V b) :
    refineFiber h b c hp hl (UniformObject.sum U V) (fiberSum U V b (.inr x)) =
      fiberSum ((inclusion h).obj U) ((inclusion h).obj V) c
        (.inr (refineFiber h b c hp hl V x)) := rfl
lemma refineEvaluationIso_enum (U : S.Obj) (x : Fiber U b) :
    (refineEvaluationIso h b c hp hl).hom.app U (enumerate U b x) =
      enumerate ((inclusion h).obj U) c (refineFiber h b c hp hl U x) := by
  change enumerate ((inclusion h).obj U) c (refineFiber h b c hp hl U
    ((enumerate U b).symm (enumerate U b x)))=_
  rw [Equiv.symm_apply_apply]

instance refineEvaluationIso_monoidal : NatTrans.IsMonoidal (refineEvaluationIso h b c hp hl).hom where
  unit := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  tensor U V := by
    simp only [Functor.LaxMonoidal.comp_μ, inclusion_μ]
    change ((𝟙 _ ≫ mu U V b) ≫ _) = (_ ≫ (𝟙 _ ≫ mu ((inclusion h).obj U) ((inclusion h).obj V) c) ≫
      (E.map (𝟙 ((inclusion h).obj U ⊗ (inclusion h).obj V))) c)
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    apply Equiv.ext
    intro x
    change (refineEvaluationIso h b c hp hl).hom.app (UniformObject.sum U V) (mu U V b x) =
      mu ((inclusion h).obj U) ((inclusion h).obj V) c
        (FiniteSetGroupoid.sumHom ((refineEvaluationIso h b c hp hl).hom.app U)
          ((refineEvaluationIso h b c hp hl).hom.app V) x)
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      erw [mu_inl,refineEvaluationIso_enum,refineFiber_sum_inl,FiniteSetGroupoid.sumHom_inl,
        refineEvaluationIso_enum,mu_inl]
      rfl
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      erw [mu_inr,refineEvaluationIso_enum,refineFiber_sum_inr,FiniteSetGroupoid.sumHom_inr,
        refineEvaluationIso_enum,mu_inr]
      rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
namespace IntervalBar.Diagram

universe u v u' v' w
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
    {F G : C ⥤ D} [F.Braided] [G.Braided]
    {I : Type w} [Preorder I]
lemma monoidalNatTrans_eta (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    α.app (𝟙_ C) ≫ η G=η F := by
  apply (cancel_epi (ε F)).mp
  rw [←Category.assoc,NatTrans.IsMonoidal.unit,Functor.Monoidal.ε_η,Functor.Monoidal.ε_η]

noncomputable def mapNatTrans (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    map (I:=I) F ⟶ map G where
  app A := {
    app i j h := α.app (A.obj i j h)
    unit i := by
      change α.app _ ≫ (G.map (A.unit i).hom ≫ η G) = F.map (A.unit i).hom ≫ η F
      rw [←Category.assoc,←α.naturality,Category.assoc,monoidalNatTrans_eta]
    cut i j k hij hjk := by
      change (α.app _ ⊗ₘ α.app _) ≫ (μ G _ _ ≫ G.map (A.cut i j k hij hjk).hom)=
        (μ F _ _ ≫ F.map (A.cut i j k hij hjk).hom) ≫ α.app _
      rw [←Category.assoc,←NatTrans.IsMonoidal.tensor,Category.assoc,←α.naturality,Category.assoc] }
  naturality _ _ f := by
    apply Hom.ext
    intro i j h
    exact α.naturality (f.app i j h)

instance mapNatTrans_monoidal (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    NatTrans.IsMonoidal (mapNatTrans (I:=I) α) where
  unit := by
    apply Hom.ext
    intro i j h
    exact NatTrans.IsMonoidal.unit (τ:=α)
  tensor A B := by
    apply Hom.ext
    intro i j h
    exact NatTrans.IsMonoidal.tensor (τ:=α) _ _
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace NerveHomotopy
universe u v
variable {C D C' D' : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} C'] [Category.{v} D']
lemma functor_map_heq {H K : C ⥤ D} (h:H=K) {X Y:C} (f:X⟶Y) : HEq (H.map f) (K.map f) := by cases h; rfl
lemma comp_heq {X Y Z X' Y' Z' : D} (hX:X=X') (hY:Y=Y') (hZ:Z=Z')
    {f:X⟶Y} {g:Y⟶Z} {f':X'⟶Y'} {g':Y'⟶Z'} (hf:HEq f f') (hg:HEq g g') :
    HEq (f≫g) (f'≫g') := by subst X';subst Y';subst Z'; cases hf;cases hg;rfl
variable {F G : C ⥤ D} {F' G' : C' ⥤ D'}
variable (R:C⥤C') (S:D⥤D') (α:F⟶G) (α':F'⟶G')
    (eF:F⋙S=R⋙F') (eG:G⋙S=R⋙G')
    (eα:∀ X,HEq (S.map (α.app X)) (α'.app (R.obj X)))
include eF eG eα
lemma cylinder_natural : cylinder α ⋙ S = R.prod (𝟭 (Fin 2)) ⋙ cylinder α' := by
  apply CategoryTheory.Functor.hext
  · rintro ⟨X,i⟩
    fin_cases i
    · exact congrArg (fun H=>H.obj X) eF
    · exact congrArg (fun H=>H.obj X) eG
  · rintro ⟨X,i⟩ ⟨Y,j⟩ f
    have hij : i≤j := leOfHom f.2
    fin_cases i <;> fin_cases j
    · change HEq (S.map (F.map f.1 ≫ 𝟙 _)) (F'.map (R.map f.1) ≫ 𝟙 _)
      simp only [Category.comp_id]
      exact functor_map_heq eF f.1
    · change HEq (S.map (F.map f.1 ≫ α.app Y)) (F'.map (R.map f.1) ≫ α'.app (R.obj Y))
      rw [S.map_comp]
      exact comp_heq (congrArg (fun H=>H.obj X) eF) (congrArg (fun H=>H.obj Y) eF)
        (congrArg (fun H=>H.obj Y) eG) (functor_map_heq eF f.1) (eα Y)
    · simp at hij
    · change HEq (S.map (G.map f.1 ≫ 𝟙 _)) (G'.map (R.map f.1) ≫ 𝟙 _)
      simp only [Category.comp_id]
      exact functor_map_heq eG f.1
end NerveHomotopy

end

end

end OAI
