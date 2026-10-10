import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageFiberSum
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleComposition
import OAI.GroupTheory.SimpleAmenable.Configurations.EmptyStage
import OAI.GroupTheory.SimpleAmenable.Configurations.PointFiberEvaluation
import OAI.GroupTheory.SimpleAmenable.Configurations.CellFunctor
import OAI.GroupTheory.SimpleAmenable.Simplicial.CellMonoidal
import OAI.GroupTheory.SimpleAmenable.Simplicial.PointFiberMonoidal
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageMonoidal

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.Cell
open BarFinitePower

variable {a n : ℕ} (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n)
variable (c : GenericSquare a × (Fin n → CutRing × CutRing))
variable (hp : c.1∈P.val) (hl : l.val=c.2)
noncomputable def fiber (U : FiniteSetGroupoid) :
    Fin U.size ≃ PointFiber.Fiber (object P l U) c where
  toFun i := ⟨⟨(i,c.1),hp⟩,rfl,hl⟩
  invFun y := y.val.val.1
  left_inv _ := rfl
  right_inv y := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl y.property.1.symm
lemma fiber_natural {U V : FiniteSetGroupoid} (f : U ⟶ V) (x : Fin U.size) :
    fiber P l c hp hl V (f x)=
      PointFiber.fiberMap (arrow P l f) c (fiber P l c hp hl U x) := rfl
noncomputable def evaluationIso :
    𝟭 FiniteSetGroupoid ≅ functor P l ⋙ PointFiber.evaluation ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (X := U) (Y := PointFiber.E.obj (object P l U) c)
    ((fiber P l c hp hl U).trans (PointFiber.enumerate (object P l U) c))) (by
      intro U V f
      apply Equiv.ext; intro x
      change PointFiber.enumerate (object P l V) c (fiber P l c hp hl V (f x)) =
        PointFiber.E.map (arrow P l f) c (PointFiber.enumerate (object P l U) c
          (fiber P l c hp hl U x))
      rw [PointFiber.E_map_enum,fiber_natural])
lemma evaluationIso_apply (U : FiniteSetGroupoid) (x : Fin U.size) :
    (evaluationIso P l c hp hl).hom.app U x =
      PointFiber.enumerate (object P l U) c (fiber P l c hp hl U x) := rfl
lemma fiber_sum_left (U V : FiniteSetGroupoid) (x : Fin U.size) :
    PointFiber.fiberMap (tensorArrow P l U V) c
      (PointFiber.fiberSum (object P l U) (object P l V) c (.inl (fiber P l c hp hl U x))) =
      fiber P l c hp hl (U⊗V) (FiniteSetGroupoid.sumEquiv U V (.inl x)) := rfl
lemma fiber_sum_right (U V : FiniteSetGroupoid) (x : Fin V.size) :
    PointFiber.fiberMap (tensorArrow P l U V) c
      (PointFiber.fiberSum (object P l U) (object P l V) c (.inr (fiber P l c hp hl V x))) =
      fiber P l c hp hl (U⊗V) (FiniteSetGroupoid.sumEquiv U V (.inr x)) := rfl
noncomputable instance evaluationIsoMonoidal : NatTrans.IsMonoidal (evaluationIso P l c hp hl).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor U V := by
    apply Equiv.ext; intro x
    change (evaluationIso P l c hp hl).hom.app (U⊗V) x =
      PointFiber.E.map (tensorArrow P l U V) c
        (PointFiber.mu (object P l U) (object P l V) c
          (FiniteSetGroupoid.sumHom ((evaluationIso P l c hp hl).hom.app U)
            ((evaluationIso P l c hp hl).hom.app V) x))
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv U V).surjective x
    cases x with
    | inl x => erw [FiniteSetGroupoid.sumHom_inl,evaluationIso_apply,PointFiber.mu_inl,
        PointFiber.E_map_enum,fiber_sum_left,evaluationIso_apply]
    | inr x => erw [FiniteSetGroupoid.sumHom_inr,evaluationIso_apply,PointFiber.mu_inr,
        PointFiber.E_map_enum,fiber_sum_right,evaluationIso_apply]

variable {hp hl}
lemma fiber_empty (h : ¬(c.1∈P.val ∧ l.val=c.2)) (U : FiniteSetGroupoid) :
    IsEmpty (PointFiber.Fiber (object P l U) c) := ⟨fun x => h
      ⟨x.property.1 ▸ x.val.property,x.property.2⟩⟩
lemma empty_size (h : ¬(c.1∈P.val ∧ l.val=c.2)) (U : FiniteSetGroupoid) :
    (PointFiber.E.obj (object P l U) c).size=0 := by
  have := fiber_empty P l c h U
  exact @Fintype.card_eq_zero _ (PointFiber.instFintypeFiber (object P l U) c) _
noncomputable def emptyIso (h : ¬(c.1∈P.val ∧ l.val=c.2)) :
    FiniteSetGroupoid.terminal ⋙ FiniteSetGroupoid.emptyFunctor ≅
      functor P l ⋙ PointFiber.evaluation ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (X := FiniteSetGroupoid.empty)
    (Y := PointFiber.E.obj (object P l U) c) (finCongr (empty_size P l c h U).symm)) (by
      intros; apply Equiv.ext; intro x; exact Fin.elim0 x)
noncomputable instance emptyIsoMonoidal (h : ¬(c.1∈P.val ∧ l.val=c.2)) :
    NatTrans.IsMonoidal (emptyIso P l c h).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor _ _ := by apply Equiv.ext; intro x; exact Fin.elim0 x
end SimpleAmenable.PolygonObject.Labelled.Cell

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open UniformObject BarFinitePower

variable {a n : ℕ} (S : Stage a n)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : GenericSquare a × (Fin n → CutRing × CutRing))
    (hp : S.partition.color c.1=b.1) (hl : S.L b.2=c.2)

noncomputable def pointFiber (U : S.Obj) :
    UniformObject.Fiber U b ≃ Labelled.PointFiber.Fiber U.obj c where
  toFun x := ⟨⟨(x.val.val.1,c.1),
    (U.uniform x.val.val.1 x.val.val.2 c.1 (by
      rw [x.property.1,S.partition.color_point,hp])).mp x.val.property⟩,rfl,
    x.property.2.trans hl⟩
  invFun y := ⟨⟨(y.val.val.1,S.partition.point b.1),
    (U.uniform y.val.val.1 y.val.val.2 (S.partition.point b.1) (by
      rw [y.property.1,hp,S.partition.color_point])).mp y.val.property⟩,rfl,
    y.property.2.trans hl.symm⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.property.1.symm
  right_inv y := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl y.property.1.symm

lemma pointFiber_natural {U V : S.Obj} (f : U ⟶ V) (x : Fiber U b) :
    pointFiber S b c hp hl V (fiberMap f b x)=
      Labelled.PointFiber.fiberMap f.arrow c (pointFiber S b c hp hl U x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact f.uniform x.val (pointFiber S b c hp hl U x).val rfl (by
      change S.partition.color x.val.val.2=S.partition.color c.1
      rw [x.property.1,S.partition.color_point,hp])
  · exact (f.arrow.positional (pointFiber S b c hp hl U x).val).symm

noncomputable def pointEvaluationIso :
    evaluation (P:=S.partition) (L:=S.L) ⋙ project _ b ≅
      S.forget ⋙ Labelled.PointFiber.evaluation ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (X := UniformObject.E.obj U b)
    (Y := Labelled.PointFiber.E.obj U.obj c)
    ((enumerate U b).symm.trans ((pointFiber S b c hp hl U).trans
      (Labelled.PointFiber.enumerate U.obj c)))) (by
      intro U V f
      apply Equiv.ext
      intro x
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      dsimp only [Functor.comp_map,Pi.eval,project,asIso_hom,Equiv.trans_apply,Equiv.symm_apply_apply]
      change Labelled.PointFiber.enumerate V.obj c (pointFiber S b c hp hl V
          ((enumerate V b).symm (UniformObject.E.map f b (enumerate U b x)))) =
        Labelled.PointFiber.E.map f.arrow c (Labelled.PointFiber.enumerate U.obj c
          (pointFiber S b c hp hl U ((enumerate U b).symm (enumerate U b x))))
      rw [E_map_enum,Equiv.symm_apply_apply,Equiv.symm_apply_apply,
        Labelled.PointFiber.E_map_enum,pointFiber_natural])

lemma pointFiber_sum_inl (U V : S.Obj) (x : Fiber U b) :
    pointFiber S b c hp hl (UniformObject.sum U V) (fiberSum U V b (.inl x)) =
      Labelled.PointFiber.fiberSum U.obj V.obj c (.inl (pointFiber S b c hp hl U x)) := rfl
lemma pointFiber_sum_inr (U V : S.Obj) (x : Fiber V b) :
    pointFiber S b c hp hl (UniformObject.sum U V) (fiberSum U V b (.inr x)) =
      Labelled.PointFiber.fiberSum U.obj V.obj c (.inr (pointFiber S b c hp hl V x)) := rfl
lemma pointEvaluationIso_enum (U : S.Obj) (x : Fiber U b) :
    (pointEvaluationIso S b c hp hl).hom.app U (enumerate U b x) =
      Labelled.PointFiber.enumerate U.obj c (pointFiber S b c hp hl U x) := by
  change Labelled.PointFiber.enumerate U.obj c (pointFiber S b c hp hl U
    ((enumerate U b).symm (enumerate U b x)))=_
  rw [Equiv.symm_apply_apply]

instance pointEvaluationIso_monoidal : NatTrans.IsMonoidal (pointEvaluationIso S b c hp hl).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor U V := by
    change ((𝟙 _ ≫ mu U V b) ≫ _) = (_ ≫ (𝟙 _ ≫ Labelled.PointFiber.mu U.obj V.obj c) ≫
      (Labelled.PointFiber.E.map (𝟙 (U.obj ⊗ V.obj))) c)
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    apply Equiv.ext
    intro x
    change (pointEvaluationIso S b c hp hl).hom.app (UniformObject.sum U V) (mu U V b x) =
      Labelled.PointFiber.mu U.obj V.obj c
        (FiniteSetGroupoid.sumHom ((pointEvaluationIso S b c hp hl).hom.app U)
          ((pointEvaluationIso S b c hp hl).hom.app V) x)
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (UniformObject.E.obj U b) (UniformObject.E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      erw [mu_inl,pointEvaluationIso_enum,pointFiber_sum_inl,FiniteSetGroupoid.sumHom_inl,
        pointEvaluationIso_enum,Labelled.PointFiber.mu_inl]
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      erw [mu_inr,pointEvaluationIso_enum,pointFiber_sum_inr,FiniteSetGroupoid.sumHom_inr,
        pointEvaluationIso_enum,Labelled.PointFiber.mu_inr]

variable {S b hp hl}
lemma pointFiber_empty_of_new_label (hc : ∀j,S.L j ≠ c.2) (U : S.Obj) :
    IsEmpty (Labelled.PointFiber.Fiber U.obj c) := ⟨by
  intro x
  obtain ⟨j,hj⟩ := U.supported x.val.val.1
  exact hc j (hj.trans x.property.2)⟩
lemma point_new_label_size (hc : ∀j,S.L j ≠ c.2) (U : S.Obj) :
    (Labelled.PointFiber.E.obj U.obj c).size=0 := by
  have := pointFiber_empty_of_new_label c hc U
  exact Fintype.card_eq_zero
noncomputable def emptyPointIso (hc : ∀j,S.L j ≠ c.2) :
    FiniteSetGroupoid.terminal ⋙ FiniteSetGroupoid.emptyFunctor ≅
      S.forget ⋙ Labelled.PointFiber.evaluation ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (X := FiniteSetGroupoid.empty)
    (Y := Labelled.PointFiber.E.obj U.obj c) (finCongr (point_new_label_size c hc U).symm)) (by
      intros; apply Equiv.ext; intro x; exact Fin.elim0 x)
noncomputable instance emptyPointIsoMonoidal (hc : ∀j,S.L j ≠ c.2) :
    NatTrans.IsMonoidal (emptyPointIso c hc).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor _ _ := by apply Equiv.ext; intro x; exact Fin.elim0 x

end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end OAI
