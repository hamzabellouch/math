import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageFiberSum
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleComposition

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open UniformObject

variable {a n : ℕ} {S T : Stage a n} (h : S≤T)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : Fin T.partition.size × Fin T.support.card)
    (hp : S.partition.color (T.partition.point c.1)=b.1)
    (hl : S.L b.2=T.L c.2)

noncomputable def refineFiber (U : S.Obj) : Fiber U b ≃ Fiber ((inclusion h).obj U) c where
  toFun x := ⟨⟨(x.val.val.1,T.partition.point c.1),
    (U.uniform x.val.val.1 x.val.val.2 (T.partition.point c.1) (by
      rw [x.property.1,S.partition.color_point,hp])).mp x.val.property⟩,rfl,
    x.property.2.trans hl⟩
  invFun y := ⟨⟨(y.val.val.1,S.partition.point b.1),
    (U.uniform y.val.val.1 y.val.val.2 (S.partition.point b.1) (by
      rw [y.property.1,hp,S.partition.color_point])).mp y.val.property⟩,rfl,
    y.property.2.trans hl.symm⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.property.1.symm
  right_inv y := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl y.property.1.symm

lemma refineFiber_natural {U V : S.Obj} (f : U ⟶ V) (x : Fiber U b) :
    refineFiber h b c hp hl V (fiberMap f b x)=
      fiberMap ((inclusion h).map f) c (refineFiber h b c hp hl U x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact f.uniform x.val (refineFiber h b c hp hl U x).val rfl (by
      change S.partition.color x.val.val.2=S.partition.color (T.partition.point c.1)
      rw [x.property.1,S.partition.color_point,hp])
  · exact (f.arrow.positional (refineFiber h b c hp hl U x).val).symm

noncomputable def refineEvaluationIso :
    evaluation (P:=S.partition) (L:=S.L) ⋙ BarFinitePower.project _ b ≅
      inclusion h ⋙ evaluation (P:=T.partition) (L:=T.L) ⋙ BarFinitePower.project _ c :=
  NatIso.ofComponents (fun U => asIso (C := FiniteSetGroupoid)
    (X := E.obj U b) (Y := E.obj ((inclusion h).obj U) c)
    (show (E.obj U b) ⟶ (E.obj ((inclusion h).obj U) c) from
    ((enumerate U b).symm.trans ((refineFiber h b c hp hl U).trans (enumerate ((inclusion h).obj U) c)))))
    (by
      intro U V f
      apply Equiv.ext
      intro x
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      dsimp only [Functor.comp_map,Pi.eval,BarFinitePower.project,asIso_hom,Equiv.trans_apply,Equiv.symm_apply_apply]
      change enumerate ((inclusion h).obj V) c (refineFiber h b c hp hl V
          ((enumerate V b).symm (E.map f b (enumerate U b x)))) =
        E.map ((inclusion h).map f) c (enumerate ((inclusion h).obj U) c
          (refineFiber h b c hp hl U ((enumerate U b).symm (enumerate U b x))))
      rw [E_map_enum,Equiv.symm_apply_apply,Equiv.symm_apply_apply,E_map_enum,refineFiber_natural])

lemma fiber_empty_of_new_label (hc : ∀j,S.L j ≠ T.L c.2) (U : S.Obj) :
    IsEmpty (Fiber ((inclusion h).obj U) c) := ⟨by
  intro x
  obtain ⟨j,hj⟩ := U.supported x.val.val.1
  exact hc j (hj.trans x.property.2)⟩

lemma new_label_size (hc : ∀j,S.L j ≠ T.L c.2) (U : S.Obj) :
    (evaluation.obj ((inclusion h).obj U) c).size=0 := by
  have := fiber_empty_of_new_label h c hc U
  exact Fintype.card_eq_zero
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
