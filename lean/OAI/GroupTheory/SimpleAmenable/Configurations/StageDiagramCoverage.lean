import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageOrder

namespace OAI

section

section
open CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram

variable {a n : ℕ} {I : Type} [Preorder I] [Fintype I]
private abbrev Interval := {t : I×I // t.1≤t.2}
private abbrev Triple := {t : I×I×I // t.1≤t.2.1 ∧ t.2.1≤t.2.2}

lemma exists_lift_diagram (A : Diagram (Labelled a n) I) :
    ∃S : Stage a n, ∃B : Diagram S.Obj I,(Diagram.map S.forget).obj B=A := by
  let κ := Interval (I:=I) ⊕ (Unit ⊕ Triple (I:=I))
  let τ := I ⊕ Triple (I:=I)
  let U : κ → Labelled a n := Sum.elim
    (fun q => A.obj q.val.1 q.val.2 q.property)
    (Sum.elim (fun _ => 𝟙_ (Labelled a n))
      (fun q => A.obj q.val.1 q.val.2.1 q.property.1 ⊗ A.obj q.val.2.1 q.val.2.2 q.property.2))
  let src : τ → κ := Sum.elim (fun i => .inl ⟨(i,i),le_rfl⟩) (fun t => .inr (.inr t))
  let dst : τ → κ := Sum.elim (fun _ => .inr (.inl ()))
    (fun t => .inl ⟨(t.val.1,t.val.2.2),t.property.1.trans t.property.2⟩)
  let f : ∀t,U (src t) ⟶ U (dst t) := Sum.rec (fun i => (A.unit i).hom)
    (fun q => (A.cut q.val.1 q.val.2.1 q.val.2.2 q.property.1 q.property.2).hom)
  obtain ⟨S,hP,hL,hf⟩ := exists_lift_family U src dst f
  let hP' := fun i j h => hP (.inl ⟨(i,j),h⟩)
  let hL' := fun i j h => hL (.inl ⟨(i,j),h⟩)
  let hU := fun i => hf (.inl i)
  let hC := fun i j k hij hjk => hf (.inr ⟨(i,j,k),hij,hjk⟩)
  exact ⟨S,liftDiagram S A hP' hL' hU hC,liftDiagram_map S A hP' hL' hU hC⟩

noncomputable def liftDiagramHom (S : Stage a n) {A B : Diagram (Labelled a n) I}
    (hPA : ∀i j h,Labelled.ObjectUniform S.partition (A.obj i j h))
    (hLA : ∀i j h t,∃l,S.L l=(A.obj i j h).label t)
    (hUA : ∀i,Labelled.ArrowUniform S.partition (A.unit i).hom)
    (hCA : ∀i j k hij hjk,Labelled.ArrowUniform S.partition (A.cut i j k hij hjk).hom)
    (hPB : ∀i j h,Labelled.ObjectUniform S.partition (B.obj i j h))
    (hLB : ∀i j h t,∃l,S.L l=(B.obj i j h).label t)
    (hUB : ∀i,Labelled.ArrowUniform S.partition (B.unit i).hom)
    (hCB : ∀i j k hij hjk,Labelled.ArrowUniform S.partition (B.cut i j k hij hjk).hom)
    (f : A ⟶ B) (hf : ∀i j h,Labelled.ArrowUniform S.partition (f.app i j h)) :
    liftDiagram S A hPA hLA hUA hCA ⟶ liftDiagram S B hPB hLB hUB hCB where
  app i j h := ⟨f.app i j h,hf i j h⟩
  unit i := UniformObject.Hom.ext _ _ (f.unit i)
  cut i j k hij hjk := UniformObject.Hom.ext _ _ (f.cut i j k hij hjk)

theorem exists_lift_diagram_family {K : Type} [Category.{0} K] [Fintype K]
    [∀i j:K,Fintype (i ⟶ j)] (F : K ⥤ Diagram (Labelled a n) I) :
    ∃S : Stage a n,∃G : K ⥤ Diagram S.Obj I,G ⋙ Diagram.map S.forget=F := by
  let V := K × (Interval (I:=I) ⊕ (Unit ⊕ Triple (I:=I)))
  let Arr := (K × (I ⊕ Triple (I:=I))) ⊕ ((Σk:K,Σl:K,k ⟶ l) × Interval (I:=I))
  let U : V → Labelled a n := fun v => Sum.elim
    (fun q => (F.obj v.1).obj q.val.1 q.val.2 q.property)
    (Sum.elim (fun _ => 𝟙_ (Labelled a n))
      (fun q => (F.obj v.1).obj q.val.1 q.val.2.1 q.property.1 ⊗
        (F.obj v.1).obj q.val.2.1 q.val.2.2 q.property.2)) v.2
  let src : Arr → V := Sum.elim
    (fun v => (v.1,Sum.elim (fun i => .inl ⟨(i,i),le_rfl⟩) (fun t => .inr (.inr t)) v.2))
    (fun v => (v.1.1,.inl v.2))
  let dst : Arr → V := Sum.elim
    (fun v => (v.1,Sum.elim (fun _ => .inr (.inl ()))
      (fun t => .inl ⟨(t.val.1,t.val.2.2),t.property.1.trans t.property.2⟩) v.2))
    (fun v => (v.1.2.1,.inl v.2))
  let f : ∀t,U (src t) ⟶ U (dst t) := by
    intro t
    rcases t with ⟨k,i|q⟩ | v
    · exact ((F.obj k).unit i).hom
    · exact ((F.obj k).cut q.val.1 q.val.2.1 q.val.2.2 q.property.1 q.property.2).hom
    · exact (F.map v.1.2.2).app v.2.val.1 v.2.val.2 v.2.property
  obtain ⟨S,hP,hL,hf⟩ := exists_lift_family U src dst f
  let p := fun k i j h => hP (k,.inl ⟨(i,j),h⟩)
  let l := fun k i j h => hL (k,.inl ⟨(i,j),h⟩)
  let u := fun k i => hf (.inl (k,.inl i))
  let c := fun k i j z hij hjz => hf (.inl (k,.inr ⟨(i,j,z),hij,hjz⟩))
  let G : K ⥤ Diagram S.Obj I := {
    obj k := liftDiagram S (F.obj k) (p k) (l k) (u k) (c k)
    map {k z} g := liftDiagramHom S (p k) (l k) (u k) (c k) (p z) (l z) (u z) (c z)
      (F.map g) (fun i j h => hf (.inr (⟨k,z,g⟩,⟨(i,j),h⟩)))
    map_id k := by
      apply Hom.ext; intro i j h
      apply UniformObject.Hom.ext
      change (F.map (𝟙 k)).app i j h=𝟙 _
      rw [F.map_id]; rfl
    map_comp g h := by
      apply Hom.ext; intro i j hij
      apply UniformObject.Hom.ext
      change (F.map (g≫h)).app i j hij=(F.map g).app i j hij≫(F.map h).app i j hij
      rw [F.map_comp]; rfl }
  refine ⟨S,G,?_⟩
  refine CategoryTheory.Functor.ext (fun k => liftDiagram_map S (F.obj k) (p k) (l k) (u k) (c k)) ?_
  intro k z g
  apply Hom.ext; intro i j h
  simp only [Functor.comp_map, comp_app, Diagram.eqToHom_app]
  change (F.map g).app i j h = 𝟙 _ ≫ (F.map g).app i j h ≫ 𝟙 _
  simp
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
