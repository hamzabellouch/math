import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalFunctor
import OAI.GroupTheory.SimpleAmenable.Configurations.TrajectoryStages
import OAI.GroupTheory.SimpleAmenable.Simplicial.UniformMonoidal

namespace OAI

section

section
open CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

namespace BooleanPartition
variable {a : ℕ}
def Refines (P Q : BooleanPartition a) : Prop :=
  ∀x y,Q.color x=Q.color y → P.color x=P.color y
lemma refines_refl (P : BooleanPartition a) : Refines P P := fun _ _ h => h
lemma refines_trans {P Q T : BooleanPartition a} (h : Refines P Q) (k : Refines Q T) :
    Refines P T := fun x y e => h x y (k x y e)
noncomputable def join (P Q : BooleanPartition a) : BooleanPartition a :=
  generated (Sum.elim P.cell Q.cell)
lemma le_join_left (P Q : BooleanPartition a) : Refines P (join P Q) := by
  intro x y h
  have e := generated_constant (Sum.elim P.cell Q.cell) h (Sum.inl (P.color x))
  exact ((e.mp rfl).symm)
lemma le_join_right (P Q : BooleanPartition a) : Refines Q (join P Q) := by
  intro x y h
  have e := generated_constant (Sum.elim P.cell Q.cell) h (Sum.inr (Q.color x))
  exact ((e.mp rfl).symm)
end BooleanPartition
namespace LabelledStage
abbrev ReducedLabel (n : ℕ) := {l : Fin n → CutRing × CutRing // ∀i,orbitRepresentative (l i)=l i}
structure Stage (a n : ℕ) where
  partition : BooleanPartition a
  support : Finset (ReducedLabel n)
namespace Stage
variable {a n : ℕ}
noncomputable def empty : Stage a n := ⟨BooleanPartition.generated (fun x : Fin 0 => Fin.elim0 x),∅⟩
instance : Nonempty (Stage a n) := ⟨empty⟩
noncomputable instance : Preorder (Stage a n) where
  le S T := S.partition.Refines T.partition ∧ S.support ⊆ T.support
  le_refl S := ⟨BooleanPartition.refines_refl _,Subset.rfl⟩
  le_trans S T U h k := ⟨BooleanPartition.refines_trans h.1 k.1,Subset.trans h.2 k.2⟩
noncomputable def sup (S T : Stage a n) : Stage a n :=
  ⟨S.partition.join T.partition,S.support ∪ T.support⟩
lemma le_sup_left (S T : Stage a n) : S ≤ sup S T :=
  ⟨BooleanPartition.le_join_left _ _,Finset.subset_union_left⟩
lemma le_sup_right (S T : Stage a n) : T ≤ sup S T :=
  ⟨BooleanPartition.le_join_right _ _,Finset.subset_union_right⟩
noncomputable instance : IsDirectedOrder (Stage a n) where
  directed S T := ⟨sup S T,le_sup_left S T,le_sup_right S T⟩
noncomputable instance : IsFiltered (Stage a n) := inferInstance
noncomputable abbrev L (S : Stage a n) : Fin S.support.card → Fin n → CutRing × CutRing :=
  fun i => ((Fintype.equivFin S.support).symm (Fin.cast (by simp) i)).val.val
lemma L_reduced (S : Stage a n) : ∀j i,orbitRepresentative (S.L j i)=S.L j i :=
  fun j => ((Fintype.equivFin S.support).symm (Fin.cast (by simp) j)).val.property
lemma L_injective (S : Stage a n) : Function.Injective S.L := by
  intro i j h
  have h' := (Fintype.equivFin S.support).symm.injective (Subtype.ext (Subtype.ext h))
  exact Fin.ext (show i.val=j.val from congrArg (fun x : Fin (Fintype.card S.support) => x.val) h')
lemma label_mem (S : Stage a n) (l : Fin n → CutRing × CutRing) (hl : ∀i,orbitRepresentative (l i)=l i) :
    (∃j,S.L j=l) ↔ (⟨l,hl⟩ : ReducedLabel n)∈S.support := by
  constructor
  · rintro ⟨j,hj⟩
    have hm := ((Fintype.equivFin S.support).symm (Fin.cast (by simp) j)).property
    convert hm using 1
    exact Subtype.ext hj.symm
  · intro h
    refine ⟨Fin.cast (by simp) (Fintype.equivFin S.support ⟨⟨l,hl⟩,h⟩),?_⟩
    simp [L]
noncomputable abbrev Obj (S : Stage a n) := UniformObject S.partition S.L
noncomputable def inclusion {S T : Stage a n} (h : S≤T) : S.Obj ⥤ T.Obj where
  obj U := {
    obj := U.obj
    uniform := fun j x y hxy => U.uniform j x y (h.1 x y hxy)
    supported := fun j => (label_mem T _ (U.obj.reduced j)).mpr
      (h.2 ((label_mem S _ (U.obj.reduced j)).mp (U.supported j))) }
  map f := ⟨f.arrow,fun x y hxy hP => f.uniform x y hxy (h.1 _ _ hP)⟩
  map_id _ := rfl
  map_comp _ _ := rfl
lemma inclusion_id (S : Stage a n) : inclusion (le_refl S)=𝟭 S.Obj := by
  refine CategoryTheory.Functor.ext (fun U => ?_) ?_
  · cases U; rfl
  · intro X Y f; rfl
lemma inclusion_comp {S T U : Stage a n} (h : S≤T) (k : T≤U) :
    inclusion (h.trans k)=inclusion h ⋙ inclusion k := by
  refine CategoryTheory.Functor.ext (fun X => ?_) ?_
  · cases X; rfl
  · intro X Y f; rfl
noncomputable def diagram : Stage a n ⥤ Cat.{0,0} where
  obj S := Cat.of S.Obj
  map h := (inclusion (leOfHom h)).toCatHom
  map_id S := by apply Cat.ext; exact inclusion_id S
  map_comp h k := by apply Cat.ext; exact inclusion_comp (leOfHom h) (leOfHom k)
end Stage
end LabelledStage
end SimpleAmenable.PolygonObject

end

section
open CategoryTheory Classical Set MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage

namespace Stage
variable {a n : ℕ}
noncomputable abbrev forget (S : Stage a n) : S.Obj ⥤ Labelled a n := UniformObject.forget
@[simp] lemma forget_ε (S : Stage a n) : Functor.LaxMonoidal.ε S.forget=𝟙 _ := rfl
@[simp] lemma forget_η (S : Stage a n) : Functor.OplaxMonoidal.η S.forget=𝟙 _ := rfl
@[simp] lemma forget_μ (S : Stage a n) (U V : S.Obj) : Functor.LaxMonoidal.μ S.forget U V=𝟙 _ := rfl
lemma forget_injective (S : Stage a n) : Function.Injective S.forget.obj := by
  intro U V h; cases U; cases V; cases h; rfl
lemma inclusion_forget {S T : Stage a n} (h : S≤T) : inclusion h ⋙ T.forget=S.forget := rfl
noncomputable def cocone : CategoryTheory.Limits.Cocone (diagram (a:=a) (n:=n)) where
  pt := Cat.of (Labelled a n)
  ι := {
    app S := S.forget.toCatHom
    naturality S T h := by apply Cat.ext; exact inclusion_forget (leOfHom h) }

theorem exists_lift_family {κ τ : Type} [Fintype κ] [Fintype τ]
    (U : κ → Labelled a n) (src dst : τ → κ) (f : ∀t,U (src t) ⟶ U (dst t)) :
    ∃S : Stage a n, (∀k,Labelled.ObjectUniform S.partition (U k)) ∧
      (∀k j,∃l,S.L l=(U k).label j) ∧ (∀t,Labelled.ArrowUniform S.partition (f t)) := by
  obtain ⟨P,hP,hf⟩ := Labelled.exists_uniform_partition U src dst f
  let lab : (Σk,Fin (U k).polygon.tracks) → ReducedLabel n := fun kj =>
    ⟨(U kj.1).label kj.2,(U kj.1).reduced kj.2⟩
  let S : Stage a n := ⟨P,Finset.univ.image lab⟩
  refine ⟨S,hP,?_,hf⟩
  intro k j
  apply (label_mem S _ ((U k).reduced j)).mpr
  exact Finset.mem_image.mpr ⟨⟨k,j⟩,Finset.mem_univ _,rfl⟩

theorem exists_lift {I : Type} [Category.{0} I] [Finite I] [∀i j:I,Finite (i ⟶ j)]
    (F : I ⥤ Labelled a n) : ∃S : Stage a n, ∃G : I ⥤ S.Obj,G ⋙ S.forget=F := by
  let : Fintype I := Fintype.ofFinite I
  let (i j : I) : Fintype (i ⟶ j) := Fintype.ofFinite (i ⟶ j)
  let Ar := Σi:I,Σj:I,i ⟶ j
  let u : Ar → I := fun t => t.1
  let v : Ar → I := fun t => t.2.1
  let f : ∀t:Ar,F.obj (u t) ⟶ F.obj (v t) := fun t => F.map t.2.2
  obtain ⟨S,hP,hL,hf⟩ := exists_lift_family F.obj u v f
  let G : I ⥤ S.Obj := {
    obj i := ⟨F.obj i,hP i,hL i⟩
    map g := ⟨F.map g,hf ⟨_,_,g⟩⟩
    map_id i := UniformObject.Hom.ext _ _ (F.map_id i)
    map_comp g h := UniformObject.Hom.ext _ _ (F.map_comp g h) }
  exact ⟨S,G,rfl⟩

open IntervalBar IntervalBar.Diagram
variable {I : Type} [Preorder I] (S : Stage a n) (A : Diagram (Labelled a n) I)
variable (hP : ∀i j h,Labelled.ObjectUniform S.partition (A.obj i j h))
    (hL : ∀i j h t,∃l,S.L l=(A.obj i j h).label t)
    (hU : ∀i,Labelled.ArrowUniform S.partition (A.unit i).hom)
    (hC : ∀i j k hij hjk,Labelled.ArrowUniform S.partition (A.cut i j k hij hjk).hom)
noncomputable def liftDiagram : Diagram S.Obj I where
  obj i j h := ⟨A.obj i j h,hP i j h,hL i j h⟩
  unit i := asIso (show (⟨A.obj i i le_rfl,hP i i _,hL i i _⟩ : S.Obj) ⟶ 𝟙_ S.Obj from
    ⟨(A.unit i).hom,hU i⟩)
  cut i j k hij hjk := asIso (show
    (⟨A.obj i j hij,hP i j hij,hL i j hij⟩ : S.Obj) ⊗ ⟨A.obj j k hjk,hP j k hjk,hL j k hjk⟩ ⟶
      ⟨A.obj i k (hij.trans hjk),hP i k _,hL i k _⟩ from ⟨(A.cut i j k hij hjk).hom,hC i j k hij hjk⟩)
  left_unit i j h := UniformObject.Hom.ext _ _ (A.left_unit i j h)
  right_unit i j h := UniformObject.Hom.ext _ _ (A.right_unit i j h)
  associativity i j k l hij hjk hkl := UniformObject.Hom.ext _ _ (A.associativity i j k l hij hjk hkl)
lemma liftDiagram_map :
    (Diagram.map S.forget).obj (liftDiagram S A hP hL hU hC)=A := by
  refine ext_heq rfl ?_ ?_
  · apply heq_of_eq; funext i
    apply Iso.ext
    simp [liftDiagram]
    rfl
  · apply heq_of_eq; funext i j k hij hjk
    apply Iso.ext
    simp [liftDiagram]
    rfl
end Stage
end SimpleAmenable.PolygonObject.LabelledStage

end

end

end OAI
