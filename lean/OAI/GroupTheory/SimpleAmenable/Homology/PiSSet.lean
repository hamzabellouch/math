import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageCoordinateMaps
import OAI.GroupTheory.SimpleAmenable.Homology.ConstantSplit

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet
open FreeChains

variable {ι:Type} (X:ι→SSet)
noncomputable def obj : SSet where
  obj p := ∀i,(X i).obj p
  map f := ↾fun s i=>(X i).map f (s i)
  map_id p := by apply ConcreteCategory.hom_ext; intro s; funext i; exact congrArg (fun f=>f (s i)) ((X i).map_id p)
  map_comp f g := by apply ConcreteCategory.hom_ext; intro s; funext i; exact congrArg (fun f=>f (s i)) ((X i).map_comp f g)
noncomputable def proj (i:ι) : obj X ⟶ X i where
  app _ := ↾fun s=>s i
  naturality _ _ _ := rfl
noncomputable def lift {Y:SSet} (f:∀i,Y⟶X i) : Y⟶obj X where
  app p := ↾fun s i=>(f i).app p s
  naturality p q g := by apply ConcreteCategory.hom_ext; intro s; funext i; exact congrArg (fun f=>f s) ((f i).naturality g)
@[simp] lemma lift_proj {Y:SSet} (f:∀i,Y⟶X i) (i:ι) : lift X f ≫ proj X i=f i := rfl
noncomputable def incl (x:∀i,(X i).obj (op ⦋0⦌)) (i:ι) : X i ⟶ obj X := by
  classical
  exact lift X (fun j=>if h:i=j then eqToHom (congrArg X h) else SSet.const (x j))
@[simp] lemma incl_self (x:∀i,(X i).obj (op ⦋0⦌)) (i:ι) : incl X x i ≫ proj X i=𝟙 _ := by
  classical
  simp [incl]
lemma incl_other (x:∀i,(X i).obj (op ⦋0⦌)) {i j:ι} (h:i≠j) :
    incl X x i ≫ proj X j=SSet.const (x j) := by
  classical
  simp [incl,h]
noncomputable def finSuccIso {n:ℕ} (X:Fin (n+1)→SSet) :
    obj X ≅ X 0 ⊗ obj (fun i:Fin n=>X i.succ) where
  hom := {app _ := ↾fun x=>(x 0,fun i=>x i.succ)
          naturality _ _ _ := rfl}
  inv := {app _ := ↾fun x=>Fin.cases x.1 x.2
          naturality _ _ _ := by
            apply ConcreteCategory.hom_ext; intro x; funext i
            cases i using Fin.cases <;> rfl}
  hom_inv_id := by
    apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i
    cases i using Fin.cases <;> rfl
  inv_hom_id := by ext p x <;> rfl
noncomputable def finZeroIso (X:Fin 0→SSet) : obj X ≅ ConnectedProduct.one where
  hom := { app _ := ↾fun _=>PUnit.unit
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun _ i=>Fin.elim0 i
           naturality _ _ _ := by apply ConcreteCategory.hom_ext; intro x; funext i; exact i.elim0 }
  hom_inv_id := by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i; exact i.elim0
  inv_hom_id := by ext p x; rfl
lemma fin_connected (n:ℕ) (X:Fin n→SSet) (hX:∀i,(X i).IsConnected) : (obj X).IsConnected := by
  induction n with
  | zero => exact BarFinitePower.connected_of_iso _ (finZeroIso X)
  | succ n ih =>
    have := hX 0
    have := ih (fun i=>X i.succ) (fun i=>hX i.succ)
    exact BarFinitePower.connected_of_iso _ (finSuccIso X)
@[simp] lemma finSucc_fst {n:ℕ} (X:Fin (n+1)→SSet) :
    (finSuccIso X).hom ≫ CartesianMonoidalCategory.fst _ _=proj X 0 := rfl
@[simp] lemma finSucc_snd {n:ℕ} (X:Fin (n+1)→SSet) (i:Fin n) :
    (finSuccIso X).hom ≫ CartesianMonoidalCategory.snd _ _ ≫ proj (fun j:Fin n=>X j.succ) i=proj X i.succ := rfl
lemma biprod_element_ext {M N:A} (a b:(M ⊞ N : A))
    (hf:(biprod.fst : M ⊞ N ⟶ M) a=(biprod.fst : M ⊞ N ⟶ M) b)
    (hs:(biprod.snd : M ⊞ N ⟶ N) a=(biprod.snd : M ⊞ N ⟶ N) b) : a=b := by
  have ha:=congrArg (fun f:(M ⊞ N)⟶(M ⊞ N)=>f a) (biprod.total (X:=M) (Y:=N))
  have hb:=congrArg (fun f:(M ⊞ N)⟶(M ⊞ N)=>f b) (biprod.total (X:=M) (Y:=N))
  change (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) a) +
    (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) a)=a at ha
  change (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) b) +
    (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) b)=b at hb
  rw [←ha,←hb,hf,hs]
lemma homology_ext (n:ℕ) (X:Fin n→SSet) (hX:∀i,(X i).IsConnected)
    (a b:((obj X).homology Z 1 : A)) (h:∀i,SSet.homologyMap (proj X i) Z 1 a=SSet.homologyMap (proj X i) Z 1 b) : a=b := by
  induction n with
  | zero =>
    have hz : IsZero ((obj X).homology Z 1) :=
      IsZero.of_iso (ConnectedProduct.one_homology_zero 1 (by decide))
        ((SSet.homologyFunctor Z 1).mapIso (finZeroIso X))
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Subsingleton.elim _ _
  | succ n ih =>
    have := hX 0
    have := fin_connected n (fun i=>X i.succ) (fun i=>hX i.succ)
    have := ConnectedProduct.projection_isIso_arbitrary (X 0) (obj (fun i:Fin n=>X i.succ))
      1 1 1 (by omega) (by omega) (by intros; omega) (by intros; omega)
    let e := (SSet.homologyFunctor Z 1).mapIso (finSuccIso X)
    apply e.toLinearEquiv.injective
    apply (ConcreteCategory.bijective_of_isIso (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1)).1
    apply biprod_element_ext
    · change (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1 ≫ biprod.fst) (e.hom a)=
        (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1 ≫ biprod.fst) (e.hom b)
      rw [ConnectedProduct.projection,biprod.lift_fst]
      change (SSet.homologyMap (finSuccIso X).hom Z 1 ≫
        SSet.homologyMap (CartesianMonoidalCategory.fst _ _) Z 1) a =
        (SSet.homologyMap (finSuccIso X).hom Z 1 ≫
        SSet.homologyMap (CartesianMonoidalCategory.fst _ _) Z 1) b
      rw [←SSet.homologyMap_comp,finSucc_fst]
      exact h 0
    · change (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1 ≫ biprod.snd) (e.hom a)=
        (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1 ≫ biprod.snd) (e.hom b)
      rw [ConnectedProduct.projection,biprod.lift_snd]
      apply ih (fun i=>X i.succ) (fun i=>hX i.succ)
      intro i
      change (SSet.homologyMap (finSuccIso X).hom Z 1 ≫
        SSet.homologyMap (CartesianMonoidalCategory.snd _ _) Z 1 ≫
        SSet.homologyMap (proj (fun i:Fin n=>X i.succ) i) Z 1) a =
        (SSet.homologyMap (finSuccIso X).hom Z 1 ≫
        SSet.homologyMap (CartesianMonoidalCategory.snd _ _) Z 1 ≫
        SSet.homologyMap (proj (fun i:Fin n=>X i.succ) i) Z 1) b
      rw [←SSet.homologyMap_comp,←SSet.homologyMap_comp,finSucc_snd]
      exact h i.succ
noncomputable def homologyPi {n:ℕ} (X:Fin n→SSet) : A := by
  letI : Module ℤ (∀i,((X i).homology Z 1 : A)) := Pi.module _ _ ℤ
  exact ModuleCat.of ℤ (∀i,((X i).homology Z 1 : A))
noncomputable def homologyProj (n:ℕ) (X:Fin n→SSet) :
    (obj X).homology Z 1 ⟶ homologyPi X := by
  letI : Module ℤ (∀i,((X i).homology Z 1 : A)) := Pi.module _ _ ℤ
  exact ModuleCat.ofHom (LinearMap.pi (fun i=>(SSet.homologyMap (proj X i) Z 1).hom))
lemma homologyProj_isIso (n:ℕ) (X:Fin n→SSet) (hX:∀i,(X i).IsConnected) : IsIso (homologyProj n X) := by
  classical
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b h
    apply homology_ext n X hX a b
    intro i
    exact congrFun h i
  · let x : ∀i,(X i).obj (op ⦋0⦌) := fun i=>by
      haveI:=hX i
      exact Classical.arbitrary _
    intro a
    refine ⟨∑ i:Fin n,SSet.homologyMap (incl X x i) Z 1 (a i),?_⟩
    funext j
    change SSet.homologyMap (proj X j) Z 1 (∑ i:Fin n,SSet.homologyMap (incl X x i) Z 1 (a i))=a j
    rw [map_sum]
    rw [Finset.sum_eq_single j]
    · simp only [←ModuleCat.comp_apply,←SSet.homologyMap_comp,incl_self,SSet.homologyMap_id,ModuleCat.id_apply]
    · intro i hi hij
      rw [←ModuleCat.comp_apply,←SSet.homologyMap_comp,incl_other X x hij,
        ConnectedProduct.const_homology_zero _ 1 (by decide)]
      rfl
    · simp
end PiSSet

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentTranslation
open FreeChains

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
abbrev P (C:Type) [Category.{0} C] := Skeleton C
noncomputable def repr (p:P C) : C := (fromSkeleton C).obj p
omit [MonoidalCategory C] [SymmetricCategory C] in
@[simp] lemma repr_component (p:P C) : toSkeleton (repr p)=p := toSkeleton_fromSkeleton_obj p
abbrev property (p:P C) : ObjectProperty C := fun U=>toSkeleton U=p
abbrev Fiber (p:P C) := (property p).FullSubcategory
noncomputable def reprMul (r s:P C) : repr r ⊗ repr s ≅ repr (r*s) :=
  Skeleton.isoOfEq (by simp [Skeleton.toSkeleton_tensorObj])
noncomputable def reprOne : repr (1:P C) ≅ 𝟙_ C :=
  Skeleton.isoOfEq (by simp [Skeleton.one_eq])
noncomputable def translate (r p q:P C) (h:r*p=q) : Fiber p ⥤ Fiber q :=
  (property q).lift ((property p).ι ⋙ tensorLeft (repr r)) (fun U=>by
    change toSkeleton (repr r ⊗ U.obj)=q
    rw [Skeleton.toSkeleton_tensorObj,repr_component,U.property,h])
noncomputable def translateOne (p:P C) (h:(1:P C)*p=p) : translate 1 p p h ⟶ 𝟭 (Fiber p) := by
  let α : tensorLeft (repr (1:P C)) ⟶ 𝟭 C :=
    (tensoringLeft C).map (reprOne (C:=C)).hom ≫ (leftUnitorNatIso C).hom
  exact { app U := ObjectProperty.homMk (α.app U.obj)
          naturality U V f := by apply ObjectProperty.hom_ext; exact α.naturality f.hom }
noncomputable def translateComp {p q t:P C} (r s:P C) (h:r*p=q) (k:s*q=t)
    (l:(s*r)*p=t) : translate (s*r) p t l ⟶ translate r p q h ⋙ translate s q t k := by
  let α : tensorLeft (repr (s*r)) ⟶ tensorLeft (repr r) ⋙ tensorLeft (repr s) :=
    (tensoringLeft C).map (reprMul s r).inv ≫ (tensorLeftTensor (repr s) (repr r)).hom
  exact { app U := ObjectProperty.homMk (α.app U.obj)
          naturality U V f := by apply ObjectProperty.hom_ext; exact α.naturality f.hom }
omit [SymmetricCategory C] in
lemma homology_one (p:P C) (h:(1:P C)*p=p) (j:ℕ) :
    SSet.homologyMap (nerveMap (translate 1 p p h)) Z j=𝟙 _ := by
  have h:=(NerveHomotopy.ofNatTrans (translateOne p h)).congr_homologyMap Z j
  change SSet.homologyMap (nerveMap (translate 1 p p _)) Z j=SSet.homologyMap (𝟙 _) Z j at h
  simpa only [SSet.homologyMap_id] using h
omit [SymmetricCategory C] in
lemma homology_comp {p q t:P C} (r s:P C) (h:r*p=q) (k:s*q=t) (l:(s*r)*p=t) (j:ℕ) :
    SSet.homologyMap (nerveMap (translate (s*r) p t l)) Z j =
      SSet.homologyMap (nerveMap (translate r p q h)) Z j ≫
      SSet.homologyMap (nerveMap (translate s q t k)) Z j := by
  have hh:=(NerveHomotopy.ofNatTrans (translateComp r s h k l)).congr_homologyMap Z j
  change SSet.homologyMap (nerveMap (translate (s*r) p t l)) Z j =
    SSet.homologyMap (nerveMap (translate r p q h) ≫ nerveMap (translate s q t k)) Z j at hh
  simpa only [SSet.homologyMap_comp] using hh
noncomputable def homologyDiagram (j:ℕ) : ActionCategory (P C) (P C) ⥤ A where
  obj p := (nerve (Fiber p.back)).homology Z j
  map {p q} f := SSet.homologyMap (nerveMap (translate f.hom p.back q.back f.map_val)) Z j
  map_id p := homology_one p.back _ j
  map_comp f g := homology_comp (f.hom:P C) (g.hom:P C) f.map_val g.map_val _ j
end ComponentTranslation

end

end OAI
