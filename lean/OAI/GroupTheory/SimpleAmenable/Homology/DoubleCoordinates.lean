import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.PiH1Coproduct
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalBinary
import OAI.GroupTheory.SimpleAmenable.Homology.ComponentStable
import OAI.GroupTheory.SimpleAmenable.Homology.RegularBlock

namespace OAI

namespace DoubleCoordinates
variable {P:Type} {n:ℕ}
abbrev Index (P:Type) (n:ℕ) := Σhv:{hv:ℕ×ℕ // hv.1+hv.2=n},(Fin hv.val.2→P) × P × (Fin hv.val.1→P)
def toSplit (s:Index P n) : MarkedCoordinates.Split P n :=
  ⟨⟨s.1.val.2,by have:=s.1.property; omega⟩,s.2.1,s.2.2.1,
    fun j=>s.2.2.2 ⟨j.val,by have:=s.1.property; dsimp at *; omega⟩⟩
def ofSplit (s:MarkedCoordinates.Split P n) : Index P n :=
  ⟨⟨(n-s.1.val,s.1.val),by omega⟩,s.2.1,s.2.2.1,s.2.2.2⟩
lemma payload_heq {m n v:ℕ} (e:m=n) (y:Fin v→P) (p:P) (x:Fin n→P)
    (hp:∀j:Fin m,j.val<n) : HEq (y,p,fun j:Fin m=>x ⟨j.val,hp j⟩) (y,p,x) := by
  subst n
  rfl
lemma left_inv (s:Index P n) : ofSplit (toSplit s)=s := by
  rcases s with ⟨⟨⟨h,v⟩,hn⟩,y,p,x⟩
  subst n
  change Fin v→P at y
  change Fin h→P at x
  dsimp [toSplit,ofSplit]
  apply Sigma.ext
  · exact Subtype.ext (Prod.ext (Nat.add_sub_cancel h v) rfl)
  · exact payload_heq (Nat.add_sub_cancel h v) y p x _
lemma right_inv (s:MarkedCoordinates.Split P n) : toSplit (ofSplit s)=s := by
  rcases s with ⟨i,y,p,x⟩
  rfl
noncomputable def equiv (P:Type) (n:ℕ) : Index P n ≃ MarkedCoordinates.Split P n where
  toFun:=toSplit
  invFun:=ofSplit
  left_inv:=left_inv
  right_inv:=right_inv
noncomputable def words (P:Type) (n:ℕ) : Index P n ≃ (Σ_:Fin (n+1),Fin (n+1)→P) :=
  (equiv P n).trans (MarkedCoordinates.equiv P n)
lemma center (s:Index P n) : (words P n s).2 (words P n s).1=s.2.2.1 :=
  MarkedCoordinates.word_center _ _ _ _
end DoubleCoordinates

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularLabels
open FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
noncomputable def totalInj {n:ℕ} (s:DoubleCoordinates.Index P n) :
    fiber F s.2.2.1 ⟶ ((RegularCoefficient.double F).total c).X n :=
  inj F s.2 ≫ (RegularCoefficient.double F).ιTotal c s.1.val.1 s.1.val.2 n s.1.property
noncomputable def totalDesc {n:ℕ} {M:A}
    (f:∀s:DoubleCoordinates.Index P n,fiber F s.2.2.1 ⟶ M) :
    ((RegularCoefficient.double F).total c).X n ⟶ M :=
  (RegularCoefficient.double F).totalDesc (fun h v hn=>desc F (fun w=>f ⟨⟨(h,v),hn⟩,w⟩))
@[reassoc (attr:=simp)] lemma totalInj_desc {n:ℕ} {M:A}
    (f:∀s:DoubleCoordinates.Index P n,fiber F s.2.2.1 ⟶ M) (s:DoubleCoordinates.Index P n) :
    totalInj F s ≫ totalDesc F f=f s := by
  dsimp only [totalInj,totalDesc]
  rw [Category.assoc,HomologicalComplex₂.ι_totalDesc,include_desc]
lemma total_hom_ext {n:ℕ} {M:A} {f g:((RegularCoefficient.double F).total c).X n ⟶ M}
    (hh:∀s:DoubleCoordinates.Index P n,totalInj F s ≫ f=totalInj F s ≫ g) : f=g := by
  apply HomologicalComplex₂.total.hom_ext
  intro h v hn
  apply hom_ext F
  intro w
  exact (Category.assoc _ _ _).symm.trans ((hh ⟨⟨(h,v),hn⟩,w⟩).trans (Category.assoc _ _ _))
noncomputable def totalIsColimit (n:ℕ) : IsColimit (Cofan.mk _ (totalInj F (n:=n))) :=
  Cofan.IsColimit.mk _ (fun s=>totalDesc F s.inj) (fun _ _=>totalInj_desc F _ _)
    (fun s _ hh=>total_hom_ext F (fun w=>(hh w).trans (totalInj_desc F s.inj w).symm))
end RegularLabels

end

namespace MarkedH1

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def wordInclude {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) : Fiber (p i) ⥤ (Fin n→C) := by
  classical
  exact Functor.pi' (fun j=>if i=j then (property (p i)).ι else (Functor.const _).obj (repr (p j)))
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma wordInclude_nerve {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    nerveMap (wordInclude p i) ≫ (PiSSet.nervePiIso (fun _:Fin n=>C)).hom =
      PiSSet.incl (fun j=>nerve (Fiber (p j))) (points p) i ≫ PiFiber.inclusion C (Fin n) p := by
  classical
  apply NatTrans.ext; funext d
  apply ConcreteCategory.hom_ext; intro s
  funext j
  change (s ⋙ wordInclude p i ⋙ Pi.eval _ j) =
    ((PiSSet.incl (fun j=>nerve (Fiber (p j))) (points p) i ≫ PiSSet.proj _ j ≫
      nerveMap (property (p j)).ι).app d s)
  dsimp only [wordInclude]
  rw [Functor.pi'_eval]
  by_cases h:i=j
  · subst j
    rw [ite_eq_left rfl, ←Category.assoc, PiSSet.incl_self]
    rfl
  · rw [ite_eq_right h, ←Category.assoc, PiSSet.incl_other _ _ h, SSet.const_comp]
    rfl
noncomputable def wordDiagram {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    Fiber (p i) ⥤ IntervalBar.Diagram C (Fin (n+1)) :=
  wordInclude p i ⋙ (IntervalBar.Diagram.eval (C:=C) n).asEquivalence.inverse
omit [SymmetricCategory C] in
lemma primitive_eq {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    primitive p i=SSet.homologyMap (nerveMap (wordDiagram p i)) Z 1 := by
  have:=NerveHomotopy.homologyMap_isIso ((IntervalBar.Diagram.eval (C:=C) n).asEquivalence.functor) Z 1
  apply (cancel_mono (evalIso (C:=C) n).hom).mp
  dsimp only [primitive]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [←SSet.homologyMap_comp,←wordInclude_nerve]
  erw [SSet.homologyMap_comp]
  dsimp only [wordDiagram,evalIso,Iso.trans_hom,Functor.mapIso_hom,asIso_hom]
  have h:=(NerveHomotopy.ofNatTrans
    (Functor.isoWhiskerLeft (wordInclude p i) (IntervalBar.Diagram.eval (C:=C) n).asEquivalence.counitIso).hom).congr_homologyMap Z 1
  have hh : SSet.homologyMap (nerveMap (wordDiagram p i)) Z 1 ≫
      SSet.homologyMap (nerveMap (IntervalBar.Diagram.eval (C:=C) n)) Z 1 =
        SSet.homologyMap (nerveMap (wordInclude p i)) Z 1 := by
    rw [←SSet.homologyMap_comp]
    exact h
  change SSet.homologyMap (nerveMap (wordInclude p i)) Z 1 ≫ _ =
    SSet.homologyMap (nerveMap (wordDiagram p i)) Z 1 ≫
      SSet.homologyMap (nerveMap (IntervalBar.Diagram.eval (C:=C) n)) Z 1 ≫ _
  rw [←Category.assoc,hh]
  rfl
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma wordInclude_proj {n:ℕ} (p:Fin n→Skeleton C) (i j:Fin n) :
    wordInclude p i ⋙ Pi.eval (fun _:Fin n=>C) j =
      if i=j then (property (p i)).ι else (Functor.const _).obj (repr (p j)) := by
  classical
  exact Functor.pi'_eval _ _
noncomputable def oneIncludeIso (p:Fin 1→Skeleton C) :
    wordDiagram p 0 ⋙ oneEval ≅ (property (p 0)).ι := by
  classical
  change (wordInclude p 0 ⋙ (eval 1).asEquivalence.inverse) ⋙
    (eval 1 ⋙ Pi.eval (fun _:Fin 1=>C) 0) ≅ _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (wordInclude p 0)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (eval 1).asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _) ≪≫
    eqToIso (by rw [wordInclude_proj,ite_eq_left rfl])
noncomputable def binaryLeft (p:Fin 2→Skeleton C) :
    wordInclude p 0 ⋙ tensorPair ≅ (property (p 0)).ι ⋙ tensorRight (repr (p 1)) := by
  classical
  apply eqToIso
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro object
    simp [wordInclude, tensorPair, tensorRight, Functor.pi']
  · intro source target morphism
    simp [wordInclude, tensorPair, tensorRight, Functor.pi']
    change morphism.hom ▷ repr (p 1) = 𝟙 _ ≫ morphism.hom ▷ repr (p 1)
    exact (Category.id_comp _).symm
noncomputable def binaryRight (p:Fin 2→Skeleton C) :
    wordInclude p 1 ⋙ tensorPair ≅ (property (p 1)).ι ⋙ tensorLeft (repr (p 0)) := by
  classical
  apply eqToIso
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro object
    simp [wordInclude, tensorPair, tensorLeft, Functor.pi']
  · intro source target morphism
    simp [wordInclude, tensorPair, tensorLeft, Functor.pi']
    change repr (p 0) ◁ morphism.hom = 𝟙 _ ≫ repr (p 0) ◁ morphism.hom
    exact (Category.id_comp _).symm
noncomputable def binaryLeftTranslate (p:Fin 2→Skeleton C) :
    wordInclude p 0 ⋙ tensorPair ≅
      translate (p 1) (p 0) (p 1*p 0) rfl ⋙ (property (p 1*p 0)).ι :=
  binaryLeft p ≪≫ Functor.isoWhiskerLeft (property (p 0)).ι
    (BraidedCategory.tensorLeftIsoTensorRight (repr (p 1))).symm
noncomputable def binaryRightTranslate (p:Fin 2→Skeleton C) :
    wordInclude p 1 ⋙ tensorPair ≅
      translate (p 0) (p 1) (p 0*p 1) rfl ⋙ (property (p 0*p 1)).ι := binaryRight p
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_face (p:Fin 2→Skeleton C) (i:Fin 2) (k:Fin 3) :
    primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ k).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 =
        SSet.homologyMap (nerveMap (wordInclude p i ⋙ binaryFace k)) Z 1 := by
  rw [primitive_eq]
  change SSet.homologyMap (nerveMap (wordDiagram p i)) Z 1 ≫
    SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ k).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 =
    SSet.homologyMap (nerveMap (wordDiagram p i) ≫
      nerveMap (reindex (SimplexCategory.δ k).toOrderHom) ≫ nerveMap oneEval) Z 1
  simp only [SSet.homologyMap_comp]
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_zero (p:Fin 2→Skeleton C) :
    primitive p 1 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1=ComponentStable.inclusion (p 1) 1 := by
  rw [binary_primitive_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceZero (C:=C))).hom).congr_homologyMap Z 1
  rw [h]
  rw [wordInclude_proj,ite_eq_left rfl]
  rfl
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_last (p:Fin 2→Skeleton C) :
    primitive p 0 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1=ComponentStable.inclusion (p 0) 1 := by
  rw [binary_primitive_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 0) (binaryFaceLast (C:=C))).hom).congr_homologyMap Z 1
  rw [h]
  rw [wordInclude_proj,ite_eq_left rfl]
  rfl
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_zero_other (p:Fin 2→Skeleton C) :
    primitive p 0 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1=0 := by
  rw [binary_primitive_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 0) (binaryFaceZero (C:=C))).hom).congr_homologyMap Z 1
  rw [h,wordInclude_proj,ite_eq_right (by decide)]
  have hc : nerveMap ((Functor.const (Fiber (p 0))).obj (repr (p 1))) =
      SSet.const (nerveEquiv.symm (repr (p 1))) := by ext n x; rfl
  rw [hc]
  exact ConnectedProduct.const_homology_zero _ 1 (by decide)
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_last_other (p:Fin 2→Skeleton C) :
    primitive p 1 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1=0 := by
  rw [binary_primitive_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceLast (C:=C))).hom).congr_homologyMap Z 1
  rw [h,wordInclude_proj,ite_eq_right (by decide)]
  have hc : nerveMap ((Functor.const (Fiber (p 1))).obj (repr (p 0))) =
      SSet.const (nerveEquiv.symm (repr (p 0))) := by ext n x; rfl
  rw [hc]
  exact ConnectedProduct.const_homology_zero _ 1 (by decide)
lemma binary_primitive_middle_stable (p:Fin 2→Skeleton C) (i:Fin 2) :
    primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 =
        ComponentStable.inclusion (p i) 1 ≫ ComponentStable.toStable 1 := by
  rw [binary_primitive_face_assoc]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p i) (binaryFaceMiddle (C:=C))).hom).congr_homologyMap Z 1
  rw [h]
  fin_cases i
  · change SSet.homologyMap (nerveMap (wordInclude p 0 ⋙ tensorPair)) Z 1 ≫ ComponentStable.toStable 1 =
      ComponentStable.inclusion (p 0) 1 ≫ ComponentStable.toStable 1
    have ht:=(NerveHomotopy.ofNatTrans (binaryLeftTranslate p).hom).congr_homologyMap Z 1
    rw [ht]
    change SSet.homologyMap (nerveMap (translate (p 1) (p 0) (p 1*p 0) rfl) ≫
      nerveMap (property (p 1*p 0)).ι) Z 1 ≫ _ = _
    rw [SSet.homologyMap_comp,Category.assoc]
    exact ComponentStable.translate_toStable _ _ _ rfl 1
  · change SSet.homologyMap (nerveMap (wordInclude p 1 ⋙ tensorPair)) Z 1 ≫ ComponentStable.toStable 1 =
      ComponentStable.inclusion (p 1) 1 ≫ ComponentStable.toStable 1
    have ht:=(NerveHomotopy.ofNatTrans (binaryRightTranslate p).hom).congr_homologyMap Z 1
    rw [ht]
    change SSet.homologyMap (nerveMap (translate (p 0) (p 1) (p 0*p 1) rfl) ≫
      nerveMap (property (p 0*p 1)).ι) Z 1 ≫ _ = _
    rw [SSet.homologyMap_comp,Category.assoc]
    exact ComponentStable.translate_toStable _ _ _ rfl 1
end

end MarkedH1

end OAI
