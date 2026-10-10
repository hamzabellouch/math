import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.DoubleCoordinates

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def interval {n:ℕ} (i j:Fin (n+1)) (h:i≤j) : Diagram C (Fin (n+1)) ⥤ C where
  obj D := D.obj i j h
  map f := f.app i j h
noncomputable def pairAt {n:ℕ} (i j:Fin n) : (Fin n→C) ⥤ C where
  obj X := X i ⊗ X j
  map f := f i ⊗ₘ f j
  map_id X := by simp
  map_comp f g := by simp [tensorHom_comp_tensorHom]
lemma interval_congr {n:ℕ} {i j i' j':Fin (n+1)} {h:i≤j} {h':i'≤j'} (hi:i=i') (hj:j=j') :
    interval (C:=C) i j h=interval i' j' h' := by subst i'; subst j'; rfl
noncomputable def faceEdge {n:ℕ} (k:Fin (n+2)) (j:Fin n) : (Fin (n+1)→C) ⥤ C :=
  if j.val+1<k.val then Pi.eval _ j.castSucc else
  if j.val+1=k.val then pairAt j.castSucc j.succ else Pi.eval _ j.succ
lemma faceEdge_left {n:ℕ} (k:Fin (n+2)) (j:Fin n) (h:j.val+1<k.val) :
    reindex (C:=C) (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j =
      eval (n+1) ⋙ Pi.eval _ j.castSucc := by
  apply interval_congr
  · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val<k.val; omega)
  · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val+1<k.val; exact h)
lemma faceEdge_right {n:ℕ} (k:Fin (n+2)) (j:Fin n) (h:k.val≤j.val) :
    reindex (C:=C) (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j =
      eval (n+1) ⋙ Pi.eval _ j.succ := by
  apply interval_congr
  · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val≤j.val; exact h)
  · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val≤j.val+1; omega)
noncomputable def faceEdge_middle {n:ℕ} (k:Fin (n+2)) (j:Fin n) (h:j.val+1=k.val) :
    eval (C:=C) (n+1) ⋙ pairAt j.castSucc j.succ ≅
      reindex (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j := by
  have he:reindex (C:=C) (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j =
      interval j.castSucc.castSucc j.succ.succ (by change j.val≤j.val+2; omega) := by
    apply interval_congr
    · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val<k.val; omega)
    · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val≤j.val+1; omega)
  let e : eval (C:=C) (n+1) ⋙ pairAt j.castSucc j.succ ≅
      interval j.castSucc.castSucc j.succ.succ (by change j.val≤j.val+2; omega) :=
    NatIso.ofComponents (fun D=>D.cut j.castSucc.castSucc j.succ.castSucc j.succ.succ
      (Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ _)) (Fin.castSucc_le_succ _))
        (by intro D E f; exact f.cut _ _ _ _ _)
  exact e ≪≫ (eqToIso he).symm
noncomputable def faceEdgeIso {n:ℕ} (k:Fin (n+2)) (j:Fin n) :
    eval (C:=C) (n+1) ⋙ faceEdge k j ≅
      reindex (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j := by
  dsimp only [faceEdge]
  split_ifs with h h'
  · exact (eqToIso (faceEdge_left k j h)).symm
  · exact faceEdge_middle k j h'
  · exact (eqToIso (faceEdge_right k j (by omega))).symm
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace NerveHomology
open FreeChains

variable {C D E:Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
noncomputable abbrev map (F:C⥤D) (q:ℕ) := SSet.homologyMap (nerveMap F) Z q
lemma comp (F:C⥤D) (G:D⥤E) (q:ℕ) : map (F⋙G) q=map F q ≫ map G q := by
  change SSet.homologyMap (nerveMap F ≫ nerveMap G) Z q=_
  rw [SSet.homologyMap_comp]
lemma iso {F G:C⥤D} (e:F≅G) (q:ℕ) : map F q=map G q :=
  (NerveHomotopy.ofNatTrans e.hom).congr_homologyMap Z q
lemma const (U:D) (q:ℕ) (hq:q≠0) : map ((Functor.const C).obj U) q=0 := by
  have h : nerveMap ((Functor.const C).obj U)=SSet.const (nerveEquiv.symm U) := by ext n x; rfl
  rw [map,h]
  exact ConnectedProduct.const_homology_zero (X:=nerve C) (Y:=nerve D) (nerveEquiv.symm U) q hq
end NerveHomology
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram NerveHomology

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
@[reassoc] lemma primitive_eval {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    primitive p i ≫ NerveHomology.map (eval n) 1=NerveHomology.map (wordInclude p i) 1 := by
  rw [primitive_eq,←NerveHomology.comp]
  exact NerveHomology.iso (Functor.isoWhiskerLeft (wordInclude p i) (eval n).asEquivalence.counitIso) 1
omit [SymmetricCategory C] in
lemma recognition {D:Type} [Category.{0} D] {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n)
    (F:D⥤IntervalBar.Diagram C (Fin (n+1))) (T:D⥤Fiber (p i))
    (e:F⋙eval n≅T⋙wordInclude p i) :
    NerveHomology.map F 1=NerveHomology.map T 1 ≫ primitive p i := by
  have := NerveHomotopy.homologyMap_isIso (eval (C:=C) n) Z 1
  apply (cancel_mono (NerveHomology.map (eval n) 1)).mp
  rw [Category.assoc,primitive_eval,←NerveHomology.comp,←NerveHomology.comp]
  exact NerveHomology.iso e 1
omit [SymmetricCategory C] in
lemma recognition_const {D:Type} [Category.{0} D] {n:ℕ} (F:D⥤IntervalBar.Diagram C (Fin (n+1)))
    (U:Fin n→C) (e:F⋙eval n≅(Functor.const D).obj U) : NerveHomology.map F 1=0 := by
  have := NerveHomotopy.homologyMap_isIso (eval (C:=C) n) Z 1
  apply (cancel_mono (NerveHomology.map (eval n) 1)).mp
  rw [zero_comp,←NerveHomology.comp,NerveHomology.iso e 1]
  exact NerveHomology.const U 1 (by decide)
noncomputable def wordDiagram_eval {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    wordDiagram p i ⋙ eval n ≅ wordInclude p i :=
  Functor.isoWhiskerLeft (wordInclude p i) (eval n).asEquivalence.counitIso
noncomputable def primitiveFace_eval {n:ℕ} (p:Fin (n+1)→Skeleton C) (i:Fin (n+1))
    (k:Fin (n+2)) (j:Fin n) :
    (wordDiagram p i ⋙ reindex (SimplexCategory.δ k).toOrderHom) ⋙ eval n ⋙ Pi.eval _ j ≅
      wordInclude p i ⋙ faceEdge k j :=
  Functor.isoWhiskerLeft (wordDiagram p i) (faceEdgeIso k j).symm ≪≫
    Functor.isoWhiskerRight (wordDiagram_eval p i) (faceEdge k j)
noncomputable def includeProjIso {n:ℕ} (p:Fin n→Skeleton C) (i j:Fin n) :
    wordInclude p i ⋙ Pi.eval _ j ≅
      (if i=j then (property (p i)).ι else (Functor.const _).obj (repr (p j))) :=
  eqToIso (wordInclude_proj p i j)
noncomputable def wordPair_left {n:ℕ} (p:Fin n→Skeleton C) (i j:Fin n) (h:i≠j) :
    wordInclude p i ⋙ pairAt i j ≅ (property (p i)).ι ⋙ tensorRight (repr (p j)) := by
  classical
  change ((wordInclude p i ⋙ Pi.eval _ i).prod' (wordInclude p i ⋙ Pi.eval _ j)) ⋙ tensor C ≅ _
  rw [wordInclude_proj,wordInclude_proj,ite_eq_left rfl,ite_eq_right h]
  exact NatIso.ofComponents (fun _=>Iso.refl _) (by intro X Y f; simp)
noncomputable def wordPair_right {n:ℕ} (p:Fin n→Skeleton C) (i j:Fin n) (h:i≠j) :
    wordInclude p j ⋙ pairAt i j ≅ (property (p j)).ι ⋙ tensorLeft (repr (p i)) := by
  classical
  change ((wordInclude p j ⋙ Pi.eval _ i).prod' (wordInclude p j ⋙ Pi.eval _ j)) ⋙ tensor C ≅ _
  rw [wordInclude_proj,wordInclude_proj,ite_eq_right h.symm,ite_eq_left rfl]
  exact NatIso.ofComponents (fun _=>Iso.refl _) (by intro X Y f; simp)
noncomputable def wordPair_other {n:ℕ} (p:Fin n→Skeleton C) (i j k:Fin n) (hi:k≠i) (hj:k≠j) :
    wordInclude p k ⋙ pairAt i j ≅ (Functor.const _).obj (repr (p i) ⊗ repr (p j)) := by
  classical
  change ((wordInclude p k ⋙ Pi.eval _ i).prod' (wordInclude p k ⋙ Pi.eval _ j)) ⋙ tensor C ≅ _
  rw [wordInclude_proj,wordInclude_proj,ite_eq_right hi,ite_eq_right hj]
  exact NatIso.ofComponents (fun _=>Iso.refl _) (by intro X Y f; simp)
omit [SymmetricCategory C] in
lemma face_recognition {n:ℕ} (p:Fin (n+1)→Skeleton C) (i:Fin (n+1)) (k:Fin (n+2))
    (p':Fin n→Skeleton C) (i':Fin n) (T:Fiber (p i)⥤Fiber (p' i'))
    (e:∀j:Fin n,wordInclude p i ⋙ faceEdge k j ≅ (T⋙wordInclude p' i') ⋙ Pi.eval _ j) :
    primitive p i ≫ NerveHomology.map (reindex (SimplexCategory.δ k).toOrderHom) 1 =
      NerveHomology.map T 1 ≫ primitive p' i' := by
  rw [primitive_eq,←NerveHomology.comp]
  apply recognition p' i' _ T
  exact NatIso.pi' (fun j=>primitiveFace_eval p i k j ≪≫ e j)
omit [SymmetricCategory C] in
lemma face_recognition_const {n:ℕ} (p:Fin (n+1)→Skeleton C) (i:Fin (n+1)) (k:Fin (n+2))
    (U:Fin n→C)
    (e:∀j:Fin n,wordInclude p i ⋙ faceEdge k j ≅ (Functor.const (Fiber (p i))).obj (U j)) :
    primitive p i ≫ NerveHomology.map (reindex (SimplexCategory.δ k).toOrderHom) 1 =0 := by
  rw [primitive_eq,←NerveHomology.comp]
  apply recognition_const _ U
  exact NatIso.pi' (fun j=>primitiveFace_eval p i k j ≪≫ e j)
end MarkedH1

end OAI
