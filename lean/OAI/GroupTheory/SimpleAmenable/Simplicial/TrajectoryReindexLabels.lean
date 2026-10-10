import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleBarMaps
import OAI.GroupTheory.SimpleAmenable.Homology.LabelRelabel
import OAI.GroupTheory.SimpleAmenable.Configurations.LabelTranslation
import OAI.GroupTheory.SimpleAmenable.Configurations.LabelledStringEquiv

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled
section

variable {a n m:ℕ}
def reindexLabel (u : Fin (m+1) ⥤ Fin (n+1))
    (g:Fin n → CutRing × CutRing) (i:Fin m) : CutRing × CutRing :=
  Fin.partialSum g (u.obj i.succ)-Fin.partialSum g (u.obj i.castSucc)
def initialDisplacement (u : Fin (m+1) ⥤ Fin (n+1))
    (g:Fin n → CutRing × CutRing) : CutRing × CutRing :=
  Fin.partialSum g (u.obj 0)
lemma representative_partialSum (g:Fin n → CutRing × CutRing) (hg:Reduced g) (i:Fin (n+1)) :
    orbitRepresentative (Fin.partialSum g i)=Fin.partialSum g i := by
  induction i using Fin.induction with
  | zero => simp only [Fin.partialSum_zero]; rfl
  | succ i ih => rw [Fin.partialSum_succ,representative_add,ih,hg i]
lemma reindexLabel_reduced (u : Fin (m+1) ⥤ Fin (n+1))
    (g:Fin n → CutRing × CutRing) (hg:Reduced g) : Reduced (reindexLabel u g) := by
  intro i
  rw [reindexLabel,representative_sub,representative_partialSum g hg,representative_partialSum g hg]
lemma partialSum_reindexLabel (u : Fin (m+1) ⥤ Fin (n+1))
    (g:Fin n → CutRing × CutRing) (i:Fin (m+1)) :
    Fin.partialSum (reindexLabel u g) i =
      Fin.partialSum g (u.obj i)-initialDisplacement u g := by
  induction i using Fin.induction with
  | zero => simp only [Fin.partialSum_zero,initialDisplacement,sub_self]
  | succ i ih => rw [Fin.partialSum_succ,ih,reindexLabel]; abel
noncomputable abbrev vertexArrow (U:Labelled a n) (i:Fin (n+1)) :
    U.polygon ⟶ (string U).obj.obj i :=
  shiftArrow U.polygon (fun k => Fin.partialSum (U.label k) i)
lemma initial_baseArrow (U:Labelled a n) (i:Fin (n+1)) :
    initial U ≫ baseArrow (string U).obj i=vertexArrow U i := by
  change initial U ≫ (inv (initial U) ≫ vertexArrow U i) = _
  simp
lemma vertexArrow_zero (U:Labelled a n) : vertexArrow U 0=initial U := rfl
lemma vertexArrow_ladder {U V:Labelled a n} (f:U⟶V) (i:Fin (n+1)) :
    vertexArrow U i ≫ (ladder f).hom.app i = f.arrow ≫ vertexArrow V i := by
  rw [←initial_baseArrow,Category.assoc]
  have h := (ladder f).hom.naturality (homOfLE (Fin.zero_le i))
  change baseArrow _ i ≫ (ladder f).hom.app i = (ladder f).hom.app 0 ≫ baseArrow _ i at h
  rw [h,ladder_zero]
  simp only [initialArrow,Category.assoc,IsIso.hom_inv_id_assoc,←initial_baseArrow]
lemma ladder_app {U V:Labelled a n} (f:U⟶V) (i:Fin (n+1)) :
    (ladder f).hom.app i = inv (vertexArrow U i) ≫ f.arrow ≫ vertexArrow V i := by
  apply (cancel_epi (vertexArrow U i)).mp
  rw [vertexArrow_ladder]
  simp
lemma trajectoryShift_vertex (U:Labelled a n) (x:U.polygon.Point) (i:Fin (n+1)) :
    trajectoryShift (string U).obj ((initial U).toEquiv x) i = Fin.partialSum (U.label x.val.1) i := by
  change trajectoryShift (translationString U.polygon (fun j k => Fin.partialSum (U.label k) j))
    ((shiftArrow U.polygon (fun k => Fin.partialSum (U.label k) 0)).toEquiv x) i = _
  rw [trajectoryShift_translationString]
  simp only [Fin.partialSum_zero,sub_zero]
  exact representative_partialSum _ (U.reduced _) i
lemma increments_vertex_reindex (U:Labelled a n) (u : Fin (m+1) ⥤ Fin (n+1))
    (x:U.polygon.Point) :
    increments (u ⋙ (string U).obj) ((vertexArrow U (u.obj 0)).toEquiv x) =
      reindexLabel u (U.label x.val.1) := by
  funext i
  rw [←initial_baseArrow,arrow_comp_apply,increments_reindex,
    trajectoryShift_vertex,trajectoryShift_vertex]
  rfl
end

section
variable {a n m:ℕ} (u:Fin (m+1) ⥤ Fin (n+1))
noncomputable def reindexFunctor : Labelled a n ⥤ Labelled a m :=
  translateFunctor (initialDisplacement u) ⋙ relabel (reindexLabel u) (reindexLabel_reduced u)
lemma reindexFunctor_arrow {U V:Labelled a n} (f: U⟶V) :
    ((reindexFunctor u).map f).arrow =
      inv (vertexArrow U (u.obj 0)) ≫ f.arrow ≫ vertexArrow V (u.obj 0) := rfl
noncomputable abbrev reindexInitial (U:Labelled a n) :
    (string ((reindexFunctor u).obj U)).obj.obj 0 ⟶ (string U).obj.obj (u.obj 0) :=
  inv (X := ((reindexFunctor u).obj U).polygon)
    (Y := (string ((reindexFunctor u).obj U)).obj.obj 0) (initial ((reindexFunctor u).obj U))
lemma reindexInitial_positional (U:Labelled a n) : Positional (reindexInitial u U) :=
  positional_inv (incrementInitial_positional _ _)
lemma reindexInitial_labels (U:Labelled a n)
    (x:((string ((reindexFunctor u).obj U)).obj.obj 0).Point) :
    increments (u ⋙ (string U).obj) ((reindexInitial u U).toEquiv x) =
      increments (string ((reindexFunctor u).obj U)).obj x := by
  obtain ⟨y,rfl⟩ := (initial ((reindexFunctor u).obj U)).toEquiv.surjective x
  rw [incrementString_spec_reduced _ _ ((reindexFunctor u).obj U).reduced]
  have h : (reindexInitial u U).toEquiv ((initial ((reindexFunctor u).obj U)).toEquiv y)=y := by
    erw [inv_arrow_apply]
    exact Equiv.symm_apply_apply _ _
  rw [h]
  obtain ⟨z,rfl⟩ := (vertexArrow U (u.obj 0)).toEquiv.surjective y
  exact increments_vertex_reindex U u z
noncomputable def reindexLadder (U:Labelled a n) :
    string ((reindexFunctor u).obj U) ⟶ (stringReindex u).obj (string U) :=
  ⟨extendLadder (reindexInitial u U),extendLadder_positional_of_increments _
    (reindexInitial_positional u U) (reindexInitial_labels u U)⟩
@[simp] lemma reindexLadder_zero (U:Labelled a n) :
    (reindexLadder u U).hom.app 0=reindexInitial u U := extendLadder_zero _
private lemma comp_inv_last {D : Type*} [Category D] {A B X Y : D}
    (a : A ⟶ B) (f : B ⟶ X) (g : X ⟶ Y) [IsIso g] :
    (a ≫ f ≫ g) ≫ inv g = a ≫ f := by
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private lemma cancel_two_inverses {D : Type*} [Category D] {A B X Y : D}
    (a : A ⟶ B) (f : A ⟶ X) (g : X ⟶ Y) [IsIso a] [IsIso g] :
    a ≫ (inv a ≫ f ≫ g) ≫ inv g = f := by
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id, Category.comp_id]

noncomputable def reindexStringIso : reindexFunctor (a:=a) u ⋙ toStrings ≅
    toStrings ⋙ stringReindex u :=
  NatIso.ofComponents (fun U => @asIso (StringGroupoid a m) _ _ _ (reindexLadder u U)
    (IsIso.of_groupoid (C := StringGroupoid a m) _)) (by
    intro U V f
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change (ladder ((reindexFunctor u).map f)).hom.app 0 ≫ (reindexLadder u V).hom.app 0 =
      (reindexLadder u U).hom.app 0 ≫ (ladder f).hom.app (u.obj 0)
    rw [reindexLadder_zero,reindexLadder_zero,ladder_zero,ladder_app]
    simp only [initialArrow,reindexInitial,reindexFunctor_arrow]
    exact @comp_inv_last _ _ _ _ _ _ _ _ _
      (IsIso.of_groupoid (C := PolygonObject a) _))
end

variable {a n m:ℕ}
lemma tensorLadder_vertex (U V:Labelled a n) (i:Fin (n+1)) :
    sumArrow (vertexArrow U i) (vertexArrow V i) ≫ (tensorLadder U V).hom.app i =
      vertexArrow (U⊗V) i := by
  have h := (tensorLadder U V).hom.naturality (homOfLE (Fin.zero_le i))
  change sumArrow (baseArrow (string U).obj i) (baseArrow (string V).obj i) ≫
    (tensorLadder U V).hom.app i = (tensorLadder U V).hom.app 0 ≫ baseArrow (string (U⊗V)).obj i at h
  rw [tensorLadder_zero] at h
  erw [←initial_baseArrow,←initial_baseArrow,sumArrow_comp,Category.assoc,h]
  change sumArrow (initial U) (initial V) ≫
    (inv (sumArrow (initial U) (initial V)) ≫ initial (U⊗V)) ≫ baseArrow _ i = _
  simp only [Category.assoc,IsIso.hom_inv_id_assoc]
  exact initial_baseArrow _ _
lemma tensorLadder_app (U V:Labelled a n) (i:Fin (n+1)) :
    (tensorLadder U V).hom.app i =
      inv (sumArrow (vertexArrow U i) (vertexArrow V i)) ≫ vertexArrow (U⊗V) i := by
  apply (cancel_epi (sumArrow (vertexArrow U i) (vertexArrow V i))).mp
  rw [tensorLadder_vertex,IsIso.hom_inv_id_assoc]
variable (u:Fin (m+1) ⥤ Fin (n+1))
noncomputable instance reindexMonoidal : (reindexFunctor (a:=a) u).Monoidal := by
  unfold reindexFunctor; infer_instance
noncomputable instance reindexBraided : (reindexFunctor (a:=a) u).Braided := by
  unfold reindexFunctor; infer_instance
lemma reindex_μ_arrow (U V:Labelled a n) :
    (Functor.LaxMonoidal.μ (reindexFunctor u) U V).arrow =
      inv (sumArrow (vertexArrow U (u.obj 0)) (vertexArrow V (u.obj 0))) ≫ vertexArrow (U⊗V) (u.obj 0) := by
  change (Functor.LaxMonoidal.μ
    (translateFunctor (initialDisplacement u) ⋙ relabel (reindexLabel u) (reindexLabel_reduced u)) U V).arrow = _
  rw [Functor.LaxMonoidal.comp_μ]
  change (𝟙 _) ≫ (translationTensor (initialDisplacement u) U V).arrow = _
  rw [Category.id_comp]
  rfl
noncomputable instance reindexStringMonoidal : NatTrans.IsMonoidal (reindexStringIso (a:=a) u).hom where
  unit := by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    apply Arrow.ext
    apply Equiv.ext
    intro x
    change Point PolygonObject.empty at x
    exact isEmptyElim x
  tensor U V := by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change ((Functor.LaxMonoidal.μ (reindexFunctor u ⋙ toStrings) U V).hom.app 0) ≫
      (reindexLadder u (U⊗V)).hom.app 0 =
      sumArrow ((reindexLadder u U).hom.app 0) ((reindexLadder u V).hom.app 0) ≫
        ((Functor.LaxMonoidal.μ (toStrings ⋙ stringReindex u) U V).hom.app 0)
    rw [Functor.LaxMonoidal.comp_μ,Functor.LaxMonoidal.comp_μ]
    change (tensorLadder ((reindexFunctor u).obj U) ((reindexFunctor u).obj V)).hom.app 0 ≫
      (ladder (Functor.LaxMonoidal.μ (reindexFunctor u) U V)).hom.app 0 ≫
      (reindexLadder u (U⊗V)).hom.app 0 =
      sumArrow ((reindexLadder u U).hom.app 0) ((reindexLadder u V).hom.app 0) ≫
        (𝟙 _ ≫ (tensorLadder U V).hom.app (u.obj 0))
    erw [tensorLadder_zero,ladder_zero,reindexLadder_zero,reindexLadder_zero,reindexLadder_zero,
      Category.id_comp,tensorLadder_app]
    simp only [tensorInitial,initialArrow,reindexInitial,Category.assoc,reindex_μ_arrow]
    congr 1
    · apply (cancel_epi (sumArrow (initial ((reindexFunctor u).obj U)) (initial ((reindexFunctor u).obj V)))).mp
      erw [IsIso.hom_inv_id]
      change 𝟙 _ = (_ ⊗ₘ _) ≫ (_ ⊗ₘ _)
      rw [tensorHom_comp_tensorHom]
      simp
    · exact @cancel_two_inverses _ _ _ _ _ _ _ _ _
        (IsIso.of_groupoid (C := PolygonObject a) _)
        (IsIso.of_groupoid (C := PolygonObject a) _)
end SimpleAmenable.PolygonObject.Labelled

end OAI
