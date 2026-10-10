import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.FirstBarStableH1
import OAI.GroupTheory.SimpleAmenable.Homology.MarkedLowHomology

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace IntervalBar.Diagram
open FreeChains ComponentTranslation MarkedH1

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma row_one_three_finite
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1:A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 2:A)] :
    Module.Finite ℤ ((homologyRow (C:=C) 1).homology 3) := by
  have :=stableH1_finite (C:=C)
  have : Module.Finite ℤ (colimit (homologyDiagram (C:=C) 1):A) := inferInstanceAs
    (Module.Finite ℤ (ComponentStable.object (C:=C) 1:A))
  have :=RegularCoefficient.total_finite (homologyDiagram (C:=C) 1) 2 (by
    intro i hi
    have :=component_homology_finite (C:=C) i
    exact Module.Finite.equiv (CommMonoidOpposite.homologyIso (Skeleton C) i).symm.toLinearEquiv)
  exact Module.Finite.equiv (lowHomologyIso (C:=C)).toLinearEquiv
lemma first_row_two_finite
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1:A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 2:A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 3:A)] :
    Module.Finite ℤ ((homologyRow (C:=C) 2).homology 1) := by
  apply first_row_finite 2
  intro p r hpr hp
  have hr:r≤1:=by omega
  interval_cases r
  · have :=component_homology_finite (C:=C) p
    let e : ((nerve (SingleObj (Skeleton C))).homology Z p:A) ≅ (homologyRow (C:=C) 0).homology p :=
      (homologyFunctor A c p).mapIso ((complexIso _) ≪≫ (componentRowChainIso (C:=C)).symm)
    exact Module.Finite.equiv e.toLinearEquiv
  · have h:p=3:=by omega
    subst p
    exact row_one_three_finite (C:=C)
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace StableBarOne
open FreeChains ComponentTranslation IntervalBar.Diagram MarkedH1

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def insert {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) (q:ℕ) :
    (nerve (Fiber (p i))).homology Z q ⟶ (homologyRow (C:=C) q).X n :=
  SSet.homologyMap (nerveMap (wordDiagram p i)) Z q
@[reassoc] lemma binary_insert_face (p:Fin 2→Skeleton C) (i:Fin 2) (k:Fin 3) (q:ℕ) :
    insert p i q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ k).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q =
        SSet.homologyMap (nerveMap (wordInclude p i ⋙ binaryFace k)) Z q := by
  change SSet.homologyMap (nerveMap (wordDiagram p i)) Z q ≫
    SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ k).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q =
    SSet.homologyMap (nerveMap (wordDiagram p i) ≫
      nerveMap (reindex (SimplexCategory.δ k).toOrderHom) ≫ nerveMap oneEval) Z q
  simp only [SSet.homologyMap_comp]
@[reassoc] lemma binary_insert_zero (p:Fin 2→Skeleton C) (q:ℕ) :
    insert p 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q=ComponentStable.inclusion (p 1) q := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceZero (C:=C))).hom).congr_homologyMap Z q
  rw [h]
  rw [wordInclude_proj,ite_eq_left rfl]
  rfl
@[reassoc] lemma binary_insert_last (p:Fin 2→Skeleton C) (q:ℕ) :
    insert p 0 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q=ComponentStable.inclusion (p 0) q := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 0) (binaryFaceLast (C:=C))).hom).congr_homologyMap Z q
  rw [h]
  rw [wordInclude_proj,ite_eq_left rfl]
  rfl
@[reassoc] lemma binary_insert_zero_other (p:Fin 2→Skeleton C) (q:ℕ) (hq:q≠0) :
    insert p 0 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q=0 := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 0) (binaryFaceZero (C:=C))).hom).congr_homologyMap Z q
  rw [h,wordInclude_proj,ite_eq_right (by decide)]
  have hc : nerveMap ((Functor.const (Fiber (p 0))).obj (repr (p 1))) =
      SSet.const (nerveEquiv.symm (repr (p 1))) := by ext n x; rfl
  rw [hc]
  exact ConnectedProduct.const_homology_zero _ q hq
@[reassoc] lemma binary_insert_last_other (p:Fin 2→Skeleton C) (q:ℕ) (hq:q≠0) :
    insert p 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q=0 := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceLast (C:=C))).hom).congr_homologyMap Z q
  rw [h,wordInclude_proj,ite_eq_right (by decide)]
  have hc : nerveMap ((Functor.const (Fiber (p 1))).obj (repr (p 0))) =
      SSet.const (nerveEquiv.symm (repr (p 0))) := by ext n x; rfl
  rw [hc]
  exact ConnectedProduct.const_homology_zero _ q hq
@[reassoc] lemma binary_insert_middle (p:Fin 2→Skeleton C) (q:ℕ) :
    insert p 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q =
        SSet.homologyMap (nerveMap (translate (p 0) (p 1) (p 0*p 1) rfl)) Z q ≫
          ComponentStable.inclusion (p 0*p 1) q := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceMiddle (C:=C))).hom).congr_homologyMap Z q
  rw [h]
  have ht:=(NerveHomotopy.ofNatTrans (binaryRightTranslate p).hom).congr_homologyMap Z q
  rw [ht]
  change SSet.homologyMap (nerveMap (translate (p 0) (p 1) (p 0*p 1) rfl) ≫
    nerveMap (property (p 0*p 1)).ι) Z q = _
  rw [SSet.homologyMap_comp]
  rfl
lemma row_d10 (q:ℕ) (hq:q≠0) : (homologyRow (C:=C) q).d 1 0=0 := by
  apply IsZero.eq_zero_of_tgt
  exact nerve.positive_zero (fun U V:IntervalBar.Diagram C (Fin 1)=>⟨zeroHom C U V⟩) q hq
noncomputable def π (q:ℕ) (hq:q≠0) : (homologyRow (C:=C) q).X 1 ⟶ (homologyRow (C:=C) q).homology 1 :=
  ChainComplex.positiveπ _ 0 (row_d10 q hq)
@[reassoc (attr:=simp)] lemma d_π (q:ℕ) (hq:q≠0) : (homologyRow (C:=C) q).d 2 1 ≫ π q hq=0 :=
  ChainComplex.d_positiveπ _ 0 (row_d10 q hq)
noncomputable def oneIso (q:ℕ) : (homologyRow (C:=C) q).X 1 ≅ (nerve C).homology Z q := by
  exact @asIso (ModuleCat ℤ) _ _ _ _
    (NerveHomotopy.homologyMap_isIso (oneEval (C:=C)) Z q)
noncomputable def linearπ (q:ℕ) (hq:q≠0) : (nerve C).homology Z q ⟶ (homologyRow (C:=C) q).homology 1 :=
  (oneIso q).inv ≫ π q hq
instance linearπ_epi (q:ℕ) (hq:q≠0) : Epi (linearπ (C:=C) q hq) := by
  dsimp only [linearπ,π]
  infer_instance
@[reassoc (attr:=simp)] lemma oneIso_linearπ (q:ℕ) (hq:q≠0) :
    SSet.homologyMap (nerveMap (oneEval (C:=C))) Z q ≫ linearπ q hq=π q hq := by
  change (oneIso (C:=C) q).hom ≫ (oneIso (C:=C) q).inv ≫ π q hq= _
  simp
private lemma boundary_linearπ (v : Fin 2 → Skeleton C) (q : ℕ) (hq : q ≠ 0) :
    insert v 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q ≫ linearπ q hq -
    insert v 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q ≫ linearπ q hq +
    insert v 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q ≫ linearπ q hq=0 := by
  have hd:=congrArg (fun f=>insert v 1 q ≫ f) (d_π (C:=C) q hq)
  rw [SimplicialFirstFinite.d21] at hd
  simp only [Preadditive.add_comp,Preadditive.sub_comp,Preadditive.comp_add,
    Preadditive.comp_sub,comp_zero] at hd
  rw [←oneIso_linearπ q hq] at hd
  exact hd

private lemma eq_of_boundary {V : Type*} [AddGroup V] {x y z a b : V}
    (h : x - y + z = 0) (hx : x = a) (hy : y = b) (hz : z = 0) : b = a := by
  rw [hx,hy,hz,add_zero] at h
  exact (sub_eq_zero.mp h).symm

private lemma binary_linearπ (v : Fin 2 → Skeleton C) (q : ℕ) (hq : q ≠ 0) :
    SSet.homologyMap (nerveMap (translate (v 0) (v 1) (v 0 * v 1) rfl)) Z q ≫
        ComponentStable.inclusion (v 0 * v 1) q ≫ linearπ q hq =
      ComponentStable.inclusion (v 1) q ≫ linearπ q hq := by
  have hd := boundary_linearπ v q hq
  have zeroFace := binary_insert_zero_assoc v q (linearπ (C:=C) q hq)
  have middleFace := binary_insert_middle_assoc v q (linearπ (C:=C) q hq)
  have lastFace := binary_insert_last_other_assoc v q hq (linearπ (C:=C) q hq)
  exact eq_of_boundary hd zeroFace middleFace (lastFace.trans zero_comp)

lemma translate_linearπ (r p s:Skeleton C) (h:r*p=s) (q:ℕ) (hq:q≠0) :
    SSet.homologyMap (nerveMap (translate r p s h)) Z q ≫ ComponentStable.inclusion s q ≫ linearπ q hq =
      ComponentStable.inclusion p q ≫ linearπ q hq := by
  subst s
  exact binary_linearπ ![r,p] q hq
noncomputable def cocone (q:ℕ) (hq:q≠0) : Cocone (homologyDiagram (C:=C) q) where
  pt := (homologyRow (C:=C) q).homology 1
  ι := {app p:=ComponentStable.inclusion p.back q ≫ linearπ q hq
        naturality {p s} f:=by
          change SSet.homologyMap (nerveMap (translate f.hom p.back s.back f.map_val)) Z q ≫
            ComponentStable.inclusion s.back q ≫ linearπ q hq = _
          erw [translate_linearπ,Category.comp_id]
          rfl}
noncomputable def fromStable (q:ℕ) (hq:q≠0) : ComponentStable.object (C:=C) q ⟶
    (homologyRow (C:=C) q).homology 1 := colimit.desc (homologyDiagram q) (cocone q hq)
@[reassoc (attr:=simp)] lemma toStable_fromStable (q:ℕ) (hq:q≠0) :
    ComponentStable.toStable (C:=C) q ≫ fromStable q hq=linearπ q hq := by
  apply (ComponentCoproduct.homologyIsColimit C q).hom_ext
  intro p
  change ComponentStable.inclusion p.as q ≫ (ComponentStable.toStable q ≫ fromStable q hq)=_
  rw [←Category.assoc,ComponentStable.inclusion_toStable]
  exact colimit.ι_desc (cocone (C:=C) q hq) ((ActionCategory.objEquiv _ _) p.as)
instance fromStable_epi (q:ℕ) (hq:q≠0) : Epi (fromStable (C:=C) q hq) := by
  have : Epi (ComponentStable.toStable (C:=C) q ≫ fromStable q hq):=by rw [toStable_fromStable]; infer_instance
  exact epi_of_epi (ComponentStable.toStable q) _
lemma row_one_finite (q:ℕ) (hq:q≠0) [Module.Finite ℤ (ComponentStable.object (C:=C) q : A)] :
    Module.Finite ℤ ((homologyRow (C:=C) q).homology 1) :=
  Module.Finite.of_surjective (fromStable q hq).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end StableBarOne

end OAI
