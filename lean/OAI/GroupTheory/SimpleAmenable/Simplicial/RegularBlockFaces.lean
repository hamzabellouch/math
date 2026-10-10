import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.RegularLiftFaces

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite HomologicalComplex AlgebraicTopology
namespace MonoidNerveCoordinates
open CoefficientNerve

variable {P:Type} [CommMonoid P]
lemma trunc_ofLabels {n:ℕ} (k:Fin (n+2)) (x:Fin (n+1)→P) :
    trunc (SimplexCategory.δ k) (ofLabels x)=ofLabels (faceLabels k x) := by
  rw [←ofLabels_labels (trunc (SimplexCategory.δ k) (ofLabels x))]
  congr 1
  exact (labels_face (ofLabels x) k).trans (congrArg (faceLabels k) (labels_ofLabels x))
end MonoidNerveCoordinates
namespace RegularLabels
open CoefficientNerve RegularCoordinates MonoidNerveCoordinates FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
@[reassoc] lemma inj_horizontalFace {h v:ℕ} (k:Fin (h+2)) (y:Fin v→P) (p:P) (x:Fin (h+1)→P) :
    inj F (y,p,x) ≫ ((chainSimplicial (RegularCoefficient.coeffComplex F)).δ k).f v =
      F.map (arrow (faceWeight k x) p) ≫ inj F (y,faceWeight k x*p,faceLabels k x) := by
  change singleLabel F p y ≫ single ((RegularCoefficient.coeffComplex F).X v) (ofLabels x) ≫
      map ((RegularCoefficient.coeffComplex F).X v) (SimplexCategory.δ k) = _
  erw [single_map,tail_face,trunc_ofLabels]
  change singleLabel F p y ≫ (RegularCoefficient.action F (faceWeight k x)).app (op ⦋v⦌) ≫
      single ((RegularCoefficient.coeffComplex F).X v) (ofLabels (faceLabels k x)) = _
  erw [←Category.assoc,singleLabel_action,Category.assoc]
@[reassoc] lemma inj_dV {h v:ℕ} (y:Fin (v+1)→P) (p:P) (x:Fin h→P) :
    inj F (y,p,x) ≫ ((RegularCoefficient.double F).X h).d (v+1) v =
      ∑k:Fin (v+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k y) p) ≫
        inj F (faceLabels k y,faceWeight k y*p,x)) := by
  change singleLabel F p y ≫ single ((RegularCoefficient.coeffComplex F).X (v+1)) (ofLabels x) ≫
    (mapNat ((RegularCoefficient.coeffComplex F).d (v+1) v)).app (op ⦋h⦌) = _
  erw [single_mapNat]
  change singleLabel F p y ≫ (complex F).d (v+1) v ≫
    single ((RegularCoefficient.coeffComplex F).X v) (ofLabels x) = _
  have hd : (complex F).d (v+1) v = ∑k:Fin (v+2),(-1:ℤ)^k.val • (simplicial F).δ k :=
    AlternatingFaceMapComplex.obj_d_eq (simplicial F) v
  rw [hd]
  erw [Preadditive.sum_comp,Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro index _
  erw [Preadditive.zsmul_comp,Preadditive.comp_zsmul,←Category.assoc,singleLabel_face,Category.assoc]
  rfl
@[reassoc] lemma inj_dH {h v:ℕ} (y:Fin v→P) (p:P) (x:Fin (h+1)→P) :
    inj F (y,p,x) ≫ ((RegularCoefficient.double F).d (h+1) h).f v =
      ∑k:Fin (h+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k x) p) ≫
        inj F (y,faceWeight k x*p,faceLabels k x)) := by
  change inj F (y,p,x) ≫ ((AlternatingFaceMapComplex.obj
    (chainSimplicial (RegularCoefficient.coeffComplex F))).d (h+1) h).f v = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  change inj F (y,p,x) ≫ (HomologicalComplex.Hom.fAddMonoidHom v)
    (∑i:Fin (h+2),(-1:ℤ)^i.val • (chainSimplicial (RegularCoefficient.coeffComplex F)).δ i) = _
  erw [map_sum,Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro index _
  erw [map_zsmul,Preadditive.comp_zsmul,inj_horizontalFace]
  rfl
end RegularLabels

end

end OAI
