import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ProductNatural

namespace OAI

section
open CategoryTheory Simplicial SimplicialObject Opposite
namespace GroupNerveCoordinates

variable {G : Type} [Group G] {n : ℕ}
def labels (F:ComposableArrows (SingleObj G) n) : Fin n → G :=
  fun i => (F.map (homOfLE (show i.castSucc ≤ i.succ by exact Fin.castSucc_le_succ i)))⁻¹
noncomputable def ofLabels (g:Fin n → G) : ComposableArrows (SingleObj G) n where
  obj _ := SingleObj.star G
  map {i j} _ := (Fin.partialProd g j)⁻¹ * Fin.partialProd g i
  map_id i := inv_mul_cancel _
  map_comp := by intros; change _ = (_ * _) * (_ * _); group
@[simp] lemma labels_ofLabels (g:Fin n → G) : labels (ofLabels g)=g := by
  funext i
  change ((Fin.partialProd g i.succ)⁻¹ * Fin.partialProd g i.castSucc)⁻¹=g i
  rw [mul_inv_rev,inv_inv,Fin.partialProd_right_inv]
lemma eqToHom_one {x y:SingleObj G} (h:x=y) : eqToHom h=(1:G) := by subst y; rfl
@[simp] lemma ofLabels_labels (F:ComposableArrows (SingleObj G) n) : ofLabels (labels F)=F := by
  apply ComposableArrows.ext (fun _=>Subsingleton.elim _ _)
  intro i hi
  simp only [eqToHom_one,SingleObj.comp_as_mul,one_mul,mul_one]
  change (Fin.partialProd (labels F) (Fin.succ ⟨i,hi⟩))⁻¹ *
    Fin.partialProd (labels F) (Fin.castSucc ⟨i,hi⟩)=_
  rw [Fin.partialProd_succ,mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
  simp only [labels,inv_inv]
noncomputable def equiv (G:Type) [Group G] (n:ℕ) :
    ComposableArrows (SingleObj G) n ≃ (Fin n → G) where
  toFun := labels
  invFun := ofLabels
  left_inv := ofLabels_labels
  right_inv := labels_ofLabels
lemma labels_zero_face (F:ComposableArrows (SingleObj G) (n+1)) :
    labels ((nerve _).δ (0:Fin (n+2)) F) = Fin.tail (labels F) := by
  funext i
  rfl
lemma labels_succ_face (F:ComposableArrows (SingleObj G) (n+1)) (i:Fin (n+1)) :
    labels ((nerve _).δ i.succ F) = Fin.contractNth i (· * ·) (labels F) := by
  obtain ⟨g,rfl⟩ := (equiv G (n+1)).symm.surjective F
  change labels ((nerve _).δ i.succ (ofLabels g)) = _
  change labels ((nerve (SingleObj G)).δ i.succ (ofLabels g)) =
    Fin.contractNth i (· * ·) (labels (ofLabels g))
  rw [labels_ofLabels]
  funext k
  change ((Fin.partialProd g (i.succ.succAbove k.succ))⁻¹ *
    Fin.partialProd g (i.succ.succAbove k.castSucc))⁻¹ = _
  rw [mul_inv_rev,inv_inv,Fin.succ_succAbove_succ]
  exact Fin.inv_partialProd_mul_eq_contractNth g i k
lemma labels_map {H:Type} [Group H] (f:G →* H)
    (F:ComposableArrows (SingleObj G) n) :
    labels ((nerveMap (SingleObj.mapHom G H f)).app (op ⦋n⦌) F) = fun i=>f (labels F i) := by
  funext i
  exact (map_inv f _).symm
end GroupNerveCoordinates

end

section
open CategoryTheory Simplicial SimplicialObject Opposite AlgebraicTopology
open scoped BigOperators
namespace GroupNerveCoordinates
open FreeChains

attribute [local instance 1200] Rep.hV2
variable (G : Type) [Group G]
noncomputable def chainCoordinates (n:ℕ) :
    (complex (nerve (SingleObj G))).X n ≅
      (groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).X n :=
  (Finsupp.domLCongr (M:=ℤ) (R:=ℤ) (equiv G n)).toModuleIso
lemma coordinates_single (n:ℕ) (F:ComposableArrows (SingleObj G) n) (z:ℤ) :
    (chainCoordinates G n).hom (Finsupp.single F z) = Finsupp.single (labels F) z :=
  Finsupp.domLCongr_single _ _ _
lemma coordinates_d (n:ℕ) :
    (complex (nerve (SingleObj G))).d (n+1) n ≫ (chainCoordinates G n).hom =
      (chainCoordinates G (n+1)).hom ≫
        (groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).d (n+1) n := by
  classical
  rw [groupHomology.inhomogeneousChains.d_def]
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro F
  apply LinearMap.ext
  intro z
  change (chainCoordinates G n).hom.hom (((complex (nerve (SingleObj G))).d (n+1) n).hom
      (Finsupp.single F z)) = _
  rw [show (complex (nerve (SingleObj G))).d (n+1) n =
    ∑ i:Fin (n+2), (-1:ℤ)^(i:ℕ) • (ModuleCat.free ℤ).map ((nerve (SingleObj G)).δ i) from
    AlternatingFaceMapComplex.obj_d_eq _ n]
  erw [ModuleCat.hom_sum]
  change (Finsupp.domLCongr (M:=ℤ) (R:=ℤ) (equiv G n))
    ((∑ index:Fin (n+2), (-1:ℤ)^(index:ℕ) •
      Finsupp.lmapDomain (α:=ComposableArrows (SingleObj G) (n+1))
        (α':=ComposableArrows (SingleObj G) n) ℤ ℤ ((nerve (SingleObj G)).δ index))
      (Finsupp.single F z)) = _
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_zsmul]
  have hmap (i:Fin (n+2)) : (chainCoordinates G n).hom
      ((ModuleCat.free ℤ).map ((nerve (SingleObj G)).δ i) (Finsupp.single F z)) =
      Finsupp.single (labels ((nerve (SingleObj G)).δ i F)) z := by
    change (Finsupp.domLCongr (equiv G n))
      (Finsupp.lmapDomain ℤ ℤ ((nerve (SingleObj G)).δ i) (Finsupp.single F z)) = _
    rw [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    exact Finsupp.domLCongr_single _ _ _
  change (∑ i:Fin (n+2), (-1:ℤ)^(i:ℕ) • (chainCoordinates G n).hom
        ((ModuleCat.free ℤ).map ((nerve (SingleObj G)).δ i) (Finsupp.single F z))) = _
  simp only [hmap]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_zsmul,Fin.val_succ]
  change _ = groupHomology.inhomogeneousChains.d (Rep.trivial ℤ G ℤ) n
    ((chainCoordinates G (n+1)).hom (Finsupp.single F z))
  erw [coordinates_single,groupHomology.inhomogeneousChains.d_single]
  apply congrArg₂ (· + ·)
  · exact congrArg (fun faceLabels => Finsupp.single faceLabels z) (labels_zero_face F)
  · apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun faceLabels => (-1:ℤ)^((index:ℕ)+1) • Finsupp.single faceLabels z)
      (labels_succ_face F index)
noncomputable def chainIso : complex (nerve (SingleObj G)) ≅
    groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ) := by
  refine HomologicalComplex.Hom.isoOfComponents (chainCoordinates G) ?_
  rintro n m rfl
  exact (coordinates_d G m).symm
noncomputable def homologyIso (n:ℕ) :
    (nerve (SingleObj G)).homology Z n ≅ groupHomology (Rep.trivial ℤ G ℤ) n :=
  (HomologicalComplex.homologyFunctor A c n).mapIso (complexIso _ ≪≫ chainIso G)
end GroupNerveCoordinates

end

section
open CategoryTheory Simplicial SimplicialObject Opposite AlgebraicTopology
open ProductChains
namespace FreeChains

lemma complexIso_natural {X Y:SSet} (f:X⟶Y) :
    SSet.chainComplexMap f Z ≫ (complexIso Y).hom = (complexIso X).hom ≫ chainMap f := by
  apply HomologicalComplex.Hom.ext; funext n
  exact naturalIso.hom.naturality (f.app (op ⦋n⦌))
end FreeChains
namespace GroupNerveCoordinates
open FreeChains SimpleAmenable

attribute [local instance 1200] Rep.hV2
variable {G H:Type} [Group G] [Group H] (f:G→*H)
lemma coordinates_natural (n:ℕ) :
    (chainMap (nerveMap f.toFunctor)).f n ≫ (chainCoordinates H n).hom =
      (chainCoordinates G n).hom ≫
        (groupHomology.chainsMap f (TransitiveInduction.trivialMap f)).f n := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro z
  change (chainCoordinates H n).hom
    (Finsupp.lmapDomain ℤ ℤ ((nerveMap f.toFunctor).app (op ⦋n⦌)) (Finsupp.single s z)) = _
  rw [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  change (chainCoordinates H n).hom
    (Finsupp.single ((nerveMap f.toFunctor).app (op ⦋n⦌) s) z) = _
  erw [coordinates_single]
  change _=(groupHomology.chainsMap f (TransitiveInduction.trivialMap f)).f n
    ((chainCoordinates G n).hom (Finsupp.single s z))
  erw [coordinates_single,groupHomology.chainsMap_f_single,labels_map]
  rfl
lemma chainIso_natural :
    chainMap (nerveMap f.toFunctor) ≫ (chainIso H).hom =
      (chainIso G).hom ≫ groupHomology.chainsMap f (TransitiveInduction.trivialMap f) := by
  apply HomologicalComplex.Hom.ext; funext n
  exact coordinates_natural f n
lemma homologyIso_natural (n:ℕ) :
    SSet.homologyMap (nerveMap f.toFunctor) Z n ≫ (homologyIso H n).hom =
      (homologyIso G n).hom ≫ TrivialHomology.map f n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [←HomologicalComplex.homologyMap_comp,←HomologicalComplex.homologyMap_comp]
  congr 1
  change SSet.chainComplexMap (nerveMap f.toFunctor) Z ≫ (complexIso _).hom ≫ (chainIso H).hom =
    ((complexIso _).hom ≫ (chainIso G).hom) ≫ _
  rw [←Category.assoc,complexIso_natural,Category.assoc,chainIso_natural,←Category.assoc]
end GroupNerveCoordinates

end

end OAI
