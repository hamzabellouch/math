import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ProductChains

namespace OAI

section

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialAugment
open FreeChains AugmentedSplit

variable (X : SSet)
noncomputable def aug0 : (ModuleCat.free ℤ).obj (X.obj (op ⦋0⦌)) ⟶ Z := ModuleCat.freeDesc (M:=Z) (↾fun _ => (1:ℤ))
@[simp] lemma aug0_mk (x : X.obj (op ⦋0⦌)) : aug0 X (ModuleCat.freeMk x)=1 :=
  ModuleCat.freeDesc_apply (M:=Z) (↾fun _ => (1:ℤ)) x
lemma d_aug0 : (complex X).d 1 0 ≫ aug0 X=0 := by
  change (∑ i : Fin 2, (-1:ℤ)^i.val • (ModuleCat.free ℤ).map (X.δ i)) ≫ aug0 X=0
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,
    pow_zero,pow_one,one_smul,neg_smul,Preadditive.add_comp,Preadditive.neg_comp]
  apply ModuleCat.free_hom_ext
  intro x
  change aug0 X ((ModuleCat.free ℤ).map (X.δ 0) (ModuleCat.freeMk x)) -
    aug0 X ((ModuleCat.free ℤ).map (X.δ 1) (ModuleCat.freeMk x)) = 0
  simp only [ModuleCat.free_map_apply]
  rw [aug0_mk,aug0_mk,sub_self]
noncomputable def aug : complex X ⟶ U :=
  (ChainComplex.toSingle₀Equiv _ Z).symm ⟨aug0 X,d_aug0 X⟩
@[simp] lemma aug_f_zero : (aug X).f 0=aug0 X := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
noncomputable def sec (x : X.obj (op ⦋0⦌)) : U ⟶ complex X :=
  (ChainComplex.fromSingle₀Equiv _ Z).symm (ModuleCat.ofHom (Finsupp.lsingle x))
lemma section_aug (x : X.obj (op ⦋0⦌)) : sec X x ≫ aug X=𝟙 U := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f,HomologicalComplex.id_f,aug_f_zero]
  change ModuleCat.ofHom (Finsupp.lsingle x) ≫ aug0 X=𝟙 Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (ModuleCat.freeDesc (M:=Z) (↾fun _ : X.obj (op ⦋0⦌) => (1:ℤ))) (ModuleCat.freeMk x)=1
  exact ModuleCat.freeDesc_apply (M:=Z) (↾fun _ => (1:ℤ)) x
instance flat (n : ℕ) : Module.Flat ℤ ((complex X).X n) := by
  change Module.Flat ℤ (X.obj (op ⦋n⦌) →₀ ℤ)
  infer_instance

lemma lift_homology (x : X.obj (op ⦋0⦌)) :
    (X.chainComplex Z).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      (X.chainComplex Z).homologyπ 0 ≫
        homologyMap ((complexIso X).hom ≫ aug X) 0 ≫
          (singleObjHomologySelfIso c 0 Z).hom=𝟙 Z := by
  rw [homologyπ_naturality_assoc,liftCycles_comp_cyclesMap_assoc]
  change liftCycles ((single A c 0).obj Z) _ 0 _ _ ≫
    ((single A c 0).obj Z).homologyπ 0 ≫ (singleObjHomologySelfIso c 0 Z).hom = _
  rw [homologyπ_singleObjHomologySelfIso_hom]
  rw [singleObjCyclesSelfIso_hom,←Category.assoc,liftCycles_i]
  simp only [HomologicalComplex.comp_f,aug_f_zero]
  change Sigma.ι (fun _ : X.obj (op ⦋0⦌) => Z) x ≫ forward _ ≫ aug0 X=𝟙 Z
  rw [ι_forward_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (ModuleCat.freeDesc (M:=Z) (↾fun _ : X.obj (op ⦋0⦌) => (1:ℤ))) (ModuleCat.freeMk x)=1
  exact ModuleCat.freeDesc_apply (M:=Z) (↾fun _ => (1:ℤ)) x

lemma homology_aug :
    homologyMap ((complexIso X).hom ≫ aug X) 0 ≫
      (singleObjHomologySelfIso c 0 Z).hom = X.homology₀ε Z := by
  apply (cancel_epi ((X.chainComplex Z).homologyπ 0)).mp
  apply (cancel_epi (X.chainComplex Z).cycles₀Iso.inv).mp
  apply Sigma.hom_ext
  intro x
  have he : X.ιChainComplex x ≫ (X.chainComplex Z).cycles₀Iso.inv =
      (X.chainComplex Z).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono ((X.chainComplex Z).iCycles 0)).mp
    simp
  change X.ιChainComplex x ≫ _ = X.ιChainComplex x ≫ _
  simp only [←Category.assoc]
  rw [he]
  simp only [Category.assoc]
  rw [lift_homology,X.liftCycles_ιChainComplex_homologyπ_homology₀ε]

instance homology_aug_isIso [X.IsConnected] : IsIso (homologyMap (aug X) 0) := by
  have h := homology_aug X
  rw [homologyMap_comp,Category.assoc] at h
  have : IsIso (homologyMap (complexIso X).hom 0 ≫
    homologyMap (aug X) 0 ≫ (singleObjHomologySelfIso c 0 Z).hom) := by rw [h]; infer_instance
  have : IsIso (homologyMap (aug X) 0 ≫ (singleObjHomologySelfIso c 0 Z).hom) :=
    (isIso_comp_left_iff (homologyMap (complexIso X).hom 0) _).mp inferInstance
  exact (isIso_comp_right_iff _ (singleObjHomologySelfIso c 0 Z).hom).mp inferInstance
end SimplicialAugment

end

end

end OAI
