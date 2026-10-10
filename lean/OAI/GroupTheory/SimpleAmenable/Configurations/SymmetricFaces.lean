import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FullGroupStability
import OAI.GroupTheory.SimpleAmenable.Configurations.SymmetricConfiguration

namespace OAI

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

section

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
noncomputable def facePermutation (i j : Fin (p+1)) : Equiv.Perm (Fin (p+1)) :=
  (finSuccEquiv' i).trans (finSuccEquiv' j).symm
@[simp] lemma facePermutation_apply (i j : Fin (p+1)) (k : Fin p) :
    facePermutation i j (i.succAbove k)=j.succAbove k := by simp [facePermutation]
noncomputable def permHom (f:Configuration m p) (σ:Equiv.Perm (Fin p)) : G m :=
  σ.viaFintypeEmbedding ⟨f.val,f.property⟩
lemma permHom_apply (f:Configuration m p) (σ:Equiv.Perm (Fin p)) (i:Fin p) : permHom f σ (f i)=f (σ i) :=
  Equiv.Perm.viaFintypeEmbedding_apply_image _ _ _
lemma permHom_fixed (f:Configuration m p) (σ:Equiv.Perm (Fin p)) (x:Fin m) (hx:x∉Set.range f.val) : permHom f σ x=x :=
  Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hx
lemma permHom_centralizes (f:Configuration m p) (σ:Equiv.Perm (Fin p))
    (h:MulAction.stabilizer (G m) f) : permHom f σ * h.val = h.val * permHom f σ := by
  have hh (i:Fin p) : h.val (f i)=f i := congrArg (fun t:Configuration m p=>t i) h.property
  exact (supported_fixer_commute (f:=h.val) (g:=permHom f σ) (U:=Set.range f.val)
    (by rintro x ⟨i,rfl⟩; exact hh i) (permHom_fixed f σ)).symm.eq
lemma permHom_face (f:Configuration m (p+1)) (i j:Fin (p+1)) :
    permHom f (facePermutation i j) • face i f=face j f := by
  apply ext; intro k
  change permHom f _ (f (i.succAbove k))=f (j.succAbove k)
  rw [permHom_apply,facePermutation_apply]
lemma homology_face_eq (m p:ℕ) (hm:p+1 ≤ m) (q:ℕ) (i j:Fin (p+1)) :
    (groupHomology.functor ℤ (G m) q).map (faceHom m p i)=
      (groupHomology.functor ℤ (G m) q).map (faceHom m p j) := by
  let f := standardLE m (p+1) hm
  exact TransitiveInduction.map_equivariant_eq_of_centralizer (face j) (face i)
    (face_smul j) (face_smul i) f (fun h=>transitive f h)
    (permHom f (facePermutation j i)) (permHom_centralizes f _) (permHom_face f j i) q
lemma boundary_two (m : ℕ) : boundary m 1 = faceHom m 1 0 - faceHom m 1 1 := by
  rw [boundary_sum, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

lemma boundary_three (m : ℕ) : boundary m 2 =
    faceHom m 2 0 - faceHom m 2 1 + faceHom m 2 2 := by
  rw [boundary_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
  norm_num
  abel

lemma homology_boundary_two_zero (m : ℕ) (hm : 7 < m) (q : ℕ) :
    (groupHomology.functor ℤ (G m) q).map (boundary m 1)=0 := by
  rw [boundary_two, Functor.map_sub, homology_face_eq m 1 (by omega) q 1 0, sub_self]

lemma homology_boundary_three (m : ℕ) (hm : 10 < m) (q : ℕ) :
    (groupHomology.functor ℤ (G m) q).map (boundary m 2)=
      (groupHomology.functor ℤ (G m) q).map (faceHom m 2 0) := by
  rw [boundary_three, Functor.map_add, Functor.map_sub,
    homology_face_eq m 2 (by omega) q 1 0, homology_face_eq m 2 (by omega) q 2 0, sub_self, zero_add]

lemma boundary_square (m p : ℕ) : boundary m (p+1) ≫ boundary m p=0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  apply (chainEquiv m p).injective
  change chainEquiv m p ((boundary m p).hom ((boundary m (p+1)).hom c)) =
    chainEquiv m p 0
  rw [boundary_chain, boundary_chain, ConfigurationChains.degreeBoundary_square, map_zero]

lemma boundary_exact (m p : ℕ) (hm : 32 ≤ m) (hp : p ≤ 2) :
    (ShortComplex.mk (boundary m (p+1)) (boundary m p) (boundary_square m p)).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{0} ℤ (G m))
    (ModuleCat.{0} ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (boundary m p).hom x=0 at hx
  have hc : ConfigurationChains.degreeBoundary ((Ne:Fin m→Fin m→Prop)) p (chainEquiv m (p+1) x)=0 := by
    rw [← boundary_chain, hx, map_zero]
  obtain ⟨y,hy⟩ := (lowDegree_exact hm hp _).mp hc
  refine ⟨(chainEquiv m (p+2)).symm y,?_⟩
  apply (chainEquiv m (p+1)).injective
  change chainEquiv m (p+1) ((boundary m (p+1)).hom _) = _
  rw [boundary_chain, LinearEquiv.apply_symm_apply, hy]

lemma boundary_zero_eq_face (m : ℕ) : boundary m 0=faceHom m 0 0 := by
  rw [boundary_sum]
  simp

lemma boundary_zero_epi (m : ℕ) (hm : 0 < m) : Epi (boundary m 0) := by
  rw [boundary_zero_eq_face, Rep.epi_iff_surjective]
  change Function.Surjective (Finsupp.mapDomain (face (0:Fin 1)))
  apply Finsupp.mapDomain_surjective
  intro f
  refine ⟨standardLE m 1 (by omega),?_⟩
  apply ext
  intro i
  exact Fin.elim0 i

lemma face_H0_isIso (m p : ℕ) (hm : 3*(p+1)+1 < m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (G m) 0).map (faceHom m p i)) := by
  let f := standardLE m (p+1) (by omega : p+1 ≤ m)
  exact TransitiveInduction.isIso_map_equivariant_H0 (face i) (face_smul i) f
    (fun h => transitive f h) (fun h => transitive _ h)

lemma boundary_two_H0_isIso (m : ℕ) (hm : 10 < m) :
    IsIso ((groupHomology.functor ℤ (G m) 0).map (boundary m 2)) := by
  rw [homology_boundary_three m hm 0]
  exact face_H0_isIso m 2 hm 0
lemma boundary_zero_H1_isIso (m : ℕ) (hm : 32 ≤ m) :
    IsIso ((groupHomology.functor ℤ (G m) 1).map (boundary m 0)) := by
  let boundaryEpi := boundary_zero_epi m (by omega)
  let boundaryIso : IsIso (BoundedHomologyEdge.Hmap 0 (boundary m 2)) :=
    boundary_two_H0_isIso m (by omega)
  exact BoundedHomologyEdge.chain_H1_isIso (boundary m 0) (boundary m 1)
    (boundary m 2) (boundary_square m 0) (boundary_square m 1)
    (boundary_exact m 0 hm (by omega)) (boundary_exact m 1 hm (by omega))
    (homology_boundary_two_zero m (by omega) 1)

end

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
instance empty_subsingleton (m : ℕ) : Subsingleton (Configuration m 0) :=
  ⟨fun _ _ => ext (fun i => Fin.elim0 i)⟩

noncomputable def empty (m : ℕ) : Configuration m 0 := standardLE m 0 (by omega)

noncomputable def emptyIso (m : ℕ) : column m 0 ≅ Rep.trivial ℤ (G m) ℤ :=
  Rep.mkIso (Representation.Equiv.mk (Finsupp.uniqueLinearEquiv ℤ ℤ (empty m)) (by
    intro g
    apply Finsupp.lhom_ext
    intro x z
    change (TransitiveInduction.permutationRep g (single x z)) (empty m)=
      (single x z) (empty m)
    rw [TransitiveInduction.permutationRep_single]
    congr 2
    exact Subsingleton.elim _ _))

@[simp] lemma emptyIso_single (m : ℕ) (x : Configuration m 0) (z : ℤ) :
    (emptyIso m).hom.hom (single x z)=z := by
  change (single x z) (empty m)=z
  simp [Subsingleton.elim (empty m) x]
lemma augmentation_pointMap (f : Configuration m 1) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer (G m) f).subtype
      (TransitiveInduction.pointMap f) q ≫
      (groupHomology.functor ℤ (G m) q).map (boundary m 0) ≫
      (groupHomology.functor ℤ (G m) q).map (emptyIso m).hom =
    TrivialHomology.map (MulAction.stabilizer (G m) f).subtype q := by
  erw [← Functor.map_comp]
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (emptyIso m).hom.hom ((boundary m 0).hom (single f z))=z
    rw [boundary_zero_eq_face]
    dsimp only [faceHom]
    rw [TransitiveInduction.equivariantMap_single, emptyIso_single]
lemma stabilizer_H1_isIso (m : ℕ) (hm : 33 ≤ m) (f : Configuration m 1) :
    IsIso (TrivialHomology.map (MulAction.stabilizer (G m) f).subtype 1) := by
  have pointIso := TransitiveInduction.isIso_map_pointMap f (fun g => transitive f g) 1
  have boundaryIso := boundary_zero_H1_isIso m (by omega)
  erw [← augmentation_pointMap f 1]
  have lastIso : IsIso ((groupHomology.functor ℤ (G m) 1).map (emptyIso m).hom) := inferInstance
  have tailIso := IsIso.comp_isIso' boundaryIso lastIso
  exact IsIso.comp_isIso' pointIso tailIso

end SimpleAmenable.SymmetricConfiguration

end OAI
