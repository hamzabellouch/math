import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.PermutationAugmentation
import OAI.GroupTheory.SimpleAmenable.Configurations.SymmetricStabilizer

namespace OAI

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

section

attribute [local instance 1200] Rep.hV2
noncomputable def castGroup {m n:ℕ} (h:m=n) : G m ≃* G n := h ▸ MulEquiv.refl _
lemma castGroup_apply {m n:ℕ} (h:m=n) (g:G m) (i:Fin m) :
    castGroup h g (Fin.cast h i)=Fin.cast h (g i) := by subst n; rfl
lemma stabilize_add (k l n:ℕ) : stabilize (k+l) n =
    (castGroup (Nat.add_assoc k l n).symm).toMonoidHom.comp
      ((stabilize k (l+n)).comp (stabilize l n)) := by
  let h : k+(l+n)=(k+l)+n := (Nat.add_assoc k l n).symm
  apply MonoidHom.ext
  intro g
  apply Equiv.ext
  intro x
  obtain ⟨i,rfl⟩ := (finCongr h).surjective x
  change stabilize (k+l) n g (Fin.cast h i)=castGroup h (stabilize k (l+n) (stabilize l n g)) (Fin.cast h i)
  rw [castGroup_apply]
  induction i using Fin.addCases with
  | left i =>
    have he : Fin.cast h (i.castAdd (l+n))=(i.castAdd l).castAdd n := Fin.ext rfl
    rw [he,stabilize_apply_head,stabilize_apply_head]
    exact he.symm
  | right i =>
    rw [stabilize_apply_tail]
    induction i using Fin.addCases with
    | left i =>
      have he : Fin.cast h ((i.castAdd n).natAdd k)=(i.natAdd k).castAdd n := Fin.ext rfl
      rw [he,stabilize_apply_head,stabilize_apply_head]
      exact he.symm
    | right i =>
      have he : Fin.cast h ((i.natAdd l).natAdd k)=i.natAdd (k+l) := by
        apply Fin.ext
        simp only [Fin.val_cast,Fin.val_natAdd]
        omega
      rw [he,stabilize_apply_tail,stabilize_apply_tail]
      apply Fin.ext
      simp only [Fin.val_cast,Fin.val_natAdd]
      omega
lemma stabilize_zero_bijective (n:ℕ) : Function.Bijective (stabilize 0 n) := by
  refine ⟨stabilize_injective 0 n,?_⟩
  intro g
  have hg : g ∈ (stabilize 0 n).range := by
    rw [stabilize_range]
    exact Subsingleton.elim _ _
  exact hg
lemma stabilize_H1_isIso (k n:ℕ) (hn:32≤n) :
    IsIso (TrivialHomology.map (stabilize k n) 1) := by
  induction k with
  | zero =>
    exact TrivialHomology.isIso_equiv
      (MulEquiv.ofBijective (stabilize 0 n) (stabilize_zero_bijective n)) 1
  | succ k ih =>
    rw [show k+1=1+k by omega,stabilize_add,TrivialHomology.map_comp,TrivialHomology.map_comp]
    have := TrivialHomology.isIso_equiv (castGroup (Nat.add_assoc 1 k n).symm) 1
    have := stabilize_one_H1_isIso (k+n) (by omega)
    have := ih
    infer_instance
end

attribute [local instance 1200] Rep.hV2
lemma columnAugmentation_H1_isIso (p n : ℕ) (hn : 32 ≤ n) :
    IsIso ((groupHomology.functor ℤ (G (p+n)) 1).map
      (TransitiveInduction.augmentation (G (p+n)) (Configuration (p+n) p))) := by
  have pointIso := TransitiveInduction.isIso_map_pointMap (standard p n)
    (fun f => transitive _ f) 1
  have subtypeIso : IsIso (TrivialHomology.map
      (MulAction.stabilizer (G (p+n)) (standard p n)).subtype 1) := by
    have := stabilize_H1_isIso p n hn
    have := TrivialHomology.isIso_equiv (standardStabilizerEquiv p n) 1
    have he : TrivialHomology.map (standardStabilizerEquiv p n).toMonoidHom 1 ≫
        TrivialHomology.map (MulAction.stabilizer (G (p+n))
          (standard p n)).subtype 1 = TrivialHomology.map (stabilize p n) 1 := by
      rw [← TrivialHomology.map_comp, standardStabilizerEquiv_subtype]
    exact IsIso.of_isIso_fac_left he
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ pointIso subtypeIso
    (TransitiveInduction.augmentation_pointMap (standard p n) 1)

lemma face_H1_isIso (m p : ℕ) (hn : p+33 ≤ m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (G m) 1).map (faceHom m p i)) := by
  have hc (t : ℕ) (ht : t ≤ p+1) :
      IsIso ((groupHomology.functor ℤ (G m) 1).map
        (TransitiveInduction.augmentation (G m) (Configuration m t))) := by
    obtain ⟨n,rfl⟩ : ∃n,m=t+n := ⟨m-t,by omega⟩
    exact columnAugmentation_H1_isIso t n (by omega)
  have := hc p (by omega)
  have := hc (p+1) (by omega)
  have he := congrArg ((groupHomology.functor ℤ (G m) 1).map)
    (TransitiveInduction.augmentation_natural (face i) (face_smul i))
  rw [Functor.map_comp] at he
  exact IsIso.of_isIso_fac_right he

lemma boundary_two_H1_isIso (m : ℕ) (hm : 35 ≤ m) :
    IsIso ((groupHomology.functor ℤ (G m) 1).map (boundary m 2)) := by
  rw [homology_boundary_three m (by omega) 1]
  exact face_H1_isIso m 2 (by omega) 0

lemma boundary_five (m : ℕ) : boundary m 4 =
    faceHom m 4 0 - faceHom m 4 1 + faceHom m 4 2 - faceHom m 4 3 + faceHom m 4 4 := by
  rw [boundary_sum]
  simp only [Fin.sum_univ_succ]
  norm_num
  abel

lemma boundary_four_H0_isIso (m : ℕ) (hm : 16 < m) :
    IsIso ((groupHomology.functor ℤ (G m) 0).map (boundary m 4)) := by
  rw [boundary_five,Functor.map_add,Functor.map_sub,Functor.map_add,Functor.map_sub]
  rw [homology_face_eq m 4 (by omega) 0 1 0, homology_face_eq m 4 (by omega) 0 2 0,
    homology_face_eq m 4 (by omega) 0 3 0, homology_face_eq m 4 (by omega) 0 4 0]
  simp only [sub_self,zero_add]
  exact face_H0_isIso m 4 hm 0
lemma boundary_zero_H2_isIso (m : ℕ) (hm : 35 ≤ m) :
    IsIso ((groupHomology.functor ℤ (G m) 2).map (boundary m 0)) := by
  have := boundary_zero_epi m (by omega)
  have boundaryTwoH0 : IsIso (BoundedHomologyEdge.Hmap 0 (boundary m 2)) :=
    boundary_two_H0_isIso m (by omega)
  have boundaryTwoH1 : IsIso (BoundedHomologyEdge.Hmap 1 (boundary m 2)) :=
    boundary_two_H1_isIso m hm
  have boundaryFourH0 : IsIso (BoundedHomologyEdge.Hmap 0 (boundary m 4)) :=
    boundary_four_H0_isIso m (by omega)
  exact BoundedHomologyEdge.chain_H2_isIso (boundary m 0) (boundary m 1)
    (boundary m 2) (boundary m 3) (boundary m 4)
    (boundary_square m 0) (boundary_square m 1) (boundary_square m 2)
    (boundary_square m 3) (boundary_exact m 0 (by omega) (by omega))
    (boundary_exact m 1 (by omega) (by omega))
    (boundary_exact m 2 (by omega) (by omega))
    (homology_boundary_two_zero m (by omega) 2)
lemma stabilizer_H2_isIso (m : ℕ) (hm : 35 ≤ m) (f : Configuration m 1) :
    IsIso (TrivialHomology.map (MulAction.stabilizer (G m) f).subtype 2) := by
  have pointIso := TransitiveInduction.isIso_map_pointMap f (fun g => transitive f g) 2
  have boundaryIso := boundary_zero_H2_isIso m hm
  erw [← augmentation_pointMap f 2]
  have lastIso : IsIso ((groupHomology.functor ℤ (G m) 2).map (emptyIso m).hom) := inferInstance
  have tailIso := IsIso.comp_isIso' boundaryIso lastIso
  exact IsIso.comp_isIso' pointIso tailIso

lemma stabilize_one_H2_isIso (n : ℕ) (hn : 34 ≤ n) :
    IsIso (TrivialHomology.map (stabilize 1 n) 2) := by
  rw [← standardStabilizerEquiv_subtype 1 n, TrivialHomology.map_comp]
  have := TrivialHomology.isIso_equiv (standardStabilizerEquiv 1 n) 2
  have := stabilizer_H2_isIso (1+n) (by omega) (standard 1 n)
  infer_instance
end SimpleAmenable.SymmetricConfiguration

end OAI
