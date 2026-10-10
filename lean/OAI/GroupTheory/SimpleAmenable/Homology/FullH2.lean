import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.RegularAugmentation

namespace OAI

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.PolygonPlacement.Configuration

attribute [local instance 1200] Rep.hV2
lemma columnAugmentation_H1_isIso (a p n : ℕ) (hn : 32 ≤ n) (hm : 3*p+1 < p+n) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a (p+n)) 1).map
      (TransitiveInduction.augmentation (polygonFullGroup a (p+n)) (Configuration a (p+n) p))) := by
  have pointIso := TransitiveInduction.isIso_map_pointMap (standard a p n)
    (fun f => transitive _ f hm) 1
  have stabilizerIso : IsIso (TrivialHomology.map
      (MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n)).subtype 1) := by
    have := PolygonTracks.stabilize_H1_isIso a p n hn
    have := TrivialHomology.isIso_equiv (standardStabilizerEquiv a p n) 1
    have he : TrivialHomology.map (standardStabilizerEquiv a p n).toMonoidHom 1 ≫
        TrivialHomology.map (MulAction.stabilizer (polygonFullGroup a (p+n))
          (standard a p n)).subtype 1 = TrivialHomology.map (PolygonTracks.stabilize a p n) 1 := by
      rw [← TrivialHomology.map_comp, standardStabilizerEquiv_subtype]
    exact IsIso.of_isIso_fac_left he
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ pointIso stabilizerIso
    (TransitiveInduction.augmentation_pointMap (standard a p n) 1)

lemma face_H1_isIso (a m p : ℕ) (hn : p+33 ≤ m) (hm : 3*(p+1)+1 < m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map (faceHom a m p i)) := by
  have hc (t : ℕ) (ht : t ≤ p+1) :
      IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map
        (TransitiveInduction.augmentation (polygonFullGroup a m) (Configuration a m t))) := by
    obtain ⟨n,rfl⟩ : ∃n,m=t+n := ⟨m-t,by omega⟩
    exact columnAugmentation_H1_isIso a t n (by omega) (by omega)
  have := hc p (by omega)
  have := hc (p+1) (by omega)
  have he := congrArg ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map)
    (TransitiveInduction.augmentation_natural (face i) (face_smul i))
  rw [Functor.map_comp] at he
  exact IsIso.of_isIso_fac_right he

lemma boundary_two_H1_isIso (a m : ℕ) (hm : 35 ≤ m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map (boundary a m 2)) := by
  rw [homology_boundary_three a m (by omega) 1]
  exact face_H1_isIso a m 2 (by omega) (by omega) 0

lemma boundary_five (a m : ℕ) : boundary a m 4 =
    faceHom a m 4 0 - faceHom a m 4 1 + faceHom a m 4 2 - faceHom a m 4 3 + faceHom a m 4 4 := by
  rw [boundary_sum]
  simp only [Fin.sum_univ_succ]
  norm_num
  abel

lemma boundary_four_H0_isIso (a m : ℕ) (hm : 16 < m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 0).map (boundary a m 4)) := by
  rw [boundary_five,Functor.map_add,Functor.map_sub,Functor.map_add,Functor.map_sub]
  rw [homology_face_eq a m 4 hm 0 1 0, homology_face_eq a m 4 hm 0 2 0,
    homology_face_eq a m 4 hm 0 3 0, homology_face_eq a m 4 hm 0 4 0]
  simp only [sub_self,zero_add]
  exact face_H0_isIso a m 4 hm 0

lemma boundary_zero_H2_isIso (a m : ℕ) (hm : 35 ≤ m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 2).map (boundary a m 0)) := by
  have := boundary_zero_epi a m (by omega)
  have : IsIso (BoundedHomologyEdge.Hmap 0 (boundary a m 2)) :=
    boundary_two_H0_isIso a m (by omega)
  have : IsIso (BoundedHomologyEdge.Hmap 1 (boundary a m 2)) :=
    boundary_two_H1_isIso a m hm
  have : IsIso (BoundedHomologyEdge.Hmap 0 (boundary a m 4)) :=
    boundary_four_H0_isIso a m (by omega)
  exact BoundedHomologyEdge.chain_H2_isIso (boundary a m 0) (boundary a m 1)
    (boundary a m 2) (boundary a m 3) (boundary a m 4)
    (boundary_square a m 0) (boundary_square a m 1) (boundary_square a m 2)
    (boundary_square a m 3) (boundary_exact a m 0 (by omega) (by omega))
    (boundary_exact a m 1 (by omega) (by omega))
    (boundary_exact a m 2 (by omega) (by omega))
    (homology_boundary_two_zero a m (by omega) 2)
lemma stabilizer_H2_isIso (a m : ℕ) (hm : 35 ≤ m) (f : Configuration a m 1) :
    IsIso (TrivialHomology.map (MulAction.stabilizer (polygonFullGroup a m) f).subtype 2) := by
  have first := TransitiveInduction.isIso_map_pointMap f (fun g => transitive f g (by omega)) 2
  have second := boundary_zero_H2_isIso a m hm
  have third : IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 2).map
      (emptyIso a m).hom) := inferInstance
  rw [← augmentation_pointMap f 2]
  have composite := IsIso.comp_isIso' first (IsIso.comp_isIso' second third)
  exact composite

lemma stabilize_H2_isIso (a n : ℕ) (hn : 34 ≤ n) :
    IsIso (TrivialHomology.map (PolygonTracks.stabilize a 1 n) 2) := by
  rw [← standardStabilizerEquiv_subtype a 1 n, TrivialHomology.map_comp]
  have := TrivialHomology.isIso_equiv (standardStabilizerEquiv a 1 n) 2
  have := stabilizer_H2_isIso a (1+n) (by omega) (standard a 1 n)
  infer_instance
end SimpleAmenable.PolygonPlacement.Configuration

end

open Classical CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2

namespace TrivialHomology
variable (G : Type) [Group G]
lemma abelianization_fg [Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 1)] :
    Group.FG (Abelianization G) := by
  let e : groupHomology (Rep.trivial ℤ G ℤ) 1 ≃ₗ[ℤ] Additive (Abelianization G) :=
    (abelianizationEquiv G).toIntLinearEquiv
  have : Module.Finite ℤ (Additive (Abelianization G)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have : AddGroup.FG (Additive (Abelianization G)) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact GroupFG.iff_add_fg.mpr inferInstance

lemma abelianization_ring_noetherian
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 1)] :
    IsNoetherianRing (MonoidAlgebra ℤ (Abelianization G)) := by
  have := abelianization_fg G
  have : Algebra.FiniteType ℤ (MonoidAlgebra ℤ (Abelianization G)) :=
    MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  exact Algebra.FiniteType.isNoetherianRing ℤ _
end TrivialHomology

namespace PolygonTracks
noncomputable def abelianKernelEquiv (a m : ℕ) (hm : 5 ≤ m) :
    (Abelianization.of : polygonFullGroup a m →* Abelianization (polygonFullGroup a m)).ker ≃*
      polygonAlternatingGroup a m :=
  MulEquiv.subgroupCongr ((Abelianization.ker_of (polygonFullGroup a m)).trans (polygonFullGroup_commutator_eq a m hm))

lemma finite_alternating_H2_of_full (a m : ℕ) (hm : 205 < m)
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 1)]
    [Module.Finite ℤ (groupHomology (Rep.trivial ℤ (polygonFullGroup a m) ℤ) 2)] :
    Module.Finite ℤ (groupHomology.H2 (IntegralHomology.coefficients (polygonAlternatingGroup a m))) := by
  let f : polygonFullGroup a m →* Abelianization (polygonFullGroup a m) := Abelianization.of
  let e := abelianKernelEquiv a m (by omega)
  have : IsNoetherianRing (MonoidAlgebra ℤ (Abelianization (polygonFullGroup a m))) :=
    TrivialHomology.abelianization_ring_noetherian _
  have : Group.IsPerfect (polygonAlternatingGroup a m) := polygonAlternatingGroup_perfect a m (by omega)
  have : Group.IsPerfect f.ker := Group.IsPerfect.ofSurjective (f:=e.symm.toMonoidHom) e.symm.surjective
  have ha : ∀g : polygonFullGroup a m,
      TrivialHomology.map (QuotientRegular.conjugate f g).toMonoidHom 2 = 𝟙 _ := by
    intro g
    have := TrivialHomology.isIso_equiv e 2
    apply (cancel_mono (TrivialHomology.map e.toMonoidHom 2)).mp
    rw [Category.id_comp, ← TrivialHomology.map_comp]
    have he : e.toMonoidHom.comp (QuotientRegular.conjugate f g).toMonoidHom =
        (fullConjugation a m g).comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      apply Subtype.ext
      rfl
    rw [he,TrivialHomology.map_comp]
    have hg : TrivialHomology.map (fullConjugation a m g) 2=𝟙 _ := by
      apply ModuleCat.hom_ext
      exact fullAction_trivial a m hm g
    rw [hg,Category.comp_id]
  have : Module.Finite ℤ (groupHomology (Rep.trivial ℤ f.ker ℤ) 2) :=
    QuotientRegular.finite_kernel_H2 f (QuotientGroup.mk'_surjective _)
      (TrivialHomology.H1_isZero_of_perfect) ha
  have := TrivialHomology.isIso_equiv e 2
  exact Module.Finite.of_surjective (TrivialHomology.map e.toMonoidHom 2).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end PolygonTracks
end SimpleAmenable

end OAI
