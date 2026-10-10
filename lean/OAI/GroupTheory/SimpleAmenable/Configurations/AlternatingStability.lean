import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonAlternatingStabilization
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonAlternatingConfigurations
import OAI.GroupTheory.SimpleAmenable.Configurations.StabilizationComposition
import OAI.GroupTheory.SimpleAmenable.Homology.PermutationAugmentation

namespace OAI

section

section

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2
namespace PolygonPlacement.Configuration
variable {a m p n : ℕ}

lemma stabilizeAlternating_smul_standard (g : polygonAlternatingGroup a n) :
    PolygonTracks.stabilizeAlternating a p n g • standard a p n=standard a p n := by
  apply ext
  intro i
  apply PolygonPlacement.ext
  intro x
  exact PolygonTracks.stabilize_left g.val (i,x)

noncomputable def alternatingRestrict (a p n : ℕ) (hn : 32 ≤ n)
    (g : MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n)) :
    polygonAlternatingGroup a n := by
  have hg : g.val.val∈PolygonTracks.bankFixer a p n := by
    have hh := g.property
    exact (show g.val ∈ (PolygonTracks.bankFixer a p n).comap
      (polygonAlternatingGroup a (p+n)).subtype from
        (alternating_stabilizer_standard a p n) ▸ hh)
  refine ⟨PolygonTracks.restrict ⟨g.val.val,hg⟩,?_⟩
  rw [← PolygonTracks.stabilize_alternating_comap a p n hn]
  change PolygonTracks.stabilize a p n (PolygonTracks.restrict _)∈polygonAlternatingGroup a (p+n)
  rw [PolygonTracks.stabilize_restrict]
  exact g.val.property

noncomputable def alternatingStabilizerEquiv (a p n : ℕ) (hn : 32 ≤ n) :
    polygonAlternatingGroup a n ≃*
      MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n) where
  toFun g := ⟨PolygonTracks.stabilizeAlternating a p n g,stabilizeAlternating_smul_standard g⟩
  invFun := alternatingRestrict a p n hn
  left_inv g := by
    apply Subtype.ext
    change PolygonTracks.restrict ⟨PolygonTracks.stabilize a p n g.val,_⟩=g.val
    exact PolygonTracks.restrict_stabilize g.val
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change PolygonTracks.stabilize a p n (PolygonTracks.restrict _) = g.val.val
    exact PolygonTracks.stabilize_restrict _
  map_mul' g h := Subtype.ext ((PolygonTracks.stabilizeAlternating a p n).map_mul g h)

lemma alternatingStabilizerEquiv_subtype (a p n : ℕ) (hn : 32 ≤ n) :
    (MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n)).subtype.comp
      (alternatingStabilizerEquiv a p n hn).toMonoidHom=PolygonTracks.stabilizeAlternating a p n := rfl

lemma alternatingStabilizer_perfect (a p n : ℕ) (hn : 32 ≤ n) :
    Group.IsPerfect (MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n)) := by
  have := polygonAlternatingGroup_perfect a n (by omega)
  exact Group.IsPerfect.ofSurjective (f:=(alternatingStabilizerEquiv a p n hn).toMonoidHom)
    (alternatingStabilizerEquiv a p n hn).surjective

noncomputable abbrev altColumn (a m p : ℕ) :=
  Rep.res (polygonAlternatingGroup a m).subtype (column a m p)
noncomputable abbrev altFaceHom (a m p : ℕ) (i : Fin (p+1)) :
    altColumn a m (p+1) ⟶ altColumn a m p :=
  (Rep.resFunctor (polygonAlternatingGroup a m).subtype).map (faceHom a m p i)
noncomputable abbrev altBoundary (a m p : ℕ) : altColumn a m (p+1) ⟶ altColumn a m p :=
  (Rep.resFunctor (polygonAlternatingGroup a m).subtype).map (boundary a m p)

lemma altBoundary_square (a m p : ℕ) : altBoundary a m (p+1) ≫ altBoundary a m p=0 := by
  rw [← Functor.map_comp, boundary_square, Functor.map_zero]

lemma altBoundary_exact (a m p : ℕ) (hm : 33 ≤ m) (hp : p ≤ 2) :
    (ShortComplex.mk (altBoundary a m (p+1)) (altBoundary a m p) (altBoundary_square a m p)).Exact := by
  exact (Rep.res_map_exact (polygonAlternatingGroup a m).subtype
    (ShortComplex.mk (boundary a m (p+1)) (boundary a m p) (boundary_square a m p))).mpr
      (boundary_exact a m p hm hp)

lemma altBoundary_zero_epi (a m : ℕ) (hm : 0 < m) : Epi (altBoundary a m 0) := by
  rw [Rep.epi_iff_surjective]
  exact (Rep.epi_iff_surjective (boundary a m 0)).mp (boundary_zero_epi a m hm)

lemma altFace_H0_eq (a m p : ℕ) (hm : 3*p+1 < m) (i j : Fin (p+1)) :
    (groupHomology.functor ℤ (polygonAlternatingGroup a m) 0).map (altFaceHom a m p i)=
      (groupHomology.functor ℤ (polygonAlternatingGroup a m) 0).map (altFaceHom a m p j) := by
  let f := standardLE a m p (by omega : p ≤ m)
  exact TransitiveInduction.map_equivariant_H0_eq (G:=polygonAlternatingGroup a m)
    (face i) (face j) (fun g x => face_smul i g.val x) (fun g x => face_smul j g.val x)
    f (fun g => alternating_transitive f g hm)

lemma altFace_H0_isIso (a m p : ℕ) (hm : 3*(p+1)+1 < m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (polygonAlternatingGroup a m) 0).map (altFaceHom a m p i)) := by
  let f := standardLE a m (p+1) (by omega : p+1 ≤ m)
  exact TransitiveInduction.isIso_map_equivariant_H0 (G:=polygonAlternatingGroup a m)
    (face i) (fun g x => face_smul i g.val x) f
      (fun g => alternating_transitive f g hm) (fun g => alternating_transitive _ g (by omega))

lemma altBoundary_two_H0_isIso (a m : ℕ) (hm : 10 < m) :
    IsIso ((groupHomology.functor ℤ (polygonAlternatingGroup a m) 0).map (altBoundary a m 2)) := by
  have he : altBoundary a m 2=altFaceHom a m 2 0-altFaceHom a m 2 1+altFaceHom a m 2 2 := by
    change (Rep.resFunctor _).map (boundary a m 2)=_
    rw [boundary_three, Functor.map_add, Functor.map_sub]
  rw [he, Functor.map_add, Functor.map_sub,
    altFace_H0_eq a m 2 (by omega) 1 0, altFace_H0_eq a m 2 (by omega) 2 0,
    sub_self,zero_add]
  exact altFace_H0_isIso a m 2 hm 0

lemma altColumn_H1_isZero (a p n : ℕ) (hn : 32 ≤ n) (hm : 3*p+1 < p+n) :
    IsZero (groupHomology (altColumn a (p+n) p) 1) := by
  have := alternatingStabilizer_perfect a p n hn
  exact (TrivialHomology.H1_isZero_of_perfect
    (G:=MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n))).of_iso
      (alternatingOrbitHomologyIso a p n hm 1)

lemma altBoundary_zero_H2_epi (a m : ℕ) (hm : 34 ≤ m) :
    Epi ((groupHomology.functor ℤ (polygonAlternatingGroup a m) 2).map (altBoundary a m 0)) := by
  have := altBoundary_zero_epi a m (by omega)
  have : IsIso (BoundedHomologyEdge.Hmap 0 (altBoundary a m 2)) :=
    altBoundary_two_H0_isIso a m (by omega)
  have hz : IsZero (groupHomology (altColumn a m 2) 1) := by
    have he : m=2+(m-2) := by omega
    rw [he]
    exact altColumn_H1_isZero a 2 (m-2) (by omega) (by omega)
  exact BoundedHomologyEdge.chain_H2_epi (altBoundary a m 0) (altBoundary a m 1)
    (altBoundary a m 2) (altBoundary_square a m 0) (altBoundary_square a m 1)
    (altBoundary_exact a m 0 (by omega) (by omega))
    (altBoundary_exact a m 1 (by omega) (by omega)) hz

end PolygonPlacement.Configuration
end SimpleAmenable

end

end

end OAI
