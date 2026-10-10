import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.TransitiveCanonical
import OAI.GroupTheory.SimpleAmenable.Homology.BoundedHomologyEdge

namespace OAI

section

open CategoryTheory Representation Rep Finsupp
universe u
namespace HomologyAdditive
variable {k G H : Type u} [CommRing k] [Group G] [Group H]

lemma chainsMap_add (f : G →* H) {A : Rep.{u} k G} {B : Rep.{u} k H}
    (φ ψ : A ⟶ Rep.res f B) :
    groupHomology.chainsMap f (φ+ψ) = groupHomology.chainsMap f φ + groupHomology.chainsMap f ψ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change (groupHomology.chainsMap f (φ+ψ)).f n (single x a) =
    (groupHomology.chainsMap f φ).f n (single x a) +
    (groupHomology.chainsMap f ψ).f n (single x a)
  rw [groupHomology.chainsMap_f_single, groupHomology.chainsMap_f_single,
    groupHomology.chainsMap_f_single]
  change single _ (φ.hom a + ψ.hom a)=_
  exact Finsupp.single_add _ _ _

instance additive (n : ℕ) : (groupHomology.functor k G n).Additive where
  map_add {A B φ ψ} := by
    change HomologicalComplex.homologyMap (groupHomology.chainsMap (MonoidHom.id G) (φ+ψ)) n = _
    rw [chainsMap_add, HomologicalComplex.homologyMap_add]
    rfl

end HomologyAdditive

end

open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

namespace ConfigurationChains
variable {V : Type*}

lemma faceSum_ofFn (n : ℕ) (f : Fin (n+1) → V) :
    faceSum (List.ofFn f) = ∑i : Fin (n+1),
      Finsupp.single (List.ofFn (fun j => f (i.succAbove j))) ((-1:ℤ)^i.val) := by
  induction n with
  | zero => simp [List.ofFn_succ, faceSum]
  | succ n ih =>
    rw [List.ofFn_succ, faceSum, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, Fin.zero_succAbove,
      map_sum, cone_single]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finsupp.single_neg]
    congr 1
    · simp [List.ofFn_succ]
    · ring

noncomputable def boundaryRep {G : Type*} [Monoid G] [MulAction G V]
    {R : V → V → Prop} (hR : ∀g : G,∀v w,R v w → R (g • v) (g • w)) (n : ℕ) :
    Rep.of (representation hR (n+1)) ⟶ Rep.of (representation hR n) :=
  Rep.ofHom ⟨degreeBoundary R n, by
    intro g
    apply LinearMap.ext
    intro x
    exact (representation_boundary hR g n x).symm⟩
end ConfigurationChains

namespace PolygonPlacement.Configuration
attribute [local instance 1200] Rep.hV2
variable {a m p : ℕ}

noncomputable abbrev column (a m p : ℕ) :=
  Rep.of (TransitiveInduction.permutationRep
    (G:=polygonFullGroup a m) (X:=Configuration a m p))

noncomputable def face (i : Fin (p+1)) (f : Configuration a m (p+1)) :
    Configuration a m p :=
  ⟨fun j => f (i.succAbove j),fun j k hjk => f.property (by
    intro h
    exact hjk (Fin.succAbove_right_injective h))⟩

@[simp] lemma face_apply (i : Fin (p+1)) (f : Configuration a m (p+1)) (j : Fin p) :
    face i f j=f (i.succAbove j) := rfl

@[simp] lemma face_smul (i : Fin (p+1)) (g : polygonFullGroup a m)
    (f : Configuration a m (p+1)) : face i (g • f)=g • face i f := rfl

noncomputable def faceHom (a m p : ℕ) (i : Fin (p+1)) :
    column a m (p+1) ⟶ column a m p :=
  TransitiveInduction.equivariantMap (face i) (face_smul i)

noncomputable def boundary (a m p : ℕ) : column a m (p+1) ⟶ column a m p :=
  (representationIso a m (p+1)).hom ≫
    ConfigurationChains.boundaryRep (fun g v w h => (apart_smul_iff g v w).mpr h) p ≫
    (representationIso a m p).inv

lemma boundary_chain (c : Configuration a m (p+1) →₀ ℤ) :
    chainEquiv a m p ((boundary a m p).hom c) =
      ConfigurationChains.degreeBoundary (@Apart a m) p (chainEquiv a m (p+1) c) := by
  change chainEquiv a m p ((chainEquiv a m p).symm _) = _
  exact (chainEquiv a m p).apply_symm_apply _

lemma boundary_sum (a m p : ℕ) : boundary a m p =
    ∑i : Fin (p+1), ((-1:ℤ)^i.val) • faceHom a m p i := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro c z
  apply (chainEquiv a m p).injective
  change (chainEquiv a m p) ((boundary a m p).hom (Finsupp.single c z)) = _
  rw [boundary_chain]
  apply Subtype.ext
  change ConfigurationChains.boundary (chainEquiv a m (p+1) (Finsupp.single c z)).val = _
  rw [chainEquiv_single_val, ConfigurationChains.boundary_single,
    ConfigurationChains.faceSum_ofFn]
  simp only [Finset.smul_sum]
  change _ = (chainEquiv a m p
    ((∑i : Fin (p+1), ((-1:ℤ)^i.val) • faceHom a m p i).hom (Finsupp.single c z))).val
  simp only [Rep.sum_hom, Rep.smul_hom, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i hi
  change z • Finsupp.single _ ((-1:ℤ)^i.val) =
    ((-1:ℤ)^i.val) • ((chainEquiv a m p)
      ((faceHom a m p i).hom (Finsupp.single c z))).val
  dsimp only [faceHom]
  rw [TransitiveInduction.equivariantMap_single]
  rw [chainEquiv_single_val]
  simp [Finsupp.smul_single, mul_comm, face]

noncomputable def facePermutation (i j : Fin (p+1)) : Equiv.Perm (Fin (p+1)) :=
  (finSuccEquiv' i).trans (finSuccEquiv' j).symm

@[simp] lemma facePermutation_apply (i j : Fin (p+1)) (k : Fin p) :
    facePermutation i j (i.succAbove k)=j.succAbove k := by
  simp [facePermutation]

lemma permHom_centralizes (f : Configuration a m p) (σ : Equiv.Perm (Fin p))
    (h : MulAction.stabilizer (polygonFullGroup a m) f) :
    permHom f.val f.property σ * h.val = h.val * permHom f.val f.property σ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hh (i : Fin p) (y : GenericSquare a) : h.val.val (f i y)=f i y :=
    congrArg (fun t : Configuration a m p => t i y) h.property
  have hs : SupportedIn (permHom f.val f.property σ).val (Set.range (bank f.val f.property)) := by
    intro x hx
    apply perm_fixed
    intro i hi
    obtain ⟨y,rfl⟩ := hi
    exact hx ⟨(i,y),rfl⟩
  have he := supported_fixer_commute (f:=h.val.val) (by
    rintro x ⟨⟨i,y⟩,rfl⟩
    exact hh i y) hs
  exact congrArg (fun e : Equiv.Perm (TrackPoint a m) => e x) he.symm.eq

lemma permHom_face (f : Configuration a m (p+1)) (i j : Fin (p+1)) :
    permHom f.val f.property (facePermutation i j) • face i f=face j f := by
  apply ext
  intro k
  apply PolygonPlacement.ext
  intro x
  change (permHom f.val f.property (facePermutation i j)).val (f (i.succAbove k) x) =
    f (j.succAbove k) x
  rw [permHom_apply, facePermutation_apply]

lemma homology_face_eq (a m p : ℕ) (hm : 3*(p+1)+1 < m) (q : ℕ)
    (i j : Fin (p+1)) :
    (groupHomology.functor ℤ (polygonFullGroup a m) q).map (faceHom a m p i) =
      (groupHomology.functor ℤ (polygonFullGroup a m) q).map (faceHom a m p j) := by
  have hm' : p+1 ≤ m := by omega
  let f : Configuration a m (p+1) :=
    ⟨fun k => PolygonPlacement.standard (Fin.castLE hm' k),fun k l hkl =>
      standard_apart (fun he => hkl (Fin.castLE_injective hm' he))⟩
  exact TransitiveInduction.map_equivariant_eq_of_centralizer (face j) (face i)
    (face_smul j) (face_smul i) f (fun h => transitive f h hm)
    (permHom f.val f.property (facePermutation j i))
    (permHom_centralizes f _) (permHom_face f j i) q

lemma boundary_two (a m : ℕ) : boundary a m 1 = faceHom a m 1 0 - faceHom a m 1 1 := by
  rw [boundary_sum, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

lemma boundary_three (a m : ℕ) : boundary a m 2 =
    faceHom a m 2 0 - faceHom a m 2 1 + faceHom a m 2 2 := by
  rw [boundary_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
  norm_num
  abel

lemma homology_boundary_two_zero (a m : ℕ) (hm : 7 < m) (q : ℕ) :
    (groupHomology.functor ℤ (polygonFullGroup a m) q).map (boundary a m 1)=0 := by
  rw [boundary_two, Functor.map_sub, homology_face_eq a m 1 hm q 1 0, sub_self]

lemma homology_boundary_three (a m : ℕ) (hm : 10 < m) (q : ℕ) :
    (groupHomology.functor ℤ (polygonFullGroup a m) q).map (boundary a m 2)=
      (groupHomology.functor ℤ (polygonFullGroup a m) q).map (faceHom a m 2 0) := by
  rw [boundary_three, Functor.map_add, Functor.map_sub,
    homology_face_eq a m 2 hm q 1 0, homology_face_eq a m 2 hm q 2 0, sub_self, zero_add]

noncomputable def standardLE (a m p : ℕ) (hp : p ≤ m) : Configuration a m p :=
  ⟨fun k => PolygonPlacement.standard (Fin.castLE hp k),fun _ _ hkl =>
    standard_apart (fun he => hkl (Fin.castLE_injective hp he))⟩

lemma boundary_square (a m p : ℕ) : boundary a m (p+1) ≫ boundary a m p=0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  apply (chainEquiv a m p).injective
  change chainEquiv a m p ((boundary a m p).hom ((boundary a m (p+1)).hom c)) =
    chainEquiv a m p 0
  rw [boundary_chain, boundary_chain, ConfigurationChains.degreeBoundary_square, map_zero]

lemma boundary_exact (a m p : ℕ) (hm : 33 ≤ m) (hp : p ≤ 2) :
    (ShortComplex.mk (boundary a m (p+1)) (boundary a m p) (boundary_square a m p)).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{0} ℤ (polygonFullGroup a m))
    (ModuleCat.{0} ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (boundary a m p).hom x=0 at hx
  have hc : ConfigurationChains.degreeBoundary (@Apart a m) p (chainEquiv a m (p+1) x)=0 := by
    rw [← boundary_chain, hx, map_zero]
  obtain ⟨y,hy⟩ := (configuration_lowDegree_exact hm hp _).mp hc
  refine ⟨(chainEquiv a m (p+2)).symm y,?_⟩
  apply (chainEquiv a m (p+1)).injective
  change chainEquiv a m (p+1) ((boundary a m (p+1)).hom _) = _
  rw [boundary_chain, LinearEquiv.apply_symm_apply, hy]

lemma boundary_zero_eq_face (a m : ℕ) : boundary a m 0=faceHom a m 0 0 := by
  rw [boundary_sum]
  simp

lemma boundary_zero_epi (a m : ℕ) (hm : 0 < m) : Epi (boundary a m 0) := by
  rw [boundary_zero_eq_face, Rep.epi_iff_surjective]
  change Function.Surjective (Finsupp.mapDomain (face (0:Fin 1)))
  apply Finsupp.mapDomain_surjective
  intro f
  refine ⟨standardLE a m 1 (by omega),?_⟩
  apply ext
  intro i
  exact Fin.elim0 i

lemma face_H0_isIso (a m p : ℕ) (hm : 3*(p+1)+1 < m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 0).map (faceHom a m p i)) := by
  let f := standardLE a m (p+1) (by omega : p+1 ≤ m)
  exact TransitiveInduction.isIso_map_equivariant_H0 (face i) (face_smul i) f
    (fun h => transitive f h hm) (fun h => transitive _ h (by omega))

lemma boundary_two_H0_isIso (a m : ℕ) (hm : 10 < m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 0).map (boundary a m 2)) := by
  rw [homology_boundary_three a m hm 0]
  exact face_H0_isIso a m 2 hm 0
lemma boundary_zero_H1_isIso (a m : ℕ) (hm : 33 ≤ m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map (boundary a m 0)) := by
  let boundaryEpi := boundary_zero_epi a m (by omega)
  let boundaryIso : IsIso (BoundedHomologyEdge.Hmap 0 (boundary a m 2)) :=
    boundary_two_H0_isIso a m (by omega)
  exact BoundedHomologyEdge.chain_H1_isIso (boundary a m 0) (boundary a m 1)
    (boundary a m 2) (boundary_square a m 0) (boundary_square a m 1)
    (boundary_exact a m 0 hm (by omega)) (boundary_exact a m 1 hm (by omega))
    (homology_boundary_two_zero a m (by omega) 1)

end PolygonPlacement.Configuration
end SimpleAmenable

end OAI
