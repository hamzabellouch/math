import OAI.GroupTheory.Congruence.Coinvariants
import OAI.GroupTheory.Congruence.Stabilization

namespace OAI

noncomputable section

/-!
Permutation orbit parameters, locally finite odd groups, quotient coinvariants, and bar augmentations.
-/

namespace CoboundaryExpanders.FinsuppPermutation
open CategoryTheory

variable {k G X Y : Type} [CommRing k] [Group G] [MulAction G X]

structure OrbitParam (G X Y : Type) [Group G] [MulAction G X] where
  f : X → Y
  invariant : ∀ (g : G) (x : X), f (g • x) = f x
  surjective : Function.Surjective f
  fiber : ∀ x y, f x = f y → ∃ g : G, g • x = y

namespace OrbitParam
variable (P : OrbitParam G X Y)
def toCoin : (ρ k G X).Coinvariants →ₗ[k] (Y →₀ k) :=
  Representation.Coinvariants.lift _ (Finsupp.lmapDomain k k P.f) (by
    intro g
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    simp [ρ_single, P.invariant])
@[simp] lemma toCoin_mk (c : X →₀ k) :
    P.toCoin (Representation.Coinvariants.mk (ρ k G X) c) = Finsupp.lmapDomain k k P.f c := rfl

def chosen (y : Y) : X := (P.surjective y).choose
@[simp] lemma chosen_spec (y : Y) : P.f (P.chosen y) = y := (P.surjective y).choose_spec

def fromCoin : (Y →₀ k) →ₗ[k] (ρ k G X).Coinvariants :=
  Finsupp.linearCombination k (fun y =>
    Representation.Coinvariants.mk (ρ k G X) (Finsupp.single (P.chosen y) 1))
@[simp] lemma fromCoin_single (y : Y) (r : k) :
    P.fromCoin (Finsupp.single y r) =
      Representation.Coinvariants.mk (ρ k G X) (Finsupp.single (P.chosen y) r) := by
  simp [fromCoin, ← map_smul]

lemma mk_eq (x y : X) (h : P.f x = P.f y) (r : k) :
    Representation.Coinvariants.mk (ρ k G X) (Finsupp.single x r) =
      Representation.Coinvariants.mk (ρ k G X) (Finsupp.single y r) := by
  obtain ⟨g,hg⟩ := P.fiber x y h
  rw [← hg, ← ρ_single]
  exact (Representation.Coinvariants.mk_self_apply _ _ _).symm

lemma from_to : (P.fromCoin (k := k)).comp P.toCoin = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro r
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, toCoin_mk,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, fromCoin_single, LinearMap.id_apply]
  exact P.mk_eq _ _ (P.chosen_spec _) r
lemma to_from : (P.toCoin (k := k)).comp P.fromCoin = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro y
  apply LinearMap.ext
  intro r
  simp

def coinEquiv : (ρ k G X).Coinvariants ≃ₗ[k] (Y →₀ k) :=
  LinearEquiv.ofLinearMap P.toCoin P.fromCoin P.to_from P.from_to
@[simp] lemma coinEquiv_mk (c : X →₀ k) :
    P.coinEquiv (Representation.Coinvariants.mk (ρ k G X) c) =
      Finsupp.lmapDomain k k P.f c := rfl

def H0Equiv : groupHomology (rep k G X) 0 ≃ₗ[k] (Y →₀ k) :=
  (groupHomology.H0Iso (rep k G X)).toLinearEquiv.trans P.coinEquiv

lemma H0_naturality {X' Y' : Type} [MulAction G X'] (Q : OrbitParam G X' Y')
    (d : rep k G X ⟶ rep k G X') (e : (Y →₀ k) →ₗ[k] (Y' →₀ k))
    (he : (Finsupp.lmapDomain k k Q.f).comp d.hom.toLinearMap =
      e.comp (Finsupp.lmapDomain k k P.f)) (x : groupHomology (rep k G X) 0) :
    Q.H0Equiv ((groupHomology.functor k G 0).map d x) = e (P.H0Equiv x) := by
  have hc : Q.coinEquiv.toLinearMap.comp
      (Representation.Coinvariants.map _ _ d.hom) = e.comp P.coinEquiv.toLinearMap := by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro c
    change Q.coinEquiv (Representation.Coinvariants.mk (ρ k G X') (d.hom c)) =
      e (P.coinEquiv (Representation.Coinvariants.mk (ρ k G X) c))
    rw [coinEquiv_mk,coinEquiv_mk]
    exact LinearMap.congr_fun he c
  have hn := congrArg (fun z => z x) (groupHomology.map_id_comp_H0Iso_hom d)
  change (groupHomology.H0Iso (rep k G X')).hom
      ((groupHomology.functor k G 0).map d x) =
    (Rep.coinvariantsFunctor k G).map d ((groupHomology.H0Iso (rep k G X)).hom x) at hn
  change Q.coinEquiv ((groupHomology.H0Iso (rep k G X')).hom _) = _
  rw [hn]
  exact LinearMap.congr_fun hc ((groupHomology.H0Iso (rep k G X)).hom x)
end OrbitParam
end CoboundaryExpanders.FinsuppPermutation


section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.Complex
variable {V W : Type} [DecidableEq V] [DecidableEq W]

structure Reduction (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W) where
  f : V → W
  injOn : ∀ s ∈ X.faces, Set.InjOn f (s : Set V)
  faces : ∀ s ∈ X.faces, s.image f ∈ Y.faces

namespace Reduction
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (r : Reduction X Y)

def face (n : ℕ) (s : X.Face n) : Y.Face n :=
  ⟨s.val.image r.f, r.faces s.val s.property.1,
    (Finset.card_image_of_injOn (r.injOn s.val s.property.1)).trans s.property.2⟩

def chains (n : ℕ) : X.Chains n →ₗ[k] Y.Chains n :=
  Finsupp.lmapDomain k k (r.face n)

omit [DecidableEq V] in
@[simp] lemma chains_single (n : ℕ) (s : X.Face n) (a : k) :
    r.chains n (Finsupp.single s a) = Finsupp.single (r.face n s) a :=
  Finsupp.mapDomain_single

lemma image_erase (s : Finset V) (hs : s ∈ X.faces) (v : V) (hv : v ∈ s) :
    (s.erase v).image r.f = (s.image r.f).erase (r.f v) := by
  ext w
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨u,⟨huv,hu⟩,rfl⟩
    exact ⟨fun h => huv (r.injOn s hs hu hv h),u,hu,rfl⟩
  · rintro ⟨hw, u,hu,rfl⟩
    exact ⟨u,⟨fun h => hw (congrArg r.f h),hu⟩,rfl⟩

lemma raw_boundary (s : Finset V) (hs : s ∈ X.faces) (a : k) :
    Finsupp.lmapDomain k k (fun t : Finset V => t.image r.f)
      (rawBoundary (Finsupp.single s a)) =
    rawBoundary (Finsupp.single (s.image r.f) a) := by
  simp only [rawBoundary_single, map_sum, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  rw [Finset.sum_image (r.injOn s hs)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [r.image_erase s hs v hv]

omit [DecidableEq V] in
lemma embed_chains (n : ℕ) :
    (Y.embed n).comp (r.chains n) =
      (Finsupp.lmapDomain k k (fun t : Finset V => t.image r.f)).comp (X.embed n) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply,Finsupp.lsingle_apply,chains_single,embed_single,
    Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rfl

lemma boundary (n : ℕ) :
    (r.chains n).comp (X.boundary n) = (Y.boundary n).comp (r.chains (n+1)) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  apply Y.embed_injective n
  change (Y.embed n).comp (r.chains n) (X.boundary n (Finsupp.single s a)) =
    (Y.embed n).comp (Y.boundary n) (r.chains (n+1) (Finsupp.single s a))
  rw [embed_chains,embed_boundary]
  change Finsupp.lmapDomain k k (fun t : Finset V => t.image r.f)
    ((X.embed n).comp (X.boundary n) (Finsupp.single s a)) =
    rawBoundary ((Y.embed (n+1)).comp (r.chains (n+1)) (Finsupp.single s a))
  rw [embed_boundary,embed_chains]
  simp only [LinearMap.comp_apply,embed_single,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  exact r.raw_boundary s.val s.property.1 a

omit [DecidableEq V] in
lemma sum_chains (n : ℕ) : (Y.sumCoefficients n).comp (r.chains n) = X.sumCoefficients n := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp
end Reduction
end CoboundaryExpanders.InfiniteChains.Complex

namespace CoboundaryExpanders.LocallyFiniteOdd
open Representation
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

lemma coinvariant_relation_support (ρ : Representation (ZMod 2) G V)
    (x : V) (hx : x ∈ Coinvariants.ker ρ) :
    ∃ s : Finset G, ∀ S : Subgroup G, (∀ g ∈ s, g ∈ S) →
      x ∈ Coinvariants.ker (ρ.comp S.subtype) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g,v⟩,rfl⟩ := hx
    refine ⟨{g},fun S hS => ?_⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp S.subtype) ⟨g,hS g (by simp)⟩ v
  | zero => exact ⟨∅,fun _ _ => Submodule.zero_mem _⟩
  | add x y hx hy ex ey =>
    obtain ⟨s,hs⟩ := ex
    obtain ⟨t,ht⟩ := ey
    refine ⟨s ∪ t,fun S hS => (Coinvariants.ker _).add_mem ?_ ?_⟩
    · exact hs S (fun g hg => hS g (Finset.mem_union_left _ hg))
    · exact ht S (fun g hg => hS g (Finset.mem_union_right _ hg))
  | smul a x hx ex =>
    obtain ⟨s,hs⟩ := ex
    exact ⟨s,fun S hS => (Coinvariants.ker _).smul_mem a (hs S hS)⟩

lemma norm_zero_of_relation [Fintype G] (ρ : Representation (ZMod 2) G V)
    (x : V) (hx : x ∈ Coinvariants.ker ρ) : ρ.norm x = 0 := by
  have h : Coinvariants.ker ρ ≤ LinearMap.ker ρ.norm := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change ρ.norm (ρ g v - v) = 0
    rw [map_sub,Representation.norm_self_apply,sub_self]
  exact h hx

lemma coinvariant_norm_subgroup (ρ : Representation (ZMod 2) G V)
    (S : Subgroup G) [Fintype S] (hodd : Odd (Fintype.card S)) (v : V) :
    Coinvariants.mk ρ (Representation.norm (ρ.comp S.subtype) v) = Coinvariants.mk ρ v := by
  have hcard : (Fintype.card S : ZMod 2) = 1 := by
    obtain ⟨a,ha⟩ := hodd
    rw [ha]
    have ht : (2 : ZMod 2) = 0 := by decide
    simp [Nat.cast_add,Nat.cast_mul,ht]
  simp only [Representation.norm,LinearMap.sum_apply,map_sum]
  have he (s : S) : Coinvariants.mk ρ ((ρ.comp S.subtype) s v) = Coinvariants.mk ρ v :=
    Coinvariants.mk_self_apply ρ s.val v
  simp only [he,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2),hcard,one_smul]

theorem coinvariants_map_injective
    (H : ∀ s : Finset G, ∃ S : Subgroup G, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)
    (ρ : Representation (ZMod 2) G V) (τ : Representation (ZMod 2) G W)
    (f : ρ.IntertwiningMap τ) (hf : Function.Injective f) :
    Function.Injective (Coinvariants.map ρ τ f) := by
  classical
  have hz : ∀ c, Coinvariants.map ρ τ f c = 0 → c = 0 := by
    intro c
    induction c using Coinvariants.induction_on with
    | h v =>
      intro hv
      rw [Coinvariants.map_mk] at hv
      obtain ⟨s,hs⟩ := coinvariant_relation_support τ (f v) ((Coinvariants.mk_eq_zero τ).mp hv)
      obtain ⟨S,hfin,hodd,hS⟩ := H s
      have : Finite S := hfin
      let : Fintype S := Fintype.ofFinite S
      have hzero : Representation.norm (τ.comp S.subtype) (f v) = 0 :=
        norm_zero_of_relation _ _ (hs S hS)
      have hnorm : f (Representation.norm (ρ.comp S.subtype) v) = Representation.norm (τ.comp S.subtype) (f v) := by
        simp only [Representation.norm,LinearMap.sum_apply,map_sum]
        apply Finset.sum_congr rfl
        intro s _
        exact LinearMap.congr_fun (f.isIntertwining' s.val) v
      have hvan : Representation.norm (ρ.comp S.subtype) v = 0 := by
        apply hf
        rw [hnorm,hzero,map_zero]
      rw [← coinvariant_norm_subgroup ρ S (by simpa only [Fintype.card_eq_nat_card] using hodd) v,hvan,map_zero]
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub,hab,sub_self]

end CoboundaryExpanders.LocallyFiniteOdd

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.LocallyFiniteOdd
variable {G : Type} [Group G]

theorem coinvariants_preserves_monomorphisms
    (H : ∀ s : Finset G, ∃ S : Subgroup G, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) :
    (Rep.coinvariantsFunctor (ZMod 2) G).PreservesMonomorphisms where
  preserves f hf := by
    apply (ModuleCat.mono_iff_injective _).mpr
    exact coinvariants_map_injective H _ _ f.hom ((Rep.mono_iff_injective f).mp hf)

theorem coinvariants_preserves_homology
    (H : ∀ s : Finset G, ∃ S : Subgroup G, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) :
    (Rep.coinvariantsFunctor (ZMod 2) G).PreservesHomology := by
  let := coinvariants_preserves_monomorphisms H
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

end CoboundaryExpanders.LocallyFiniteOdd

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation

namespace CoboundaryExpanders.QuotientCoinvariants

section
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

abbrev L := Rep.quotientToCoinvariantsFunctor (ZMod 2) N
abbrev R := Rep.resFunctor (QuotientGroup.mk' N) (k := ZMod 2)

noncomputable def homTo {X : Rep (ZMod 2) G} {Y : Rep (ZMod 2) (G ⧸ N)}
    (f : (L N).obj X ⟶ Y) : X ⟶ (R N).obj Y :=
  Rep.ofHom ⟨f.hom.toLinearMap ∘ₗ Coinvariants.mk (X.ρ.comp N.subtype), by
    intro g
    ext x
    exact LinearMap.congr_fun (f.hom.isIntertwining' (QuotientGroup.mk' N g))
      (Coinvariants.mk _ x)⟩

noncomputable def homFrom {X : Rep (ZMod 2) G} {Y : Rep (ZMod 2) (G ⧸ N)}
    (f : X ⟶ (R N).obj Y) : (L N).obj X ⟶ Y := by
  let h (s : N) : f.hom.toLinearMap ∘ₗ (X.ρ.comp N.subtype) s = f.hom.toLinearMap := by
    ext x
    have he := LinearMap.congr_fun (f.hom.isIntertwining' s.val) x
    have hs : QuotientGroup.mk' N s.val = 1 := by simp
    change f.hom.toLinearMap (X.ρ s.val x) = Y.ρ (QuotientGroup.mk' N s.val) (f.hom.toLinearMap x) at he
    change f.hom.toLinearMap (X.ρ s.val x) = f.hom.toLinearMap x
    rw [hs,map_one,Module.End.one_apply] at he
    exact he
  let m : Coinvariants (X.ρ.comp N.subtype) →ₗ[ZMod 2] Y :=
    Coinvariants.lift _ f.hom.toLinearMap h
  refine Rep.ofHom ⟨m,fun g => ?_⟩
  refine QuotientGroup.induction_on g (fun g => ?_)
  apply Coinvariants.hom_ext
  ext x
  exact LinearMap.congr_fun (f.hom.isIntertwining' g) x

noncomputable def homEquiv (X : Rep (ZMod 2) G) (Y : Rep (ZMod 2) (G ⧸ N)) :
    ((L N).obj X ⟶ Y) ≃ (X ⟶ (R N).obj Y) where
  toFun := homTo N
  invFun := homFrom N
  left_inv f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Coinvariants.hom_ext
    rfl
  right_inv f := by
    ext x
    rfl

noncomputable def adjunction : L N ⊣ R N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv N
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply Coinvariants.hom_ext
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        ext x
        rfl }

instance : (L N).Additive where
  map_add := by
    intro X Y f g
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Coinvariants.hom_ext
    rfl

instance : (L N).IsLeftAdjoint := (adjunction N).isLeftAdjoint

instance : (L N).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms (adjunction N)

end

section
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

include H

theorem preservesMonomorphisms : (L N).PreservesMonomorphisms where
  preserves f hf := by
    apply (Rep.mono_iff_injective _).mpr
    exact LocallyFiniteOdd.coinvariants_map_injective H _ _
      ((Rep.resFunctor N.subtype).map f).hom ((Rep.mono_iff_injective f).mp hf)

theorem preservesHomology : (L N).PreservesHomology := by
  let := preservesMonomorphisms N H
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

noncomputable def descendedResolution {X : Rep.{0} (ZMod 2) G}
    (P : ProjectiveResolution X) : ProjectiveResolution ((L N).obj X) := by
  letI := preservesHomology N H
  exact (L N).mapProjectiveResolution P

end

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

noncomputable def inflatedTrivialIso :
    Rep.trivialFunctor (ZMod 2) (G ⧸ N) ⋙ R N ≅ Rep.trivialFunctor (ZMod 2) G :=
  NatIso.ofComponents (fun X => Iso.refl _) (by intro X Y f; rfl)

noncomputable def totalAdjunction :
    L N ⋙ Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N) ⊣ Rep.trivialFunctor (ZMod 2) G :=
  ((adjunction N).comp (Rep.coinvariantsAdjunction (ZMod 2) (G ⧸ N))).ofNatIsoRight
    (inflatedTrivialIso N)

noncomputable def totalCoinvariantsIso :
    L N ⋙ Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N) ≅ Rep.coinvariantsFunctor (ZMod 2) G :=
  Adjunction.leftAdjointUniq (totalAdjunction N) (Rep.coinvariantsAdjunction (ZMod 2) G)

lemma totalCoinvariantsIso_double_mk (X : Rep (ZMod 2) G) (x : X) :
    ((totalCoinvariantsIso N).hom.app X).hom
      (Coinvariants.mk (((L N).obj X).ρ) (Coinvariants.mk (X.ρ.comp N.subtype) x)) =
      Coinvariants.mk X.ρ x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (totalAdjunction N) (Rep.coinvariantsAdjunction (ZMod 2) G) X
  exact LinearMap.congr_fun (congrArg (fun f => f.hom.toLinearMap) h) x

noncomputable def trivialIso :
    (L N).obj (Rep.trivial (ZMod 2) G (ZMod 2)) ≅ Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2) where
  hom := homFrom N (𝟙 _)
  inv := Rep.ofHom ⟨Coinvariants.mk ((Rep.trivial (ZMod 2) G (ZMod 2)).ρ.comp N.subtype), by
    intro g
    refine QuotientGroup.induction_on g (fun g => ?_)
    rfl⟩
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Coinvariants.hom_ext
    rfl
  inv_hom_id := by
    ext
    rfl

end CoboundaryExpanders.QuotientCoinvariants

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory

namespace CoboundaryExpanders.QuotientCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

noncomputable def quotientResolution [DecidableEq G] :
    ProjectiveResolution (Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2)) where
  complex := (descendedResolution N H (Rep.barResolution (ZMod 2) G)).complex
  projective := (descendedResolution N H (Rep.barResolution (ZMod 2) G)).projective
  π := (descendedResolution N H (Rep.barResolution (ZMod 2) G)).π ≫
    (ChainComplex.single₀ _).map (trivialIso N).hom

noncomputable def homologyIso [DecidableEq G] [DecidableEq (G ⧸ N)] (n : ℕ) :
    groupHomology (Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2)) n ≅
      groupHomology (Rep.trivial (ZMod 2) G (ZMod 2)) n := by
  let CQ := Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N)
  let CG := Rep.coinvariantsFunctor (ZMod 2) G
  let P := quotientResolution N H
  let eQ := (NatIso.mapHomologicalComplex
    (Functor.isoWhiskerRight (leftUnitorNatIso (Rep (ZMod 2) (G ⧸ N))) CQ) _).app P.complex
  let eT := (NatIso.mapHomologicalComplex (totalCoinvariantsIso N) _).app (Rep.barComplex (ZMod 2) G)
  let eG := groupHomology.inhomogeneousChainsIso (Rep.trivial (ZMod 2) G (ZMod 2)) ≪≫
    (NatIso.mapHomologicalComplex
      (Functor.isoWhiskerRight (leftUnitorNatIso (Rep (ZMod 2) G)) CG) _).app (Rep.barComplex (ZMod 2) G)
  let h := HomologicalComplex.homologyFunctor (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) n
  exact groupHomologyIso (Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2)) n P ≪≫
    h.mapIso eQ ≪≫ h.mapIso eT ≪≫ (h.mapIso eG).symm

end CoboundaryExpanders.QuotientCoinvariants

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp

namespace CoboundaryExpanders.QuotientCoinvariants
variable {G : Type} [Group G] [DecidableEq G] (N : Subgroup G) [N.Normal]

noncomputable def quotientBarF (n : ℕ) :
    (Rep.barComplex (ZMod 2) G).X n ⟶
      (R N).obj ((Rep.barComplex (ZMod 2) (G ⧸ N)).X n) :=
  Rep.freeLift (ZMod 2) G _ (fun x : Fin n → G =>
    Finsupp.single (fun i => QuotientGroup.mk' N (x i)) (.single (1 : G ⧸ N) (1 : ZMod 2)))

omit [DecidableEq G] in
@[simp] theorem quotientBarF_single (n : ℕ) (x : Fin n → G) (g : G) (r : ZMod 2) :
    (quotientBarF N n).hom (Finsupp.single x (.single g r)) =
      Finsupp.single (fun i => QuotientGroup.mk' N (x i)) (.single (QuotientGroup.mk' N g) r) := by
  change (Representation.freeLift
    ((Representation.free (ZMod 2) (G ⧸ N) (Fin n → G ⧸ N)).comp (QuotientGroup.mk' N))
    (fun x : Fin n → G => Finsupp.single (fun i => QuotientGroup.mk' N (x i))
      (.single (1 : G ⧸ N) (1 : ZMod 2))))
    (Finsupp.single x (.single g r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free (ZMod 2) (G ⧸ N) (Fin n → G ⧸ N) (QuotientGroup.mk' N g) _ = _
  rw [Representation.free_single_single]
  simp

noncomputable def quotientBar [DecidableEq (G ⧸ N)] :
    ((L N).mapHomologicalComplex _).obj (Rep.barComplex (ZMod 2) G) ⟶
      Rep.barComplex (ZMod 2) (G ⧸ N) where
  f n := homFrom N (quotientBarF N n)
  comm' i j hij := by
    cases hij
    apply (homEquiv N _ _).injective
    apply Rep.free_ext
    intro x
    change ((Rep.barComplex (ZMod 2) (G ⧸ N)).d (j + 1) j).hom
      ((quotientBarF N (j + 1)).hom (Finsupp.single x (.single 1 1))) =
      (quotientBarF N j).hom
      (((Rep.barComplex (ZMod 2) G).d (j + 1) j).hom (Finsupp.single x (.single 1 1)))
    rw [Rep.barComplex.d_def,Rep.barComplex.d_def,quotientBarF_single]
    simp only [map_one]
    rw [Rep.barComplex.d_single,Rep.barComplex.d_single]
    have hq : ∀ (n : ℕ) (x : Fin n → G) (g : G) (r : ZMod 2),
        (quotientBarF N n).hom (Finsupp.single x (.single g r)) =
          Finsupp.single (fun i => QuotientGroup.mk' N (x i)) (.single (QuotientGroup.mk' N g) r) :=
      quotientBarF_single N
    simp only [map_add,map_sum,hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    exact (Fin.comp_contractNth (· * ·) (· * ·) (fun a b : G => (map_mul (QuotientGroup.mk' N) a b).symm) i x).symm

end CoboundaryExpanders.QuotientCoinvariants

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct

namespace CoboundaryExpanders.QuotientBarAugmentation
variable {k G : Type} [CommRing k] [Group G] [DecidableEq G]
omit [DecidableEq G] in
lemma diagonal_inv_single (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G n).inv.hom (single x (.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd x) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (single x (.single g r)) = .single g 1 ⊗ₜ[k] .single x r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r
  rw [step1]
  simp only [Action.tensorObj_V, tensor_V, tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, x) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g x 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by
      rw [one_mul]
      exact congrArg (fun f : Fin (n + 1) → G => MonoidAlgebra.single f r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g x))

omit [DecidableEq G] in
@[simp] theorem bar_augmentation_single (x : Fin 0 → G) (g : G) (r : k) :
    ((Rep.barResolution k G).π.f 0).hom (single x (.single g r)) = r := by
  change (Rep.standardComplex.ε k G).hom
    ((Rep.diagonalSuccIsoFree k G 0).inv.hom (single x (.single g r))) = r
  rw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

end CoboundaryExpanders.QuotientBarAugmentation

namespace CoboundaryExpanders.QuotientCoinvariants
open QuotientBarAugmentation
variable {G : Type} [Group G] [DecidableEq G] (N : Subgroup G) [N.Normal]
variable [DecidableEq (G ⧸ N)]
variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

theorem quotientBar_augmentation :
    quotientBar N ≫ (Rep.barResolution (ZMod 2) (G ⧸ N)).π = (quotientResolution N H).π := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    apply (homEquiv N _ _).injective
    apply Rep.free_ext
    intro x
    change ((Rep.barResolution (ZMod 2) (G ⧸ N)).π.f 0).hom
      ((quotientBarF N 0).hom (single x (.single 1 1))) =
      ((Rep.barResolution (ZMod 2) G).π.f 0).hom (single x (.single 1 1))
    rw [quotientBarF_single,bar_augmentation_single,bar_augmentation_single]
  | succ n =>
    apply Limits.IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X (V := Rep (ZMod 2) (G ⧸ N))
      (ComplexShape.down ℕ) 0 (Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2)) (n + 1) (by omega)

noncomputable def quotientBarHomotopy : Homotopy (quotientBar N)
    ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).hom :=
  ProjectiveResolution.liftHomotopy
    (P := quotientResolution N H) (Q := Rep.barResolution (ZMod 2) (G ⧸ N))
    (𝟙 _) (quotientBar N)
    ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).hom
    (by rw [CategoryTheory.Functor.map_id,Category.comp_id]; exact quotientBar_augmentation N H)
    (by rw [CategoryTheory.Functor.map_id,Category.comp_id]; exact ProjectiveResolution.homotopyEquiv_hom_π _ _)

noncomputable def quotientBarEquiv : HomotopyEquiv
    ((L N).mapHomologicalComplex _ |>.obj (Rep.barComplex (ZMod 2) G))
    (Rep.barComplex (ZMod 2) (G ⧸ N)) where
  hom := quotientBar N
  inv := ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).inv
  homotopyHomInvId := ((quotientBarHomotopy N H).compRight _).trans
    ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).homotopyHomInvId
  homotopyInvHomId := ((quotientBarHomotopy N H).compLeft _).trans
    ((quotientResolution N H).homotopyEquiv (Rep.barResolution (ZMod 2) (G ⧸ N))).homotopyInvHomId

end CoboundaryExpanders.QuotientCoinvariants

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.QuotientCoinvariantModel
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]

abbrev complex : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj (Rep.barComplex k G)

def chainsIso : groupHomology.inhomogeneousChains (Rep.trivial k G k) ≅
    complex (k := k) (G := G) :=
  groupHomology.inhomogeneousChainsIso (Rep.trivial k G k) ≪≫
    (NatIso.mapHomologicalComplex
      (Functor.isoWhiskerRight (leftUnitorNatIso (Rep k G)) (Rep.coinvariantsFunctor k G)) _).app
        (Rep.barComplex k G)

@[simp] theorem chainsIso_hom_single (n : ℕ) (x : Fin n → G) (r : k) :
    (chainsIso (k := k) (G := G)).hom.f n (single x r) =
      Representation.Coinvariants.mk (Representation.free k G (Fin n → G))
        (single x (.single (1 : G) r)) := by
  change (Rep.coinvariantsFunctor k G).map (λ_ (Rep.free k G (Fin n → G))).hom
    (Rep.finsuppToCoinvariantsTensorFree (Rep.trivial k G k) (Fin n → G)
      (single x r)) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  simp

end CoboundaryExpanders.QuotientCoinvariantModel

namespace CoboundaryExpanders.QuotientCoinvariants
open Representation
variable {G : Type} [Group G] [DecidableEq G] (N : Subgroup G) [N.Normal] [DecidableEq (G ⧸ N)]

omit [DecidableEq G] [DecidableEq (G ⧸ N)] in
lemma totalCoinvariantsIso_inv_mk (X : Rep.{0} (ZMod 2) G) (x : X) :
    ((totalCoinvariantsIso N).inv.app X).hom (Coinvariants.mk X.ρ x) =
      Coinvariants.mk (((L N).obj X).ρ) (Coinvariants.mk (X.ρ.comp N.subtype) x) := by
  apply ((ModuleCat.mono_iff_injective ((totalCoinvariantsIso N).hom.app X)).mp inferInstance)
  exact (ConcreteCategory.congr_hom ((totalCoinvariantsIso N).inv_hom_id_app X) _).trans
    (totalCoinvariantsIso_double_mk N X x).symm

noncomputable def coinvariantQuotient :
    QuotientCoinvariantModel.complex (k := ZMod 2) (G := G) ⟶
      QuotientCoinvariantModel.complex (k := ZMod 2) (G := G ⧸ N) :=
  ((NatIso.mapHomologicalComplex (totalCoinvariantsIso N) _).app (Rep.barComplex (ZMod 2) G)).inv ≫
    ((Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N)).mapHomologicalComplex _).map (quotientBar N)

noncomputable def trivialQuotient : Rep.trivial (ZMod 2) G (ZMod 2) ⟶
    Rep.res (QuotientGroup.mk' N) (Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2)) := 𝟙 _

theorem quotient_chain_factorization :
    (QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G)).hom ≫ coinvariantQuotient N =
      groupHomology.chainsMap (QuotientGroup.mk' N) (trivialQuotient N) ≫
        (QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G ⧸ N)).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x r
  change Coinvariants.map _ _ (homFrom N (quotientBarF N n)).hom
    (((totalCoinvariantsIso N).inv.app (Rep.free (ZMod 2) G (Fin n → G))).hom
      ((QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G)).hom.f n (single x r))) =
    (QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G ⧸ N)).hom.f n
      ((groupHomology.chainsMap (QuotientGroup.mk' N) (trivialQuotient N)).f n (single x r))
  rw [QuotientCoinvariantModel.chainsIso_hom_single,totalCoinvariantsIso_inv_mk]
  change Coinvariants.mk (Representation.free (ZMod 2) (G ⧸ N) (Fin n → G ⧸ N))
    ((quotientBarF N n).hom (single x (.single 1 r))) = _
  rw [groupHomology.chainsMap_f_single,QuotientCoinvariantModel.chainsIso_hom_single]
  rw [quotientBarF_single]
  rfl

variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

noncomputable def coinvariantQuotientEquiv : HomotopyEquiv
    (QuotientCoinvariantModel.complex (k := ZMod 2) (G := G))
    (QuotientCoinvariantModel.complex (k := ZMod 2) (G := G ⧸ N)) :=
  (HomotopyEquiv.ofIso
    (((NatIso.mapHomologicalComplex (totalCoinvariantsIso N) _).app (Rep.barComplex (ZMod 2) G)).symm)).trans
      ((Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N)).mapHomotopyEquiv (quotientBarEquiv N H))

include H in
theorem quotient_map_isIso (j : ℕ) :
    IsIso (groupHomology.map (QuotientGroup.mk' N) (trivialQuotient N) j) := by
  have hf := congrArg (fun f => HomologicalComplex.homologyMap f j) (quotient_chain_factorization N)
  simp only [HomologicalComplex.homologyMap_comp] at hf
  have he : IsIso (HomologicalComplex.homologyMap (coinvariantQuotient N) j) := by
    change IsIso (HomologicalComplex.homologyMap (coinvariantQuotientEquiv N H).hom j)
    refine ⟨⟨HomologicalComplex.homologyMap (coinvariantQuotientEquiv N H).inv j, ?_, ?_⟩⟩
    · rw [← HomologicalComplex.homologyMap_comp,
        (coinvariantQuotientEquiv N H).homotopyHomInvId.homologyMap_eq j,
        HomologicalComplex.homologyMap_id]
    · rw [← HomologicalComplex.homologyMap_comp,
        (coinvariantQuotientEquiv N H).homotopyInvHomId.homologyMap_eq j,
        HomologicalComplex.homologyMap_id]
  have hi : IsIso (HomologicalComplex.homologyMap
      ((QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G)).hom) j ≫
        HomologicalComplex.homologyMap (coinvariantQuotient N) j) := inferInstance
  rw [hf] at hi
  change IsIso (HomologicalComplex.homologyMap
    (groupHomology.chainsMap (QuotientGroup.mk' N) (trivialQuotient N)) j)
  have hQ : IsIso (HomologicalComplex.homologyMap
      ((QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G ⧸ N)).hom) j) := inferInstance
  exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap
    ((QuotientCoinvariantModel.chainsIso (k := ZMod 2) (G := G ⧸ N)).hom) j)

end CoboundaryExpanders.QuotientCoinvariants

end

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory
open CategoryTheory

namespace CoboundaryExpanders.QuotientCoinvariants

section
variable {G K : Type} [Group G] [Group K]

def trivialMap (f : G →* K) : Rep.trivial (ZMod 2) G (ZMod 2) ⟶
    Rep.res f (Rep.trivial (ZMod 2) K (ZMod 2)) := 𝟙 _

theorem surjection_map_isIso (f : G →* K) (hf : Function.Surjective f)
    (H : ∀ s : Finset f.ker, ∃ S : Subgroup f.ker,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) (j : ℕ) :
    IsIso (groupHomology.map f (trivialMap f) j) := by
  classical
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hq : IsIso (groupHomology.map (QuotientGroup.mk' f.ker) (trivialQuotient f.ker) j) :=
    quotient_map_isIso f.ker H j
  have he : IsIso (groupHomology.map e.toMonoidHom (trivialMap e.toMonoidHom) j) := by
    let E := groupHomology.mapIso
      (A := Rep.trivial (ZMod 2) (G ⧸ f.ker) (ZMod 2))
      (B := Rep.trivial (ZMod 2) K (ZMod 2))
      e (LinearEquiv.refl (ZMod 2) (ZMod 2)) (fun _ => rfl) j
    have ht : groupHomology.map e.toMonoidHom (trivialMap e.toMonoidHom) j = E.hom :=
      groupHomology.map_congr rfl rfl j
    rw [ht]
    infer_instance
  have hfactor : groupHomology.map f (trivialMap f) j =
      groupHomology.map (QuotientGroup.mk' f.ker) (trivialQuotient f.ker) j ≫
        groupHomology.map e.toMonoidHom (trivialMap e.toMonoidHom) j := by
    rw [← groupHomology.map_comp]
    apply groupHomology.map_congr
    · ext g
      rfl
    · rfl
  rw [hfactor]
  infer_instance

theorem localOdd_equiv (e : G ≃* K)
    (H : ∀ s : Finset G, ∃ S : Subgroup G,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) :
    ∀ s : Finset K, ∃ S : Subgroup K,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S := by
  classical
  intro s
  obtain ⟨S,hfin,hodd,hS⟩ := H (s.image e.symm)
  let eS := e.subgroupMap S
  refine ⟨S.map (e : G →* K),Finite.of_equiv S eS.toEquiv,?_,?_⟩
  · rw [← Nat.card_congr eS.toEquiv]
    exact hodd
  · intro g hg
    exact ⟨e.symm g,hS _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩),e.apply_symm_apply g⟩

end

variable {N G : Type} [Group N] [Group G] (φ : G →* MulAut N)

noncomputable def semidirectKernelEquiv : N ≃* (SemidirectProduct.rightHom : N ⋊[φ] G →* G).ker where
  toFun n := ⟨SemidirectProduct.inl n, by simp⟩
  invFun n := n.val.left
  left_inv _ := rfl
  right_inv n := by
    apply Subtype.ext
    ext
    · rfl
    · exact n.property.symm
  map_mul' n m := by
    apply Subtype.ext
    exact SemidirectProduct.inl.map_mul n m

theorem semidirect_projection_isIso
    (H : ∀ s : Finset N, ∃ S : Subgroup N,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) (j : ℕ) :
    IsIso (groupHomology.map (SemidirectProduct.rightHom : N ⋊[φ] G →* G)
      (trivialMap _) j) :=
  surjection_map_isIso _ SemidirectProduct.rightHom_surjective
    (localOdd_equiv (semidirectKernelEquiv φ) H) j

theorem semidirect_section_isIso
    (H : ∀ s : Finset N, ∃ S : Subgroup N,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) (j : ℕ) :
    IsIso (groupHomology.map (SemidirectProduct.inr : G →* N ⋊[φ] G)
      (trivialMap _) j) := by
  let f := (SemidirectProduct.inr : G →* N ⋊[φ] G)
  let g := (SemidirectProduct.rightHom : N ⋊[φ] G →* G)
  have hp := semidirect_projection_isIso φ H j
  have hc : groupHomology.map f (trivialMap f) j ≫ groupHomology.map g (trivialMap g) j = 𝟙 _ := by
    rw [← groupHomology.map_comp]
    have he : groupHomology.map (g.comp f) (trivialMap f ≫ (Rep.resFunctor f).map (trivialMap g)) j =
        groupHomology.map (MonoidHom.id G) (trivialMap (MonoidHom.id G)) j := by
      apply groupHomology.map_congr
      · exact SemidirectProduct.rightHom_comp_inr
      · rfl
    rw [he]
    exact groupHomology.map_id j
  have hcomp : IsIso (groupHomology.map f (trivialMap f) j ≫ groupHomology.map g (trivialMap g) j) := by
    rw [hc]
    infer_instance
  exact IsIso.of_isIso_comp_right (groupHomology.map f (trivialMap f) j)
    (groupHomology.map g (trivialMap g) j)

end CoboundaryExpanders.QuotientCoinvariants

namespace CoboundaryExpanders.LocallyFiniteOdd

theorem vector_group_local_odd (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] :
    ∀ s : Finset (Multiplicative V), ∃ S : Subgroup (Multiplicative V),
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S := by
  classical
  intro s
  let t : Finset V := s.image Multiplicative.toAdd
  let W : Submodule (ZMod p) V := Submodule.span (ZMod p) (t : Set V)
  let S : Subgroup (Multiplicative V) :=
    { carrier := {g | Multiplicative.toAdd g ∈ W}
      one_mem' := W.zero_mem
      mul_mem' := fun ha hb => W.add_mem ha hb
      inv_mem' := fun ha => W.neg_mem ha }
  let e : S ≃ W :=
    { toFun := fun x => ⟨Multiplicative.toAdd x.val,x.property⟩
      invFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : FiniteDimensional (ZMod p) W := FiniteDimensional.span_finset (ZMod p) t
  have hc : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_eq_fintype_card,ZMod.card]
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  refine ⟨S,Finite.of_equiv W e.symm,?_,?_⟩
  · rw [Nat.card_congr e,hc]
    exact hp.pow
  · intro g hg
    change Multiplicative.toAdd g ∈ W
    apply Submodule.subset_span
    change Multiplicative.toAdd g ∈ t
    exact Finset.mem_image.mpr ⟨g,hg,rfl⟩

end CoboundaryExpanders.LocallyFiniteOdd

namespace CoboundaryExpanders.QuotientCoinvariants

section
open CategoryTheory

theorem vector_semidirect_maps_isIso (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (G : Type) [Group G] (φ : G →* MulAut (Multiplicative V)) (j : ℕ) :
    IsIso (groupHomology.map
      (SemidirectProduct.rightHom : (Multiplicative V) ⋊[φ] G →* G)
      (trivialMap _) j) ∧
    IsIso (groupHomology.map
      (SemidirectProduct.inr : G →* (Multiplicative V) ⋊[φ] G)
      (trivialMap _) j) :=
  ⟨semidirect_projection_isIso φ (LocallyFiniteOdd.vector_group_local_odd p hp V) j,
   semidirect_section_isIso φ (LocallyFiniteOdd.vector_group_local_odd p hp V) j⟩
end

variable {G K : Type} [Group G] [Group K]

theorem localOdd_of_injective (f : G →* K) (hf : Function.Injective f)
    (H : ∀ s : Finset K, ∃ S : Subgroup K,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S) :
    ∀ s : Finset G, ∃ S : Subgroup G,
      Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S := by
  classical
  intro s
  obtain ⟨S,hfin,hodd,hS⟩ := H (s.image f)
  have := hfin
  let T := S.comap f
  let g : T →* S :=
    { toFun := fun x => ⟨f x.val,x.property⟩
      map_one' := by apply Subtype.ext; exact f.map_one
      map_mul' x y := by apply Subtype.ext; exact f.map_mul x.val y.val }
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hxy
  refine ⟨T,Finite.of_injective g hg,?_,?_⟩
  · exact hodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)
  · intro x hx
    exact hS (f x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

end CoboundaryExpanders.QuotientCoinvariants

end

end OAI
