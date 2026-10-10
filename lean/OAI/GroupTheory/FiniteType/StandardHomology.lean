import Mathlib
import OAI.GroupTheory.FiniteType.CategoryTheoryShortComplex
import OAI.GroupTheory.FiniteType.CosetCoordinates

namespace OAI

noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
namespace StandardHomology
variable {R G : Type} [CommRing R] [Group G]

def coefficientMap (P : ChainComplex (Rep R G) ℕ) {A B : Rep R G} (α : A ⟶ B) :
    P.coinvariantsTensorObj A ⟶ P.coinvariantsTensorObj B :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor R G).map α) _).app P

lemma coefficientMap_naturality {P Q : ChainComplex (Rep R G) ℕ}
    (u : P ⟶ Q) {A B : Rep R G} (α : A ⟶ B) :
    (((Rep.coinvariantsTensor R G).obj A).mapHomologicalComplex _).map u ≫
      coefficientMap Q α = coefficientMap P α ≫
        (((Rep.coinvariantsTensor R G).obj B).mapHomologicalComplex _).map u :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor R G).map α) _).naturality u

lemma inhomogeneousIso_naturality [DecidableEq G] {A B : Rep R G} (α : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) α ≫
      (groupHomology.inhomogeneousChainsIso B).hom =
    (groupHomology.inhomogeneousChainsIso A).hom ≫
      coefficientMap (Rep.barComplex R G) α := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s a
  change (groupHomology.inhomogeneousChainsIso B).hom.f n
    ((groupHomology.chainsMap (MonoidHom.id G) α).f n (Finsupp.single s a)) = _
  rw [groupHomology.chainsMap_f_single]
  change Rep.finsuppToCoinvariantsTensorFree B (Fin n → G)
      (Finsupp.single s (α a)) =
    (coefficientMap (Rep.barComplex R G) α).f n
      (Rep.finsuppToCoinvariantsTensorFree A (Fin n → G) (Finsupp.single s a))
  rw [Rep.finsuppToCoinvariantsTensorFree_single,Rep.finsuppToCoinvariantsTensorFree_single]
  rfl

def chainsIso (A : Rep R G) : groupHomology.inhomogeneousChains A ≅
    (Rep.standardComplex R G).coinvariantsTensorObj A := by
  classical
  exact groupHomology.inhomogeneousChainsIso A ≪≫
    (((Rep.coinvariantsTensor R G).obj A).mapHomologicalComplex _).mapIso
      (Rep.barComplex.isoStandardComplex R G)

lemma chainsIso_naturality {A B : Rep R G} (α : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id G) α ≫ (chainsIso B).hom =
    (chainsIso A).hom ≫ coefficientMap (Rep.standardComplex R G) α := by
  classical
  dsimp [chainsIso]
  rw [← Category.assoc,inhomogeneousIso_naturality,Category.assoc,
    ← coefficientMap_naturality,← Category.assoc]

def homologyIso (A : Rep R G) (n : ℕ) : groupHomology A n ≅
    ((Rep.standardComplex R G).coinvariantsTensorObj A).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
    (chainsIso A)

lemma homologyIso_naturality {A B : Rep R G} (α : A ⟶ B) (n : ℕ) :
    (groupHomology.functor R G n).map α ≫ (homologyIso B n).hom =
      (homologyIso A n).hom ≫ HomologicalComplex.homologyMap
        (coefficientMap (Rep.standardComplex R G) α) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
      HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp,
    chainsIso_naturality]

end StandardHomology

open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace groupHomology
open scoped _root_.groupHomology
variable (R G : Type) [CommRing R] [Group G]

instance chainsFunctor_additive : (_root_.groupHomology.chainsFunctor R G).Additive where
  map_add := by
    intro A B α β
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro s a
    change (_root_.groupHomology.chainsMap (MonoidHom.id G) (α+β)).f n (Finsupp.single s a) =
      (_root_.groupHomology.chainsMap (MonoidHom.id G) α).f n (Finsupp.single s a) +
      (_root_.groupHomology.chainsMap (MonoidHom.id G) β).f n (Finsupp.single s a)
    exact (_root_.groupHomology.chainsMap_f_single (MonoidHom.id G) (α+β) n s a).trans
      ((Finsupp.single_add _ _ _).trans
        (congrArg₂ (· + ·)
          (_root_.groupHomology.chainsMap_f_single (MonoidHom.id G) α n s a)
          (_root_.groupHomology.chainsMap_f_single (MonoidHom.id G) β n s a)).symm)

instance functor_additive (n : ℕ) : (_root_.groupHomology.functor R G n).Additive := by
  change (_root_.groupHomology.chainsFunctor R G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).Additive
  infer_instance

end groupHomology

namespace LocalNilpotence

variable {A : Type*} [AddCommGroup A]

def IsLocallyNilpotent (f : A →+ A) : Prop := ∀ x, ∃ n : ℕ, (f : A → A)^[n] x = 0

def partialSum (f : A →+ A) : ℕ → A → A
  | 0, _ => 0
  | n+1, x => partialSum f n x + (f : A → A)^[n] x

lemma partialSum_sub_map (f : A →+ A) (n : ℕ) (x : A) :
    partialSum f n x - f (partialSum f n x) = x - (f : A → A)^[n] x := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [partialSum,map_add,Function.iterate_succ_apply']
    calc
      partialSum f n x + (f : A → A)^[n] x -
          (f (partialSum f n x) + f ((f : A → A)^[n] x)) =
        (partialSum f n x - f (partialSum f n x)) +
          ((f : A → A)^[n] x - f ((f : A → A)^[n] x)) := by abel
      _ = x - f ((f : A → A)^[n] x) := by rw [ih]; abel

lemma iterate_fixed (f : A →+ A) {x : A} (hx : f x = x) (n : ℕ) :
    (f : A → A)^[n] x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,hx]

theorem one_sub_bijective (f : A →+ A) (hf : IsLocallyNilpotent f) :
    Function.Bijective (AddMonoidHom.id A - f) := by
  constructor
  · intro x y hxy
    have he : f (x-y) = x-y := by
      change x - f x = y - f y at hxy
      rw [map_sub]
      have h := sub_eq_sub_iff_add_eq_add.mp hxy
      apply sub_eq_sub_iff_add_eq_add.mpr
      simpa only [add_comm] using h.symm
    obtain ⟨n,hn⟩ := hf (x-y)
    rw [iterate_fixed f he] at hn
    exact sub_eq_zero.mp hn
  · intro x
    obtain ⟨n,hn⟩ := hf x
    refine ⟨partialSum f n x,?_⟩
    change partialSum f n x - f (partialSum f n x) = x
    rw [partialSum_sub_map,hn,sub_zero]

noncomputable def oneSubEquiv (f : A →+ A) (hf : IsLocallyNilpotent f) : A ≃+ A :=
  AddEquiv.ofBijective (AddMonoidHom.id A - f) (one_sub_bijective f hf)

end LocalNilpotence

open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace HomologyVanishingSequence
variable {R G : Type} [CommRing R] [Group G]
variable (S : ShortComplex (Rep R G)) (hS : S.ShortExact)

include hS

theorem vanishing (n : ℕ)
    (hsurj : Function.Surjective ((groupHomology.functor R G (n+1)).map S.f))
    (hinj : Function.Injective ((groupHomology.functor R G n).map S.f)) :
    ∀ x : groupHomology S.X₃ (n+1), x = 0 := by
  intro x
  let T := groupHomology.mapShortComplex₃ hS (i := n+1) (j := n) rfl
  have hex : T.Exact := groupHomology.mapShortComplex₃_exact hS rfl
  have hz : T.g x = 0 := by
    apply hinj
    have h := (groupHomology.mapShortComplex₁ hS (i := n+1) (j := n) rfl).zero_apply x
    change ((groupHomology.functor R G n).map S.f) (T.g x) = 0 at h
    exact h.trans (((groupHomology.functor R G n).map S.f).hom.map_zero).symm
  obtain ⟨z,hz⟩ := T.moduleCat_exact_iff.mp hex x hz
  obtain ⟨y,hy⟩ := hsurj z
  rw [← hz,← hy]
  exact (groupHomology.mapShortComplex₂ S (n+1)).zero_apply y

end HomologyVanishingSequence

namespace RegularProduct
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable (G I : Type) [Group G] (S : Subgroup G)
variable (f : S →* S) (t : G) (ht : ∀ s : S, (s : G)*t=t*(f s : G))
variable (p : (G ⧸ S) → G ⧸ S) (peq : ∀ (g : G) (v : G ⧸ S), p (g • v)=g • p v)
variable (pbase : p (QuotientGroup.mk (1 : G)) = QuotientGroup.mk t)

lemma shift_local_nilpotence {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    ∀ x : ((Rep.standardComplex ℤ S).coinvariantsTensorObj (Rep.res S.subtype (rep G I))).homology (n+1),
      ∃ k : ℕ, (HomologicalComplex.homologyMap
        (CosetEndpoint.shiftChain S (rep G I) f t ht) (n+1) : _ → _)^[k] x = 0 := by
  apply HomologyTransport.localNilpotence_transfer _
    (HomologicalComplex.homologyMap (ListChains.standardShiftChainMap S I (G ⧸ S) f
      (CosetCoordinates.nextCoset S t) (CosetCoordinates.correction S t)) (n+1))
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (n+1)).mapIso
      (restrictionChainIso G I S))
  · change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp,
      restrictionChainIso_shift]
  · exact hf.standard_local_nilpotence S I (G ⧸ S) _ _

include t ht pbase peq

lemma coset_parent_local_nilpotence {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    ∀ x : ((Rep.standardComplex ℤ G).coinvariantsTensorObj
      (CosetInduction.cosetRep S (rep G I))).homology (n+1),
    ∃ k : ℕ, (HomologicalComplex.homologyMap
      (StandardTensor.coefficientMap (FunctionalTree.parentHom (rep G I) p peq)) (n+1) : _ → _)^[k] x = 0 := by
  apply HomologyTransport.localNilpotence_transfer_reverse
    (HomologicalComplex.homologyMap (CosetEndpoint.shiftChain S (rep G I) f t ht) (n+1)) _
    ((StandardShapiro.cosetEquiv S (rep G I)).toHomologyIso (n+1))
  · change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp]
    exact (CosetEndpoint.shapiroParentHomotopy S (rep G I) f t ht p peq pbase).homologyMap_eq (n+1) |>.symm
  · exact shift_local_nilpotence G I S f t ht hf

lemma parent_local_nilpotence {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    ∀ x : groupHomology (CosetInduction.cosetRep S (rep G I)) (n+1),
    ∃ k : ℕ, ((groupHomology.functor ℤ G (n+1)).map
      (FunctionalTree.parentHom (rep G I) p peq) : _ → _)^[k] x = 0 := by
  apply HomologyTransport.localNilpotence_transfer _ _
    (StandardHomology.homologyIso (CosetInduction.cosetRep S (rep G I)) (n+1))
    (StandardHomology.homologyIso_naturality (FunctionalTree.parentHom (rep G I) p peq) (n+1))
  exact coset_parent_local_nilpotence G I S f t ht p peq pbase hf

lemma boundary_bijective {n : ℕ} (hf : ListChains.UniformFillings S f (n+1)) :
    Function.Bijective ((groupHomology.functor ℤ G (n+1)).map
      (FunctionalTree.boundaryHom (rep G I) p peq)) := by
  have h := LocalNilpotence.one_sub_bijective
    (((groupHomology.functor ℤ G (n+1)).map
      (FunctionalTree.parentHom (rep G I) p peq)).hom.toAddMonoidHom)
    (parent_local_nilpotence G I S f t ht p peq pbase hf)
  rw [FunctionalTree.boundaryHom,CategoryTheory.Functor.map_sub,CategoryTheory.Functor.map_id]
  exact h

theorem vanishing {n : ℕ}
    (hf₁ : ListChains.UniformFillings S f (n+1))
    (hf₂ : ListChains.UniformFillings S f (n+2))
    [Nonempty (G ⧸ S)]
    (merge : ∀ v w, ∃ a b : ℕ, p^[a] v = p^[b] w)
    (height : (G ⧸ S) → ℤ) (raise : ∀ v, height (p v)=height v+1) :
    ∀ x : groupHomology (rep G I) (n+2), x=0 := by
  exact HomologyVanishingSequence.vanishing
    (FunctionalTree.equivariantComplex (rep G I) p peq)
    (FunctionalTree.equivariantComplex_shortExact (rep G I) p peq merge height raise)
    (n+1)
    (boundary_bijective G I S f t ht p peq pbase hf₂).surjective
    (boundary_bijective G I S f t ht p peq pbase hf₁).injective

end RegularProduct

end

end OAI
