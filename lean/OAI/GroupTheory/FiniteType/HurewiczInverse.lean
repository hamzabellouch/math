import Mathlib
import OAI.GroupTheory.FiniteType.BoundaryValueBoundarySplit

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace HurewiczInverse
open Set Topology CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains SingularNormalization.Coherent
open scoped unitInterval
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

variable (hπ : ∀ p < n+2, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X)

def coherent : SingularNormalization.Coherent X where
  H := FixedSingularTightening.hom hπ x
  zero := FixedSingularTightening.hom_zero hπ x
  face := FixedSingularTightening.hom_face hπ x

lemma coherent_top (p : ℕ) (hp : p < n+2) (f : C(Std p,X)) :
    (coherent hπ x).top p f = ContinuousMap.const _ x := by
  ext s
  exact FixedSingularTightening.hom_top hπ x p hp f s

lemma coherent_fixed (p : ℕ) :
    (coherent hπ x).H p (ContinuousMap.const _ x) = ContinuousMap.const _ x :=
  FixedSingularTightening.hom_fixed hπ x p

def normalize (f : C(Std (n+2),X)) : BasedSimplex.Space (n+2) X x :=
  ⟨(coherent hπ x).top (n+2) f,by
    rintro s ⟨i,hi⟩
    rw [← SimplexBoundary.face_drop i s hi]
    change ((coherent hπ x).top (n+2) f).comp (face i) _ = _
    rw [top_face,coherent_top hπ x (n+1) (by omega)]
    rfl⟩

lemma normalize_const : normalize hπ x (ContinuousMap.const _ x) = BasedSimplex.const _ x := by
  apply Subtype.ext
  ext s
  change (coherent hπ x).H (n+2) (ContinuousMap.const _ x) (1,s) = x
  rw [coherent_fixed]
  rfl

lemma hom_relative (f : BasedSimplex.Space (n+2) X x) :
    Nonempty (f.1.HomotopyRel (normalize hπ x f.1).1 (BasedSimplex.Boundary (n+2))) := by
  refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
  · exact { toContinuousMap := (coherent hπ x).H (n+2) f.1
            map_zero_left := (coherent hπ x).zero (n+2) f.1
            map_one_left := fun _ => rfl }
  · intro t s hs
    change (coherent hπ x).H (n+2) f.1 (t,s) = f.1 s
    rw [f.2 s hs]
    obtain ⟨i,hi⟩ := hs
    rw [← SimplexBoundary.face_drop i s hi]
    exact ((coherent hπ x).face (n+1) f.1 i t (SimplexBoundary.drop i s hi)).trans (by
      rw [HurewiczNormalized.based_face,coherent_fixed]
      rfl)

lemma normalize_class (f : BasedSimplex.Space (n+2) X x) :
    DuffyBased.homotopyClass (normalize hπ x f.1) = DuffyBased.homotopyClass f :=
  ((DuffyBased.class_eq_iff _ _).mpr (hom_relative hπ x f)).symm

lemma top_double (f : C(Std (n+3),X)) :
    ∀ s ∈ DuffyTriangle.DoubleBoundary (n+3), (coherent hπ x).top (n+3) f s = x := by
  rintro s ⟨i,j,hij,hi,hj⟩
  obtain ⟨j',hj'⟩ := Fin.exists_succAbove_eq hij.symm
  subst j
  let a := SimplexBoundary.drop i s hi
  have ha : a.1 j' = 0 := hj
  rw [← SimplexBoundary.face_drop i s hi]
  change ((coherent hπ x).top (n+3) f).comp (face i) a = x
  rw [top_face,← SimplexBoundary.face_drop j' a ha]
  change ((coherent hπ x).top (n+2) (f.comp (face i))).comp (face j') _ = x
  rw [top_face,coherent_top hπ x (n+1) (by omega)]
  rfl

lemma top_basedFace (f : C(Std (n+3),X)) (i : Fin (n+4)) :
    SimplexAddition.basedFace ((coherent hπ x).top (n+3) f) (top_double hπ x f) i =
      normalize hπ x (f.comp (face i)) := by
  apply Subtype.ext
  exact top_face (coherent hπ x) (n+2) f i

abbrev A := BoundaryValue.A n X x

def chainValue : (chains X).X (n+2) ⟶ ModuleCat.of ℤ (A (n:=n) (x:=x)) :=
  desc (fun f => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (BoundaryValue.value (normalize hπ x f))))

lemma generator_chainValue (f : C(Std (n+2),X)) :
    generator f ≫ chainValue hπ x =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (BoundaryValue.value (normalize hπ x f))) :=
  generator_desc _ _

lemma boundary_chainValue : (chains X).d (n+3) (n+2) ≫ chainValue hπ x = 0 := by
  apply SingularChains.hom_ext
  intro f
  rw [← Category.assoc,generator_boundary]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,generator_chainValue,comp_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have h := BoundaryValue.boundary_zero ((coherent hπ x).top (n+3) f) (top_double hπ x f)
  simp only [BoundaryValue.boundary,top_basedFace] at h
  simpa using h

def inverse : (chains X).homology (n+2) ⟶ ModuleCat.of ℤ (A (n:=n) (x:=x)) :=
  ((chains X).sc (n+2)).descHomology (((chains X).sc (n+2)).iCycles ≫ chainValue hπ x) (by
    erw [← Category.assoc,ShortComplex.toCycles_i]
    change (chains X).d _ (n+2) ≫ chainValue hπ x = 0
    have hd (i : ℕ) : (chains X).d i (n+2) ≫ chainValue hπ x = 0 := by
      by_cases hi : i = n+3
      · subst i
        exact boundary_chainValue hπ x
      · rw [(chains X).shape i (n+2) (by change ¬ n+2+1 = i; omega)]
        exact zero_comp
    exact hd _)

lemma homologyπ_inverse : (chains X).homologyπ (n+2) ≫ inverse hπ x =
    (chains X).iCycles (n+2) ≫ chainValue hπ x :=
  ShortComplex.π_descHomology _ _ _

lemma cycleClassHom_inverse (f : BasedSimplex.Space (n+2) X x) :
    HurewiczNormalized.cycleClassHom (HurewiczNormalized.cycle f) (HurewiczNormalized.cycle_d f) ≫
      inverse hπ x = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (BoundaryValue.value f)) := by
  rw [HurewiczNormalized.cycleClassHom,Category.assoc,homologyπ_inverse,
    ← Category.assoc,liftCycles_i,HurewiczNormalized.cycle,Preadditive.sub_comp,
    generator_chainValue,generator_chainValue,normalize_const]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (1:ℤ) • BoundaryValue.value (normalize hπ x f.1) -
    (1:ℤ) • BoundaryValue.value (BasedSimplex.const (n+2) x) = (1:ℤ) • BoundaryValue.value f
  rw [one_smul,one_smul,one_smul,BoundaryValue.value_const,sub_zero]
  exact congrArg Additive.ofMul (normalize_class hπ x f)

lemma inverse_homologyClass (f : BasedSimplex.Space (n+2) X x) :
    inverse hπ x (HurewiczNormalized.homologyClass f) = BoundaryValue.value f := by
  have h := congrArg (fun z : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (A (n:=n) (x:=x)) => z 1)
    (cycleClassHom_inverse hπ x f)
  change inverse hπ x (HurewiczNormalized.homologyClass f) = (1:ℤ) • BoundaryValue.value f at h
  simpa only [one_smul] using h

lemma leftInverse : Function.LeftInverse (inverse hπ x) (DuffyHurewicz.hom (n+1) x) := by
  intro p
  obtain ⟨q,hq⟩ := Quotient.exists_rep p.toMul
  let f := DuffyBased.ofLoop q
  have hf : DuffyBased.homotopyClass f = p.toMul := by
    exact (congrArg (Quotient.mk _) (DuffyBased.loop_ofLoop q)).trans hq
  have hp : Additive.ofMul (DuffyBased.homotopyClass f) = p := congrArg Additive.ofMul hf
  rw [← hp,DuffyHurewicz.hom_class,inverse_homologyClass]
  rfl

end HurewiczInverse

namespace DuffyHurewicz
open SingularChains
variable {X : Type} [TopologicalSpace X] {n : ℕ}

theorem injective
    (hπ : ∀ p < n+2, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X) :
    Function.Injective (hom (n+1) x) :=
  (HurewiczInverse.leftInverse hπ x).injective

theorem bijective
    (hπ : ∀ p < n+2, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X) :
    Function.Bijective (hom (n+1) x) :=
  ⟨injective hπ x,surjective hπ x⟩

end DuffyHurewicz

namespace HurewiczConstruction
section
open SingularChains SphereQuotient CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] {n : ℕ}

theorem exists_sphere
    (hπ : ∀ p < n+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X)
    (z : (chains X).homology (n+1)) :
    ∃ f : C(Boundary (n+2),X),
      pushforward (n+1) f (SingularSphereCycle.fundamentalClass (n+1)) = z := by
  obtain ⟨p,hp⟩ := DuffyHurewicz.surjective hπ x z
  change DuffyHurewicz.value p.toMul = z at hp
  have hr : ∀ q : HomotopyGroup.Pi (n+1) X x,
      ∃ f : C(Boundary (n+2),X),
        pushforward (n+1) f (SingularSphereCycle.fundamentalClass (n+1)) =
          DuffyHurewicz.value q := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      let s := DuffyBased.ofLoop a
      refine ⟨sphereMap (BasedSimplex.loop s),?_⟩
      change canonical (n+1) (BasedSimplex.homotopyClass s) = _
      rw [HurewiczNormalized.canonical_simplex]
      rfl
  obtain ⟨f,hf⟩ := hr p.toMul
  exact ⟨f,hf.trans hp⟩

variable {G : Type} [Group G] [MulAction G X] [ContinuousConstSMul G X]

def actionMap (g : G) : C(X,X) := ⟨(g • ·),continuous_const_smul g⟩

@[simp] lemma actionMap_one : actionMap (X:=X) (1 : G) = ContinuousMap.id X := by ext x; simp [actionMap]
@[simp] lemma actionMap_mul (g h : G) :
    actionMap (X:=X) (g*h) = (actionMap g).comp (actionMap h) := by ext x; simp [actionMap,mul_smul]

def homologyRep (j : ℕ) : Representation ℤ G (integralHomology j X) where
  toFun g := pushforward j (actionMap g)
  map_one' := by
    rw [actionMap_one]
    exact congrArg ModuleCat.Hom.hom
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) j).obj (ModuleCat.of ℤ ℤ)).map_id _)
  map_mul' g h := by rw [actionMap_mul,pushforward_comp]; rfl

abbrev homologyModule (j : ℕ) := (homologyRep (G:=G) (X:=X) j).asModule

def sphereModuleClass (j : ℕ) (f : C(Boundary (j+1),X)) : homologyModule (G:=G) (X:=X) j :=
  (homologyRep (G:=G) (X:=X) j).asModuleEquiv.symm
    (pushforward j f (SingularSphereCycle.fundamentalClass j))

theorem finite_sphere_generators
    (hπ : ∀ p < n+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X)
    [Module.Finite (MonoidAlgebra ℤ G) (homologyModule (G:=G) (X:=X) (n+1))] :
    ∃ (k : ℕ) (s : Fin k → C(Boundary (n+2),X)),
      Submodule.span (MonoidAlgebra ℤ G)
        (Set.range (fun i => sphereModuleClass (G:=G) (n+1) (s i))) = ⊤ := by
  obtain ⟨k,z,hz⟩ := Module.Finite.exists_fin (R:=MonoidAlgebra ℤ G)
    (M:=homologyModule (G:=G) (X:=X) (n+1))
  choose s hs using fun i => exists_sphere hπ x (z i)
  refine ⟨k,s,?_⟩
  have he : (fun i => sphereModuleClass (G:=G) (n+1) (s i)) = z :=
    funext hs
  rw [he]
  exact hz
end

open CategoryTheory.Limits SingularChains
variable {X : Type} [TopologicalSpace X]

lemma homotopy_zero [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup (Fin 0) X x) :=
  HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton

lemma homotopy_one [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup (Fin 1) X x) :=
  HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton

theorem homotopy_trivial_of_homology_zero [SimplyConnectedSpace X] (n : ℕ)
    (hH : ∀ j, 2 ≤ j → j ≤ n → IsZero ((chains X).homology j)) :
    ∀ j ≤ n, ∀ x : X, Subsingleton (HomotopyGroup (Fin j) X x) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj x
    cases j with
    | zero => exact homotopy_zero x
    | succ j =>
      cases j with
      | zero => exact homotopy_one x
      | succ j =>
        have hp : ∀ p < j+2, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z) :=
          fun p h z => ih p h (by omega) z
        let := (ModuleCat.isZero_iff_subsingleton.mp (hH (j+2) (by omega) hj))
        have hi := DuffyHurewicz.injective hp x
        exact (hi.comp (show Function.Injective (Additive.ofMul :
          HomotopyGroup.Pi (j+2) X x → Additive (HomotopyGroup.Pi (j+2) X x)) from fun _ _ h => h)).subsingleton

lemma homology_zero_of_homotopy {n : ℕ}
    (hπ : ∀ p ≤ n+1, ∀ z : X, Subsingleton (HomotopyGroup (Fin p) X z)) (x : X) :
    IsZero ((chains X).homology (n+1)) := by
  let := hπ (n+1) le_rfl x
  have hs := DuffyHurewicz.surjective (n:=n) (fun p h z => hπ p (by omega) z) x
  let : Subsingleton ((chains X).homology (n+1)) := hs.subsingleton
  exact ModuleCat.isZero_of_subsingleton _
end HurewiczConstruction

end

end OAI
