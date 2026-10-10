import Mathlib
import OAI.GroupTheory.FiniteType.SimplexHomotopy

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
namespace SingularPrism
open scoped Simplicial

variable {X Y Z : TopCat} {f g : X ⟶ Y}

open MonoidalCategory Functor.LaxMonoidal

lemma top_h_precomp (H : TopCat.Homotopy f g) (p : Z ⟶ X) :
    (H.comp (TopCat.Homotopy.refl p)).h = p ▷ TopCat.I ≫ H.h := by
  ext x
  rfl

lemma sset_h_precomp (H : TopCat.Homotopy f g) (p : Z ⟶ X) :
    (H.comp (TopCat.Homotopy.refl p)).toSSet.h =
      (TopCat.toSSet.map p) ▷ Δ[1] ≫ H.toSSet.h := by
  simp only [TopCat.Homotopy.toSSet,top_h_precomp,Functor.map_comp]
  rw [← Category.assoc (μ TopCat.toSSet _ _),← μ_natural_left]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc]

theorem component_precomp (H : TopCat.Homotopy f g) (p : Z ⟶ X)
    {n : ℕ} (i : Fin (n+1)) :
    ((H.comp (TopCat.Homotopy.refl p)).toSSet.toSimplicialObjectHomotopy).h i =
      (TopCat.toSSet.map p).app _ ≫ H.toSSet.toSimplicialObjectHomotopy.h i := by
  ext x
  simp only [SSet.Homotopy.toSimplicialObjectHomotopy,sset_h_precomp,
    TypeCat.Fun.toFun_apply,types_comp_apply,TypeCat.hom_ofHom,TypeCat.Fun.coe_mk]
  rw [← SSet.yonedaEquiv_symm_comp]
  simp only [comp_whiskerRight,Category.assoc]

theorem prism_precomp (H : TopCat.Homotopy f g) (p : Z ⟶ X) (n : ℕ) :
    ((H.comp (TopCat.Homotopy.refl p)).singularChainComplexFunctorObjMap
      (ModuleCat.of ℤ ℤ)).hom n (n+1) =
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map p).f n ≫
        (H.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)).hom n (n+1) := by
  change CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
    ((H.comp (TopCat.Homotopy.refl p)).toSSet.toSimplicialObjectHomotopy.whiskerRight
      (sigmaConst.obj (ModuleCat.of ℤ ℤ))) n (n+1) =
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map ((TopCat.toSSet.map p).app (Opposite.op ⦋n⦌)) ≫
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
        (H.toSSet.toSimplicialObjectHomotopy.whiskerRight
          (sigmaConst.obj (ModuleCat.of ℤ ℤ))) n (n+1)
  rw [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
    CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  simp only [Preadditive.comp_neg,Preadditive.comp_sum,Preadditive.comp_zsmul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map _ =
    (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map _ ≫ (sigmaConst.obj (ModuleCat.of ℤ ℤ)).map _
  rw [← Functor.map_comp,component_precomp]

end SingularPrism

namespace SingularChains
open Set Topology CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def start (F : C(I × X,Y)) : C(X,Y) :=
  F.comp ⟨fun x => (0,x),continuous_const.prodMk continuous_id⟩
def finish (F : C(I × X,Y)) : C(X,Y) :=
  F.comp ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩

def cylinderHom (F : C(I × X,Y)) : ContinuousMap.Homotopy (start F) (finish F) where
  toContinuousMap := F
  map_zero_left _ := rfl
  map_one_left _ := rfl

def prism (F : C(I × X,Y)) (n : ℕ) : (chains X).X n ⟶ (chains Y).X (n+1) :=
  (TopCat.Homotopy.singularChainComplexFunctorObjMap (f := TopCat.ofHom (start F))
    (g := TopCat.ofHom (finish F)) (cylinderHom F) (ModuleCat.of ℤ ℤ)).hom n (n+1)

def precompCylinder (F : C(I × X,Y)) (p : C(Z,X)) : C(I × Z,Y) :=
  F.comp ⟨fun z => (z.1,p z.2),continuous_fst.prodMk (p.continuous.comp continuous_snd)⟩

lemma prism_precomp (F : C(I × X,Y)) (p : C(Z,X)) (n : ℕ) :
    prism (precompCylinder F p) n = (map p).f n ≫ prism F n := by
  exact SingularPrism.prism_precomp (f := TopCat.ofHom (start F)) (g := TopCat.ofHom (finish F))
    (cylinderHom F) (TopCat.ofHom p) n

lemma prism_boundary_zero (F : C(I × X,Y)) :
    (map (start F)).f 0 = prism F 0 ≫ (chains Y).d 1 0 + (map (finish F)).f 0 := by
  have h := (TopCat.Homotopy.singularChainComplexFunctorObjMap (f := TopCat.ofHom (start F))
    (g := TopCat.ofHom (finish F)) (cylinderHom F) (ModuleCat.of ℤ ℤ)).comm 0
  rw [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,zero_add] at h
  exact h

lemma prism_boundary_succ (F : C(I × X,Y)) (n : ℕ) :
    (map (start F)).f (n+1) =
      (chains X).d (n+1) n ≫ prism F n +
        prism F (n+1) ≫ (chains Y).d (n+2) (n+1) + (map (finish F)).f (n+1) := by
  have h := (TopCat.Homotopy.singularChainComplexFunctorObjMap (f := TopCat.ofHom (start F))
    (g := TopCat.ofHom (finish F)) (cylinderHom F) (ModuleCat.of ℤ ℤ)).comm (n+1)
  rw [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex] at h
  exact h

end SingularChains

namespace SingularNormalization
section
open Set Topology CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval
open SingularChains
variable {X : Type} [TopologicalSpace X]

structure Coherent (X : Type) [TopologicalSpace X] where
  H : ∀ n, C(Std n,X) → C(I × Std n,X)
  zero : ∀ n f s, H n f (0,s) = f s
  face : ∀ n (f : C(Std (n+1),X)) (i : Fin (n+2)) t s,
    H (n+1) f (t,SingularChains.face i s) = H n (f.comp (SingularChains.face i)) (t,s)

namespace Coherent
variable (S : Coherent X)

def top (n : ℕ) (f : C(Std n,X)) : C(Std n,X) := finish (S.H n f)

lemma start_eq (n : ℕ) (f : C(Std n,X)) : start (S.H n f) = f := by
  ext s
  exact S.zero n f s

lemma top_face (n : ℕ) (f : C(Std (n+1),X)) (i : Fin (n+2)) :
    (S.top (n+1) f).comp (SingularChains.face i) = S.top n (f.comp (SingularChains.face i)) := by
  ext s
  exact S.face n f i 1 s

lemma hom_face (n : ℕ) (f : C(Std (n+1),X)) (i : Fin (n+2)) :
    precompCylinder (S.H (n+1) f) (SingularChains.face i) = S.H n (f.comp (SingularChains.face i)) := by
  ext s
  exact S.face n f i s.1 s.2

def topComponent (n : ℕ) : (chains X).X n ⟶ (chains X).X n :=
  desc (fun f => generator (S.top n f))

lemma top_comm (n : ℕ) :
    S.topComponent (n+1) ≫ (chains X).d (n+1) n =
      (chains X).d (n+1) n ≫ S.topComponent n := by
  apply hom_ext
  intro f
  simp only [topComponent,← Category.assoc,generator_boundary,
    Preadditive.sum_comp,Preadditive.zsmul_comp,generator_desc]
  simp only [top_face]

def topMap : chains X ⟶ chains X where
  f := S.topComponent
  comm' i j hij := by
    have he : j+1 = i := hij
    subst i
    exact S.top_comm j

def prismComponent (n : ℕ) : (chains X).X n ⟶ (chains X).X (n+1) :=
  desc (fun f => generator (ContinuousMap.id (Std n)) ≫ prism (S.H n f) n)

lemma identity_prism_zero (f : C(Std 0,X)) :
    generator f =
      generator (ContinuousMap.id (Std 0)) ≫ prism (S.H 0 f) 0 ≫ (chains X).d 1 0 +
      generator (S.top 0 f) := by
  have h := congrArg (fun a => generator (ContinuousMap.id (Std 0)) ≫ a)
    (prism_boundary_zero (S.H 0 f))
  simpa only [Preadditive.comp_add,generator_map,start_eq,ContinuousMap.comp_id,
    Category.assoc,top] using h

lemma lifted_face_prism (n : ℕ) (f : C(Std (n+1),X)) (i : Fin (n+2)) :
    generator (SingularChains.face i) ≫ prism (S.H (n+1) f) n =
      generator (ContinuousMap.id (Std n)) ≫ prism (S.H n (f.comp (SingularChains.face i))) n := by
  rw [← S.hom_face,prism_precomp,← Category.assoc,generator_map,ContinuousMap.comp_id]

lemma identity_prism_succ (n : ℕ) (f : C(Std (n+1),X)) :
    generator f =
      (∑ i : Fin (n+2), (-1:ℤ)^i.val •
        (generator (ContinuousMap.id (Std n)) ≫ prism (S.H n (f.comp (SingularChains.face i))) n)) +
      generator (ContinuousMap.id (Std (n+1))) ≫
        prism (S.H (n+1) f) (n+1) ≫ (chains X).d (n+2) (n+1) +
      generator (S.top (n+1) f) := by
  have h := congrArg (fun a => generator (ContinuousMap.id (Std (n+1))) ≫ a)
    (prism_boundary_succ (S.H (n+1) f) n)
  simp only [Preadditive.comp_add,generator_map,start_eq,ContinuousMap.comp_id,
    ← Category.assoc,generator_boundary,Preadditive.sum_comp,Preadditive.zsmul_comp,
    ContinuousMap.id_comp,S.lifted_face_prism] at h
  exact h

lemma prism_comm_zero :
    𝟙 ((chains X).X 0) = S.prismComponent 0 ≫ (chains X).d 1 0 + S.topComponent 0 := by
  apply hom_ext
  intro f
  simpa only [Category.comp_id,Preadditive.comp_add,prismComponent,topComponent,
    generator_desc_assoc,generator_desc,Category.assoc] using S.identity_prism_zero f

lemma prism_comm_succ (n : ℕ) :
    𝟙 ((chains X).X (n+1)) = (chains X).d (n+1) n ≫ S.prismComponent n +
      S.prismComponent (n+1) ≫ (chains X).d (n+2) (n+1) + S.topComponent (n+1) := by
  apply hom_ext
  intro f
  simpa only [Category.comp_id,Preadditive.comp_add,prismComponent,topComponent,
    generator_desc_assoc,generator_desc,← Category.assoc,generator_boundary,
    Preadditive.sum_comp,Preadditive.zsmul_comp,generator_desc] using S.identity_prism_succ n f

def homComponent (n m : ℕ) : (chains X).X n ⟶ (chains X).X m :=
  if h : n+1 = m then S.prismComponent n ≫ eqToHom (congrArg (chains X).X h) else 0

lemma homComponent_succ (n : ℕ) : S.homComponent n (n+1) = S.prismComponent n := by
  simp [homComponent]

def chainHomotopy : Homotopy (𝟙 (chains X)) S.topMap where
  hom := S.homComponent
  zero i j h := by simp only [ComplexShape.down_Rel] at h; simp [homComponent,h]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex,Homotopy.prevD_chainComplex,zero_add,
        homComponent_succ]
      exact S.prism_comm_zero
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex,Homotopy.prevD_chainComplex,
        homComponent_succ,homComponent_succ]
      exact S.prism_comm_succ n

end Coherent

open Coherent
def tightening {k : ℕ}
    (hπ : ∀ p < k, ∀ x : X, Subsingleton (HomotopyGroup (Fin p) X x)) (x₀ : X) :
    Coherent X where
  H := SingularTightening.hom hπ x₀
  zero := SingularTightening.hom_zero hπ x₀
  face := SingularTightening.hom_face hπ x₀

lemma tightening_top {k : ℕ}
    (hπ : ∀ p < k, ∀ x : X, Subsingleton (HomotopyGroup (Fin p) X x)) (x₀ : X)
    (n : ℕ) (hn : n < k) (f : C(Std n,X)) :
    (tightening hπ x₀).top n f = ContinuousMap.const _ x₀ := by
  ext s
  exact SingularTightening.hom_top hπ x₀ n hn f s

end

open CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma homologyMap_congr_component {f g : chains X ⟶ chains Y} (n : ℕ)
    (h : f.f n = g.f n) : homologyMap f n = homologyMap g n := by
  apply (cancel_epi ((chains X).homologyπ n)).1
  rw [homologyπ_naturality,homologyπ_naturality]
  congr 1
  apply (cancel_mono ((chains Y).iCycles n)).1
  simp only [cyclesMap_i,h]

lemma homologyMap_const (n : ℕ) (hn : n ≠ 0) (y : Y) :
    homologyMap (map (ContinuousMap.const X y)) n = 0 := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  have hz : CategoryTheory.Limits.IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of PUnit) hn
  change F.map (TopCat.ofHom (ContinuousMap.const X y)) = 0
  have he : TopCat.ofHom (ContinuousMap.const X y) =
      TopCat.ofHom (ContinuousMap.const X PUnit.unit) ≫
        TopCat.ofHom (ContinuousMap.const PUnit y) := rfl
  rw [he,F.map_comp,hz.eq_of_src (F.map (TopCat.ofHom (ContinuousMap.const PUnit y))) 0,
    comp_zero]

lemma tightening_component {k : ℕ}
    (hπ : ∀ p < k, ∀ x : X, Subsingleton (HomotopyGroup (Fin p) X x)) (x₀ : X)
    (n : ℕ) (hn : n < k) :
    ((tightening hπ x₀).topMap).f n = (map (ContinuousMap.const X x₀)).f n := by
  apply SingularChains.hom_ext
  intro f
  change generator f ≫ desc _ = _
  rw [generator_desc,generator_map,tightening_top hπ x₀ n hn]
  rfl

theorem homology_isZero_of_low_homotopy {k : ℕ}
    (hπ : ∀ p < k, ∀ x : X, Subsingleton (HomotopyGroup (Fin p) X x)) (x₀ : X)
    (n : ℕ) (hn : n < k) (hn₀ : n ≠ 0) : IsZero ((chains X).homology n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have he := (tightening hπ x₀).chainHomotopy.homologyMap_eq n
  rw [homologyMap_id,homologyMap_congr_component n (tightening_component hπ x₀ n hn),
    homologyMap_const n hn₀ x₀] at he
  exact he

end SingularNormalization

end

end OAI
