import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace OAI

/-! # Maps and homotopies on cochains computed from representation complexes -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {G : Type} [Group G]
  {P Q R : ChainComplex (Rep k G) ℕ}

def repCochainPrecomp (u : P ⟶ Q) (A : Rep k G) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k A :=
  (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)).map
    ((((linearYoneda k (Rep k G)).obj A).rightOp.mapHomologicalComplex _).map u).op

@[simp] theorem repCochainPrecomp_apply (u : P ⟶ Q) (A : Rep k G)
    (i : ℕ) (f : Q.X i ⟶ A) :
    ((repCochainPrecomp k u A).f i).hom f = u.f i ≫ f := rfl

@[simp] theorem repCochainPrecomp_comp (u : P ⟶ Q) (v : Q ⟶ R) (A : Rep k G) :
    repCochainPrecomp k (u ≫ v) A =
      repCochainPrecomp k v A ≫ repCochainPrecomp k u A := by
  ext i f
  change (u.f i ≫ v.f i) ≫ f = u.f i ≫ (v.f i ≫ f)
  exact Category.assoc _ _ _

@[simp] theorem repCochainPrecomp_id (A : Rep k G) :
    repCochainPrecomp k (𝟙 P) A = 𝟙 _ := by
  ext i f
  exact Category.id_comp f

@[simp] theorem repCochainPrecomp_sub (u v : P ⟶ Q) (A : Rep k G) :
    repCochainPrecomp k (u - v) A = repCochainPrecomp k u A - repCochainPrecomp k v A := by
  ext i f
  change (u.f i - v.f i) ≫ f = u.f i ≫ f - v.f i ≫ f
  exact Preadditive.sub_comp _ _ _

def repCochainHomotopy {u v : P ⟶ Q} (h : Homotopy u v) (A : Rep k G) :
    Homotopy (repCochainPrecomp k u A) (repCochainPrecomp k v A) :=
  (((linearYoneda k (Rep k G)).obj A).rightOp.mapHomotopy h).unop

def repCochainHomotopyEquiv (e : HomotopyEquiv P Q) (A : Rep k G) :
    HomotopyEquiv (Q.linearYonedaObj k A) (P.linearYonedaObj k A) where
  hom := repCochainPrecomp k e.hom A
  inv := repCochainPrecomp k e.inv A
  homotopyHomInvId := by
    simpa only [repCochainPrecomp_comp, repCochainPrecomp_id] using
      repCochainHomotopy k e.homotopyInvHomId A
  homotopyInvHomId := by
    simpa only [repCochainPrecomp_comp, repCochainPrecomp_id] using
      repCochainHomotopy k e.homotopyHomInvId A

def repCochainPostcomp (P : ChainComplex (Rep k G) ℕ) {A B : Rep k G} (u : A ⟶ B) :
    P.linearYonedaObj k A ⟶ P.linearYonedaObj k B where
  f i := ModuleCat.ofHom (Linear.rightComp k (P.X i) u)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change P.d j i ≫ (f ≫ u) = (P.d j i ≫ f) ≫ u
    exact (Category.assoc _ _ _).symm

@[simp] theorem repCochainPostcomp_apply {A B : Rep k G} (u : A ⟶ B)
    (i : ℕ) (f : P.X i ⟶ A) :
    ((repCochainPostcomp k P u).f i).hom f = f ≫ u := rfl

def repCochainPostcompIso (P : ChainComplex (Rep k G) ℕ) {A B : Rep k G} (e : A ≅ B) :
    P.linearYonedaObj k A ≅ P.linearYonedaObj k B where
  hom := repCochainPostcomp k P e.hom
  inv := repCochainPostcomp k P e.inv
  hom_inv_id := by
    ext i f
    change P.X i ⟶ A at f
    change (f ≫ e.hom) ≫ e.inv = f
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    ext i f
    change P.X i ⟶ B at f
    change (f ≫ e.inv) ≫ e.hom = f
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

end PolycyclicRecognition

end

end OAI
