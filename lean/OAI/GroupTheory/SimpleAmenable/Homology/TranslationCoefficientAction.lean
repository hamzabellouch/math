import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.Coefficient
import OAI.GroupTheory.SimpleAmenable.Simplicial.CoefficientNaturality

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace RegularTranslation

variable {P:Type} [CommMonoid P]
abbrev C := ActionCategory P P
lemma eqToHom_val {x y:C (P:=P)} (h:x=y) : (eqToHom h).hom=(1:P) := by subst y; rfl
noncomputable def shift (p:P) : C (P:=P) ⥤ C (P:=P) where
  obj x := (p*x.back:P)
  map f := ⟨f.hom,by change f.hom*(p*_)=_; rw [mul_left_comm]; exact congrArg (p*·) f.map_val⟩
  map_id _ := rfl
  map_comp _ _ := rfl
lemma shift_one : shift (1:P)=𝟭 (C (P:=P)) := by
  apply CategoryTheory.Functor.ext
  · intro x y f; apply Functor.Elements.hom_ext
    simp only [ActionCategory.comp_hom,eqToHom_val,one_mul,mul_one]; rfl
  · intro x; apply (ActionCategory.objEquiv P P).symm.injective; exact one_mul _
lemma shift_mul (p q:P) : shift (p*q)=shift p ⋙ shift q := by
  apply CategoryTheory.Functor.ext
  · intro x y f; apply Functor.Elements.hom_ext
    simp only [ActionCategory.comp_hom,eqToHom_val,one_mul,mul_one]; rfl
  · intro x; apply (ActionCategory.objEquiv P P).symm.injective
    change (p*q)*x.back=q*(p*x.back)
    simp only [mul_assoc,mul_left_comm]
noncomputable def forward (p:P) : 𝟭 (C (P:=P)) ⟶ shift p where
  app x := ⟨p,rfl⟩
  naturality x y f := by apply Functor.Elements.hom_ext; exact mul_comm _ _
end RegularTranslation
namespace RegularCoefficient
open CoefficientNerve RegularTranslation

private lemma comp_step {V : Type*} [Category V] {A B C D E : V}
    {i : A ⟶ B} {f : B ⟶ C} {g : C ⟶ D} {a : A ⟶ E}
    {j : E ⟶ C} {k : E ⟶ D}
    (hf : i ≫ f = a ≫ j) (hg : j ≫ g = k) : i ≫ f ≫ g = a ≫ k := by
  rw [← Category.assoc, hf, Category.assoc, hg]

private lemma comp_pair {V : Type*} [Category V] {A B C D E F : V}
    {i : A ⟶ B} {f : B ⟶ C} {g : C ⟶ D} {a : A ⟶ E}
    {j : E ⟶ C} {b : E ⟶ F} {k : F ⟶ D}
    (h₁ : i ≫ f = a ≫ j) (h₂ : j ≫ g = b ≫ k) :
    i ≫ f ≫ g = (a ≫ b) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

variable {P:Type} [CommMonoid P] {R:Type} [CommRing R]
variable (F:ActionCategory P P ⥤ ModuleCat.{0} R)
noncomputable def action (p:P) : simplicial F ⟶ simplicial F :=
  mapNat (Functor.whiskerRight (forward p) F) ≫ post (shift p) F
@[reassoc] lemma single_action (p:P) {n:ℕ} (s:Simplex (ActionCategory P P) n) :
    single F s ≫ (action F p).app (op ⦋n⦌)=F.map ((forward p).app s.right.unop) ≫ single F (s ⋙ (shift p).op) := by
  simp only [action,NatTrans.comp_app]
  exact comp_step (single_mapNat (Functor.whiskerRight (forward p) F) s)
    (single_post (shift p) F n s)
lemma action_one : action F (1:P)=𝟙 _ := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  change single F s ≫ (action F 1).app (op ⦋n.unop.len⦌)=single F s ≫ 𝟙 _
  rw [single_action,Category.comp_id]
  conv_rhs => rw [←Category.id_comp (single F s),←F.map_id s.right.unop]
  apply weighted_eq F (by rw [shift_one]; rfl)
  apply Functor.Elements.hom_ext
  simp only [ActionCategory.comp_hom,eqToHom_val,one_mul]
  rfl
lemma action_mul (p q:P) : action F (p*q)=action F p ≫ action F q := by
  apply NatTrans.ext; funext n
  apply hom_ext; intro s
  change single F s ≫ (action F (p*q)).app (op ⦋n.unop.len⦌)=
    single F s ≫ (action F p).app (op ⦋n.unop.len⦌) ≫ (action F q).app (op ⦋n.unop.len⦌)
  have hc := comp_pair (single_action F p s) (single_action F q (s ⋙ (shift p).op))
  refine (single_action F (p*q) s).trans (Eq.trans ?_ hc.symm)
  rw [← F.map_comp]
  apply weighted_eq F (by rw [shift_mul]; rfl)
  apply Functor.Elements.hom_ext
  simp only [ActionCategory.comp_hom,eqToHom_val,one_mul]
  exact mul_comm p q
noncomputable def representation : SingleObj P ⥤ SimplicialObject (ModuleCat.{0} R) where
  obj _ := simplicial F
  map p := action F p
  map_id _ := action_one F
  map_comp p q := by change action F (q*p)=_; rw [mul_comm q p]; exact action_mul F p q
end RegularCoefficient

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] {K L:ChainComplex (ModuleCat.{0} R) ℕ}
@[reassoc] lemma zeroπ_natural (f:K⟶L) : f.f 0 ≫ zeroπ L=zeroπ K ≫ homologyMap f 0 := by
  simp only [zeroπ,Category.assoc,_root_.ChainComplex.isoHomologyι₀_inv_naturality,HomologicalComplex.p_opcyclesMap_assoc]
end ChainComplex
namespace RegularCoefficient
open CoefficientNerve RegularTranslation

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ ModuleCat.{0} ℤ)
lemma zeroι_action (p:P) (x:ActionCategory P P) :
    zeroι F x ≫ homologyMap ((alternatingFaceMapComplex _).map (action F p)) 0=zeroι F x := by
  dsimp only [zeroι]
  erw [Category.assoc,←ChainComplex.zeroπ_natural,←Category.assoc]
  change (single F (ComposableArrows.mk₀ (op x)) ≫ (action F p).app (op ⦋0⦌)) ≫ _ = _
  erw [single_action,Category.assoc]
  exact zeroι_naturality F ((forward p).app x)
lemma homology_action_zero (p:P) :
    homologyMap ((alternatingFaceMapComplex _).map (action F p)) 0=𝟙 _ := by
  apply (zeroIsColimit F).hom_ext
  intro x
  exact (zeroι_action F p x).trans (Category.comp_id _).symm
end RegularCoefficient

end OAI
