import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.TranslationCoefficientAction
import OAI.GroupTheory.SimpleAmenable.Simplicial.ConstantCoefficient
import OAI.GroupTheory.SimpleAmenable.Homology.GroupoidComponentHomology

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularCoefficient
open CoefficientNerve FreeChains

private lemma iso_transport_cancel {V : Type*} [Category V] {A B C D : V}
    (a : A ≅ B) (b : C ≅ D) (f : A ⟶ C) (g : B ⟶ D)
    (h : f = a.hom ≫ g ≫ b.inv) : f ≫ b.hom = a.hom ≫ g := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma inverse_square_of_identity {V : Type*} [Category V] {X Y Z T : V}
    (a : X ≅ Y) (b : X ≅ Z) (f : Y ⟶ Z) (g : X ⟶ T)
    (h : 𝟙 X ≫ b.hom = a.hom ≫ f) : f ≫ b.inv ≫ g = a.inv ≫ g ≫ 𝟙 T := by
  simp only [Category.id_comp] at h
  apply (cancel_epi a.hom).mp
  simp only [← Category.assoc, ← h, Iso.hom_inv_id, Category.id_comp, Category.comp_id]

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
noncomputable def coeffComplex : ChainComplex (SingleObj P ⥤ A) ℕ :=
  ExactShapeHomology.complex (representation F ⋙ alternatingFaceMapComplex A)
noncomputable def evalHomology (n:ℕ) (p:SingleObj P) :
    (CoefficientNerve.complex F).homology n ≅ ((coeffComplex F).homology n).obj p :=
  ExactShapeHomology.evaluationHomology (representation F ⋙ alternatingFaceMapComplex A) n p
lemma evalHomology_natural (n:ℕ) {p q:SingleObj P} (f:p⟶q) :
    homologyMap (((representation F ⋙ alternatingFaceMapComplex A).map f)) n ≫
      (evalHomology F n q).hom =
      (evalHomology F n p).hom ≫ ((coeffComplex F).homology n).map f := by
  have h:=ShortComplex.homologyMap_mapNatTrans ((coeffComplex F).sc n)
    ((evaluation (SingleObj P) A).map f)
  change homologyMap (((representation F ⋙ alternatingFaceMapComplex A).map f)) n =
    (evalHomology F n p).hom ≫ ((coeffComplex F).homology n).map f ≫
      (evalHomology F n q).inv at h
  exact iso_transport_cancel _ _ _ _ h
noncomputable def homologyZeroIso : (coeffComplex F).homology 0 ≅
    constant (C:=SingleObj P) (colimit F) :=
  NatIso.ofComponents (fun p=>(evalHomology F 0 p).symm ≪≫ zeroIso F) (by
    intro p q f
    have h:=evalHomology_natural F 0 f
    change homologyMap ((alternatingFaceMapComplex A).map (action F f)) 0 ≫
      (evalHomology F 0 q).hom = (evalHomology F 0 p).hom ≫ ((coeffComplex F).homology 0).map f at h
    rw [homology_action_zero] at h
    exact inverse_square_of_identity (evalHomology F 0 p) (evalHomology F 0 q)
      _ (zeroIso F).hom h)

lemma positive_isZero (n:ℕ) (hn:n≠0) : IsZero ((coeffComplex F).homology n) := by
  apply Functor.isZero
  intro p
  exact IsZero.of_iso (positive_acyclic F n hn) (evalHomology F n p).symm
noncomputable def double : HomologicalComplex₂ A c c := CoefficientNerve.double (coeffComplex F)
noncomputable def rowZeroIso : TotalFiniteness.row (double F) 0 ≅ complex (constant (C:=SingleObj P) (colimit F)) :=
  CoefficientNerve.rowIso (coeffComplex F) 0 ≪≫
    (alternatingFaceMapComplex A).mapIso (CoefficientNerve.functor.mapIso (homologyZeroIso F))
lemma row_positive_isZero (n q:ℕ) (hq:q≠0) : IsZero ((TotalFiniteness.row (double F) q).homology n) := by
  apply IsZero.of_iso _ ((homologyFunctor A c n).mapIso (CoefficientNerve.rowIso (coeffComplex F) q))
  exact Functor.map_isZero (CoefficientNerve.functor ⋙ alternatingFaceMapComplex A ⋙ homologyFunctor A c n)
    (positive_isZero F q hq)
lemma total_finite [Module.Finite ℤ (colimit F : A)] (n:ℕ)
    (h:∀i,i≤n → Module.Finite ℤ ((nerve (SingleObj P)ᵒᵖ).homology Z i : A)) :
    Module.Finite ℤ (((double F).total c).homology n) := by
  apply TotalFiniteness.finite
  intro p q hpq
  by_cases hq:q=0
  · subst q
    apply (Module.Finite.equiv_iff ((homologyFunctor A c p).mapIso (rowZeroIso F)).symm.toLinearEquiv).mp
    exact constant_finite (C:=SingleObj P) (colimit F) p (fun i hi=>h i (by omega))
  · have :=ModuleCat.isZero_iff_subsingleton.mp (row_positive_isZero F p q hq)
    infer_instance
end RegularCoefficient

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite
namespace RegularCoordinates
open CoefficientNerve RegularTranslation

variable {P:Type} [CommMonoid P]
abbrev B (n:ℕ) := Simplex (SingleObj P) n
lemma opposite_eqToHom_val {x y:Opposite (C (P:=P))} (h:x=y) : (eqToHom h).unop.hom=(1:P) := by subst y; rfl
lemma single_eqToHom_val {x y:Opposite (SingleObj P)} (h:x=y) : (eqToHom h).unop=(1:P) := by subst y; rfl
noncomputable def lift {n:ℕ} (p:P) (s:B (P:=P) n) : Simplex (C (P:=P)) n where
  obj i := op ((ActionCategory.objEquiv P P) ((s.map (homOfLE (Fin.le_last i))).unop * p))
  map {i j} f := (show ((ActionCategory.objEquiv P P) ((s.map (homOfLE (Fin.le_last j))).unop * p)) ⟶
      ((ActionCategory.objEquiv P P) ((s.map (homOfLE (Fin.le_last i))).unop * p)) from
    ⟨(s.map f).unop,by
      change (s.map f).unop * ((s.map (homOfLE (Fin.le_last j))).unop * p)=_
      rw [←mul_assoc]
      have h:=congrArg Quiver.Hom.unop (s.map_comp f (homOfLE (Fin.le_last j)))
      change (s.map (f ≫ homOfLE (Fin.le_last j))).unop=
        (s.map f).unop * (s.map (homOfLE (Fin.le_last j))).unop at h
      rw [←h]
      rfl⟩).op
  map_id i := by apply Quiver.Hom.unop_inj; apply Functor.Elements.hom_ext; exact congrArg Quiver.Hom.unop (s.map_id i)
  map_comp f g := by apply Quiver.Hom.unop_inj; apply Functor.Elements.hom_ext; exact congrArg Quiver.Hom.unop (s.map_comp f g)
lemma lift_right {n:ℕ} (p:P) (s:B (P:=P) n) : (lift p s).right.unop.back=p := by
  change (s.map (𝟙 _)).unop * p=p
  rw [s.map_id]
  exact one_mul _
lemma lift_project {n:ℕ} (p:P) (s:B (P:=P) n) : lift p s ⋙ (ActionCategory.π P P).op=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Quiver.Hom.unop_inj
    simp only [unop_comp,single_eqToHom_val,SingleObj.comp_as_mul,one_mul,mul_one]
    rfl
  · intro i; exact Subsingleton.elim _ _
lemma lift_recover {n:ℕ} (s:Simplex (C (P:=P)) n) :
    lift s.right.unop.back (s ⋙ (ActionCategory.π P P).op)=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    simp only [unop_comp,ActionCategory.comp_hom,opposite_eqToHom_val,one_mul,mul_one]
    rfl
  · intro i
    apply unop_injective
    apply (ActionCategory.objEquiv P P).symm.injective
    exact (s.map (homOfLE (Fin.le_last i))).unop.map_val
noncomputable def coordinates (n:ℕ) : Simplex (C (P:=P)) n ≃ P × B (P:=P) n where
  toFun s := (s.right.unop.back,s ⋙ (ActionCategory.π P P).op)
  invFun x := lift x.1 x.2
  left_inv := lift_recover
  right_inv x := Prod.ext (lift_right x.1 x.2) (lift_project x.1 x.2)
lemma shift_right {n:ℕ} (q:P) (s:Simplex (C (P:=P)) n) :
    (ComposableArrows.right (s ⋙ (shift q).op)).unop.back=q*s.right.unop.back := rfl
lemma shift_project {n:ℕ} (q:P) (s:Simplex (C (P:=P)) n) :
    (s ⋙ (shift q).op) ⋙ (ActionCategory.π P P).op = s ⋙ (ActionCategory.π P P).op := by
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Quiver.Hom.unop_inj
    simp only [unop_comp,single_eqToHom_val,SingleObj.comp_as_mul,one_mul,mul_one]
    rfl
  · intro i; exact Subsingleton.elim _ _
lemma shift_lift {n:ℕ} (q p:P) (s:B (P:=P) n) :
    lift p s ⋙ (shift q).op=lift (q*p) s := by
  apply (coordinates n).injective
  apply Prod.ext
  · change (ComposableArrows.right (lift p s ⋙ (shift q).op)).unop.back=(lift (q*p) s).right.unop.back
    rw [shift_right,lift_right,lift_right]
  · change (lift p s ⋙ (shift q).op) ⋙ (ActionCategory.π P P).op=lift (q*p) s ⋙ (ActionCategory.π P P).op
    rw [shift_project,lift_project,lift_project]
end RegularCoordinates

end OAI
