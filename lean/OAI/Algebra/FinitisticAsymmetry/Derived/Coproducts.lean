import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u v w t
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type t} {c : ComplexShape ι} {I : Type w}
variable {K : I → HomologicalComplex C c}

def cofanEvalIsColimit (s : Cofan K) (hs : IsColimit s)
    [HasColimitsOfShape (Discrete I) C] (j : ι) :
    IsColimit (Cofan.mk (s.pt.X j) (fun i => (s.inj i).f j)) :=
  (Cofan.isColimitMapCoconeEquiv (eval C c j) K s)
    (isColimitOfPreserves (eval C c j) hs)

def homotopyCofanDesc (s : Cofan K) (hs : IsColimit s)
    [HasColimitsOfShape (Discrete I) C] {Y : HomologicalComplex C c}
    (f g : s.pt ⟶ Y) (h : ∀ i, Homotopy (s.inj i ≫ f) (s.inj i ≫ g)) : Homotopy f g where
  hom j l := (cofanEvalIsColimit s hs j).desc (Cofan.mk _ fun i => (h i).hom j l)
  zero j l hrel := by
    apply (cofanEvalIsColimit s hs j).hom_ext
    intro i
    simp only [comp_zero]
    change (s.inj i.as).f j ≫ _ = 0
    rw [show (s.inj i.as).f j ≫ (cofanEvalIsColimit s hs j).desc
      (Cofan.mk _ fun i => (h i).hom j l) = (h i.as).hom j l from
        (cofanEvalIsColimit s hs j).fac _ i]
    exact (h i.as).zero j l hrel
  comm j := by
    apply (cofanEvalIsColimit s hs j).hom_ext
    intro i
    have hh := (h i.as).comm j
    dsimp only [HomologicalComplex.comp_f] at hh
    have fac (a b : ι) : (s.inj i.as).f a ≫
        (cofanEvalIsColimit s hs a).desc (Cofan.mk _ fun i => (h i).hom a b) =
          (h i.as).hom a b := (cofanEvalIsColimit s hs a).fac _ i
    let a : s.pt.X (c.next j) ⟶ Y.X j :=
      (cofanEvalIsColimit s hs (c.next j)).desc (Cofan.mk _ fun i => (h i).hom (c.next j) j)
    let b : s.pt.X j ⟶ Y.X (c.prev j) :=
      (cofanEvalIsColimit s hs j).desc (Cofan.mk _ fun i => (h i).hom j (c.prev j))
    change (s.inj i.as).f j ≫ f.f j = (s.inj i.as).f j ≫
      (s.pt.d j (c.next j) ≫ a + b ≫ Y.d (c.prev j) j + g.f j)
    dsimp only [a, b]
    rw [Preadditive.comp_add, Preadditive.comp_add,
      (s.inj i.as).comm_assoc, fac, ← Category.assoc, fac]
    exact hh

def quotientCofanIsColimit (s : Cofan K) (hs : IsColimit s)
    [HasColimitsOfShape (Discrete I) C] :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient C c).obj s.pt)
      (fun i => (HomotopyCategory.quotient C c).map (s.inj i))) := by
  let Q := HomotopyCategory.quotient C c
  refine Cofan.IsColimit.mk _
    (fun t => Q.map (hs.desc (Cofan.mk t.pt.as (fun i => (t.inj i).out)))) ?_ ?_
  · intro t i
    change Q.map (s.inj i) ≫ Q.map _ = _
    rw [← Q.map_comp, Cofan.IsColimit.inj_desc]
    exact HomotopyCategory.quotient_map_out _
  · intro t m hm
    obtain ⟨m, rfl⟩ := Q.map_surjective m
    apply HomotopyCategory.eq_of_homotopy
    apply homotopyCofanDesc s hs
    intro i
    apply HomotopyCategory.homotopyOfEq
    change ∀ i, Q.map (s.inj i) ≫ Q.map m = t.inj i at hm
    rw [Q.map_comp, hm, Cofan.IsColimit.inj_desc]
    exact (HomotopyCategory.quotient_map_out _).symm

end

open CategoryTheory.MorphismProperty
universe u₁ u₂ v₁ v₂ w
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
variable (W : MorphismProperty C) (F : C ⥤ D) [F.IsLocalization W] [F.Additive]
variable [W.HasRightCalculusOfFractions] {I : Type w}
  [HasColimitsOfShape (Discrete I) C] [W.IsStableUnderCoproductsOfShape I]

omit [Preadditive C] [W.HasRightCalculusOfFractions] in
lemma cofan_desc_mem {X Y : I → C} (s : Cofan Y) (hs : IsColimit s)
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, W (f i)) :
    W (Sigma.desc (fun i => f i ≫ s.inj i)) := by
  exact IsStableUnderColimitsOfShape.condition _ _ _ _
    (colimit.isColimit (Discrete.functor X)) hs
    (Discrete.natTrans fun i => f i.as) (fun i => hf i.as) _
    (fun i => by
      change Sigma.ι X i.as ≫ _ = f i.as ≫ s.inj i.as
      exact Sigma.ι_comp_desc _ _)

include W

lemma localizationCofan_zero {X : I → C} (s : Cofan X) (hs : IsColimit s)
    {Y : C} (d : F.obj s.pt ⟶ F.obj Y)
    (hd : ∀ i, F.map (s.inj i) ≫ d = 0) : d = 0 := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction F W d
  let ρ (i : I) : W.RightFraction (X i) φ.X' :=
    (LeftFraction.mk (s.inj i) φ.s φ.hs).rightFraction
  have hρ (i : I) : (ρ i).s ≫ s.inj i = (ρ i).f ≫ φ.s :=
    (LeftFraction.mk (s.inj i) φ.s φ.hs).rightFraction_fac
  have hz (i : I) : F.map ((ρ i).f ≫ φ.f) = F.map (0 : (ρ i).X' ⟶ Y) := by
    have hr := congrArg (fun f => F.map (ρ i).s ≫ f) (hd i)
    rw [hφ] at hr
    simpa only [RightFraction.map, comp_zero, ← F.map_comp_assoc, hρ,
      F.map_comp, Category.assoc, IsIso.hom_inv_id_assoc, F.map_zero] using hr
  have hex (i : I) := (W.map_eq_iff_precomp F ((ρ i).f ≫ φ.f) 0).mp (hz i)
  choose Z t ht htf using hex
  let q : (∐ Z) ⟶ φ.X' := Sigma.desc (fun i => t i ≫ (ρ i).f)
  have hq : W (q ≫ φ.s) := by
    have eq : q ≫ φ.s = Sigma.desc (fun i => (t i ≫ (ρ i).s) ≫ s.inj i) := by
      apply Sigma.hom_ext
      intro i
      simp only [q, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc, hρ]
    rw [eq]
    exact cofan_desc_mem W s hs _ (fun i => W.comp_mem _ _ (ht i) (ρ i).hs)
  have hqf : q ≫ φ.f = 0 := by
    apply Sigma.hom_ext
    intro i
    simpa only [q, Sigma.ι_comp_desc_assoc, comp_zero, Category.assoc] using htf i
  let : IsIso (F.map (q ≫ φ.s)) := Localization.inverts F W _ hq
  apply (cancel_epi (F.map (q ≫ φ.s))).mp
  rw [comp_zero, F.map_comp, hφ]
  let : IsIso (F.map φ.s) := Localization.inverts F W _ φ.hs
  simp only [RightFraction.map, Category.assoc]
  rw [IsIso.hom_inv_id_assoc, ← F.map_comp, hqf, F.map_zero]

lemma localizationCofan_hom_ext {X : I → C} (s : Cofan X) (hs : IsColimit s)
    {Y : C} (f g : F.obj s.pt ⟶ F.obj Y)
    (h : ∀ i, F.map (s.inj i) ≫ f = F.map (s.inj i) ≫ g) : f = g := by
  apply sub_eq_zero.mp
  exact localizationCofan_zero W F s hs (f - g) (fun i => by simp [Preadditive.comp_sub, h i])

omit [Preadditive C] [Preadditive D] [F.Additive] in
lemma localizationCofan_lift {X : I → C} (s : Cofan X) (hs : IsColimit s)
    {Y : C} (f : ∀ i, F.obj (X i) ⟶ F.obj Y) :
    ∃ g : F.obj s.pt ⟶ F.obj Y, ∀ i, F.map (s.inj i) ≫ g = f i := by
  choose φ hφ using fun i => Localization.exists_rightFraction F W (f i)
  let q : (∐ fun i => (φ i).X') ⟶ s.pt := Sigma.desc (fun i => (φ i).s ≫ s.inj i)
  have hq : W q := cofan_desc_mem W s hs _ (fun i => (φ i).hs)
  let : IsIso (F.map q) := Localization.inverts F W _ hq
  let p : (∐ fun i => (φ i).X') ⟶ Y := Sigma.desc (fun i => (φ i).f)
  refine ⟨inv (F.map q) ≫ F.map p, ?_⟩
  intro i
  apply (cancel_epi (F.map (φ i).s)).mp
  have he : F.map (φ i).s ≫ F.map (s.inj i) =
      F.map (Sigma.ι (fun i => (φ i).X') i) ≫ F.map q := by
    simp only [← F.map_comp, q, Sigma.ι_comp_desc]
  rw [← Category.assoc, he, Category.assoc, IsIso.hom_inv_id_assoc,
    ← F.map_comp,
    show Sigma.ι (fun i => (φ i).X') i ≫ p = (φ i).f from Sigma.ι_comp_desc _ _, hφ]
  simp only [RightFraction.map, IsIso.hom_inv_id_assoc]

def localizationCofanIsColimit {X : I → C} (s : Cofan X) (hs : IsColimit s) :
    IsColimit (Cofan.mk (F.obj s.pt) (fun i => F.map (s.inj i))) := by
  letI : F.EssSurj := Localization.essSurj F W
  let lift (t : Cofan (fun i => F.obj (X i))) : F.obj s.pt ⟶ t.pt :=
    (localizationCofan_lift W F s hs (fun i => t.inj i ≫ (F.objObjPreimageIso t.pt).inv)).choose ≫
      (F.objObjPreimageIso t.pt).hom
  have fac (t : Cofan (fun i => F.obj (X i))) (i : I) :
      F.map (s.inj i) ≫ lift t = t.inj i := by
    dsimp only [lift]
    rw [← Category.assoc, (localizationCofan_lift W F s hs _).choose_spec i]
    simp
  refine Cofan.IsColimit.mk _ lift fac ?_
  intro t m hm
  apply (cancel_mono (F.objObjPreimageIso t.pt).inv).mp
  apply localizationCofan_hom_ext W F s hs
  intro i
  rw [← Category.assoc, ← Category.assoc, fac]
  exact congrArg (fun f => f ≫ (F.objObjPreimageIso t.pt).inv) (hm i)

end LittleFinitistic.DerivedSupport

end

end OAI
