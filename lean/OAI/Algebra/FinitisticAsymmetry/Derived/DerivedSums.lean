import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Derived.ComplexSums

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v w z
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{z} C]
variable {I : Type w} [HasColimitsOfShape (Discrete I) C]
  [HasExactColimitsOfShape (Discrete I) C]

def derivedHomotopyCofanIsColimit {X : I → HomotopyCategory C (ComplexShape.up ℤ)}
    (s : Cofan X) (hs : IsColimit s) :
    IsColimit (Cofan.mk (DerivedCategory.Qh.obj s.pt)
      (fun i => DerivedCategory.Qh.map (s.inj i))) :=
  localizationCofanIsColimit (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Qh s hs

def derivedCofanIsColimit {X : I → CochainComplex C ℤ} (s : Cofan X) (hs : IsColimit s) :
    IsColimit (Cofan.mk (DerivedCategory.Q.obj s.pt)
      (fun i => DerivedCategory.Q.map (s.inj i))) := by
  let h := derivedHomotopyCofanIsColimit _ (quotientCofanIsColimit s hs)
  let e := DerivedCategory.quotientCompQhIso C
  refine Cofan.IsColimit.mk _ (fun t =>
    (e.app s.pt).inv ≫ h.desc (Cofan.mk t.pt (fun i => (e.app (X i)).hom ≫ t.inj i))) ?_ ?_
  · intro t i
    change DerivedCategory.Q.map (s.inj i) ≫ (e.app s.pt).inv ≫
      h.desc (Cofan.mk t.pt (fun i => (e.app (X i)).hom ≫ t.inj i)) = t.inj i
    have hn : DerivedCategory.Q.map (s.inj i) ≫ (e.app s.pt).inv =
        (e.app (X i)).inv ≫ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (s.inj i)) :=
      e.inv.naturality (s.inj i)
    have hf : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (s.inj i)) ≫
        h.desc (Cofan.mk t.pt (fun j => (e.app (X j)).hom ≫ t.inj j)) =
        (e.app (X i)).hom ≫ t.inj i := h.fac _ (Discrete.mk i)
    rw [← Category.assoc, hn, Category.assoc, hf]
    exact Iso.inv_hom_id_assoc _ _
  · intro t m hm
    apply (cancel_epi (e.app s.pt).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    apply h.hom_ext
    intro i
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (s.inj i.as)) ≫ _ = _
    rw [IsColimit.fac]
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      (s.inj i.as)) ≫ (e.app s.pt).hom ≫ m = (e.app (X i.as)).hom ≫ t.inj i.as
    have hn : DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (s.inj i.as)) ≫ (e.app s.pt).hom =
        (e.app (X i.as)).hom ≫ DerivedCategory.Q.map (s.inj i.as) :=
      e.hom.naturality (s.inj i.as)
    change ∀ i, DerivedCategory.Q.map (s.inj i) ≫ m = t.inj i at hm
    rw [← Category.assoc, hn, Category.assoc, hm]

def derivedSumIsColimit (X : I → CochainComplex C ℤ) :=
  derivedCofanIsColimit _ (sumComplexIsColimit X)

lemma prop_derived_sum (P : ObjectProperty (DerivedCategory C))
    [P.IsClosedUnderColimitsOfShape (Discrete I)] (X : I → CochainComplex C ℤ)
    (hX : ∀ i, P (DerivedCategory.Q.obj (X i))) : P (DerivedCategory.Q.obj (sumComplex X)) :=
  P.prop_of_isColimit (derivedSumIsColimit X) (fun i => hX i.as)

instance derivedHasCoproducts : HasColimitsOfShape (Discrete I) (DerivedCategory C) where
  has_colimit G := by
    let F := DerivedCategory.Qh (C := C)
    let : F.EssSurj := Localization.essSurj F (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    let X (i : I) := F.objPreimage (G.obj ⟨i⟩)
    let e (i : I) := F.objObjPreimageIso (G.obj ⟨i⟩)
    let s : Cofan (fun i => F.obj (X i)) :=
      Cofan.mk (F.obj (∐ X)) (fun i => F.map (Sigma.ι X i))
    let h : IsColimit s := derivedHomotopyCofanIsColimit _ (colimit.isColimit _)
    let t : Cofan (fun i => G.obj ⟨i⟩) :=
      Cofan.mk s.pt (fun i => (e i).inv ≫ s.inj i)
    have ht : IsColimit t := by
      refine Cofan.IsColimit.mk _ (fun z => h.desc (Cofan.mk z.pt
        (fun i => (e i).hom ≫ z.inj i))) ?_ ?_
      · intro z i
        change ((e i).inv ≫ s.inj i) ≫ _ = _
        rw [Category.assoc, Cofan.IsColimit.inj_desc]
        exact Iso.inv_hom_id_assoc _ _
      · intro z m hm
        apply h.hom_ext
        intro i
        rw [IsColimit.fac]
        change s.inj i.as ≫ m = (e i.as).hom ≫ z.inj i.as
        rw [← hm i.as]
        change s.inj i.as ≫ m = (e i.as).hom ≫ ((e i.as).inv ≫ s.inj i.as) ≫ m
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    let : HasColimit (Discrete.functor (fun i : I => G.obj ⟨i⟩)) := ⟨_, ht⟩
    exact hasColimit_of_iso (F := Discrete.functor (fun i : I => G.obj ⟨i⟩))
      (Discrete.natIso (fun i => Iso.refl (G.obj i)))

end LittleFinitistic.DerivedSupport

end

end OAI
