import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Derived.Coproducts

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v w t
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type t} {c : ComplexShape ι} {I : Type w}
variable [HasColimitsOfShape (Discrete I) C]

def bundleComplex (K : I → HomologicalComplex C c) :
    HomologicalComplex (Discrete I ⥤ C) c where
  X j := Discrete.functor (fun i => (K i).X j)
  d j l := Discrete.natTrans (fun i => (K i.as).d j l)
  shape j l hjl := by ext i; exact (K i.as).shape _ _ hjl
  d_comp_d' i j l _ _ := by ext a; exact (K a.as).d_comp_d i j l

def bundleComplexMap {K L : I → HomologicalComplex C c} (f : ∀ i, K i ⟶ L i) :
    bundleComplex K ⟶ bundleComplex L where
  f j := Discrete.natTrans (fun i => (f i.as).f j)
  comm' j l _ := by ext i; exact (f i.as).comm _ _

def sumComplex (K : I → HomologicalComplex C c) : HomologicalComplex C c :=
  (colim.mapHomologicalComplex c).obj (bundleComplex K)

def sumComplexMap {K L : I → HomologicalComplex C c} (f : ∀ i, K i ⟶ L i) :
    sumComplex K ⟶ sumComplex L := (colim.mapHomologicalComplex c).map (bundleComplexMap f)

def sumComplexInj (K : I → HomologicalComplex C c) (i : I) : K i ⟶ sumComplex K where
  f j := Sigma.ι (fun i => (K i).X j) i
  comm' j l _ := by
    exact colimit.ι_map ((bundleComplex K).d j l) (Discrete.mk i)

@[reassoc] lemma sumComplexInj_map {K L : I → HomologicalComplex C c}
    (f : ∀ i, K i ⟶ L i) (i : I) :
    sumComplexInj K i ≫ sumComplexMap f = f i ≫ sumComplexInj L i := by
  ext j
  exact colimit.ι_map ((bundleComplexMap f).f j) (Discrete.mk i)

def sumComplexCofan (K : I → HomologicalComplex C c) : Cofan K :=
  Cofan.mk (sumComplex K) (sumComplexInj K)

def sumComplexIsColimit (K : I → HomologicalComplex C c) : IsColimit (sumComplexCofan K) :=
  HomologicalComplex.isColimitOfEval _ _ (fun j =>
    (Cofan.isColimitMapCoconeEquiv (eval C c j) K (sumComplexCofan K)).symm
      (colimit.isColimit (Discrete.functor (fun i => (K i).X j))))

lemma sumComplexMap_quasiIso [HasExactColimitsOfShape (Discrete I) C]
    {K L : I → HomologicalComplex C c} (f : ∀ i, K i ⟶ L i) [∀ i, QuasiIso (f i)] :
    QuasiIso (sumComplexMap f) := by
  have : QuasiIso (bundleComplexMap f) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro i
    change QuasiIso (f i.as)
    infer_instance
  exact inferInstanceAs (QuasiIso ((colim.mapHomologicalComplex c).map (bundleComplexMap f)))

def homotopySumCofan (X : I → HomotopyCategory C c) : Cofan X :=
  Cofan.mk ((HomotopyCategory.quotient C c).obj (sumComplex (fun i => (X i).as)))
    (fun i => (HomotopyCategory.quotient C c).map (sumComplexInj (fun j => (X j).as) i))

def homotopySumIsColimit (X : I → HomotopyCategory C c) :
    IsColimit (homotopySumCofan X) :=
  quotientCofanIsColimit _ (sumComplexIsColimit (fun i => (X i).as))

instance homotopyHasCoproducts : HasColimitsOfShape (Discrete I) (HomotopyCategory C c) where
  has_colimit F := by
    let X (i : I) := F.obj ⟨i⟩
    let : HasColimit (Discrete.functor X) := ⟨_, homotopySumIsColimit X⟩
    exact hasColimit_of_iso (F := Discrete.functor X)
      (Discrete.natIso (fun i => Iso.refl (F.obj i)))

instance homotopyQuasiIsoCoproducts [HasExactColimitsOfShape (Discrete I) C] :
    (HomotopyCategory.quasiIso C c).IsStableUnderCoproductsOfShape I := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X Y _ _ f hf
  let Q := HomotopyCategory.quotient C c
  let a := (colimit.isColimit (Discrete.functor X)).coconePointUniqueUpToIso (homotopySumIsColimit X)
  let b := (colimit.isColimit (Discrete.functor Y)).coconePointUniqueUpToIso (homotopySumIsColimit Y)
  have hq (i : I) : QuasiIso (f i).out := by
    rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomotopyCategory.quotient_map_out]
    exact hf i
  have h : HomotopyCategory.quasiIso C c (Q.map (sumComplexMap (fun i => (f i).out))) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact sumComplexMap_quasiIso _
  refine ((HomotopyCategory.quasiIso C c).arrow_mk_iso_iff ?_).2 h
  refine Arrow.isoMk a b ?_
  apply Sigma.hom_ext
  intro i
  have ha : Sigma.ι X i ≫ a.hom = Q.map (sumComplexInj (fun j => (X j).as) i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk i)
  have hb : Sigma.ι Y i ≫ b.hom = Q.map (sumComplexInj (fun j => (Y j).as) i) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk i)
  change Sigma.ι X i ≫ a.hom ≫ Q.map (sumComplexMap (fun i => (f i).out)) =
    Sigma.ι X i ≫ Limits.Sigma.map f ≫ b.hom
  erw [Sigma.ι_map_assoc, hb, ← Category.assoc, ha, ← Q.map_comp, sumComplexInj_map,
    Q.map_comp, HomotopyCategory.quotient_map_out]
  rfl

end LittleFinitistic.DerivedSupport

end

end OAI
