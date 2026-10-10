import OAI.Algebra.Finitistic.Selected.SelectedTensorComparison
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.SelectedTargetHomology
open QuadraticEncoding SelectedNativeEvaluation FiniteProjectiveHomotopy
universe v
variable {Y : Type v} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
  [Module SelectionRing Y] [IsScalarTower ℂ SelectionRing Y]
abbrev C := ModuleCat.{v} ℂ
abbrev I := derivedTargetInclusion.{0,v} (k := ℂ)
abbrev cohomology (n : ℤ) := I ⋙ DerivedCategory.homologyFunctor C n
instance (n : ℤ) : (cohomology.{v} n).Additive := by dsimp [cohomology]; infer_instance
instance (n : ℤ) : PreservesBinaryBiproducts (cohomology.{v} n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

def stalkIso : I.obj (HDerived (Y := Y)) ≅
    (DerivedCategory.singleFunctor C 0).obj (H (Y := Y)) := Iso.refl _
def shiftedIso : I.obj ((HDerived (Y := Y))⟦(3 : ℤ)⟧) ≅
    (DerivedCategory.singleFunctor C (-3)).obj (H (Y := Y)) :=
  (I.commShiftIso (3 : ℤ)).app _ ≪≫
    (shiftFunctor _ (3 : ℤ)).mapIso (stalkIso (Y := Y)) ≪≫
      ((DerivedCategory.singleFunctors C).shiftIso 3 (-3) 0 (by norm_num)).app _

def stalkHomologyIso : (cohomology 0).obj (HDerived (Y := Y)) ≅ H (Y := Y) :=
  (DerivedCategory.homologyFunctor C 0).mapIso stalkIso ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _
def shiftedHomologyIso : (cohomology (-3)).obj ((HDerived (Y := Y))⟦(3 : ℤ)⟧) ≅ H (Y := Y) :=
  (DerivedCategory.homologyFunctor C (-3)).mapIso shiftedIso ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-3)).app _

lemma single_zero (M : C) (i n : ℤ) (hn : n ≠ i) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.singleFunctor C i).obj M)) := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ i n h
  · exact DerivedCategory.isZero_of_isLE _ i n h
lemma stalk_zero (n : ℤ) (hn : n ≠ 0) :
    IsZero ((cohomology n).obj (HDerived (Y := Y))) :=
  ((DerivedCategory.homologyFunctor C n).mapIso (stalkIso (Y := Y))).isZero_iff.mpr
    (single_zero _ _ _ hn)
lemma shifted_zero (n : ℤ) (hn : n ≠ -3) :
    IsZero ((cohomology n).obj ((HDerived (Y := Y))⟦(3 : ℤ)⟧)) :=
  ((DerivedCategory.homologyFunctor C n).mapIso (shiftedIso (Y := Y))).isZero_iff.mpr
    (single_zero _ _ _ hn)

def targetH0 : (cohomology 0).obj (target (Y := Y)) ≅ H (Y := Y) :=
  (cohomology 0).mapBiprod _ _ ≪≫
    (isoBiprodZero (shifted_zero (Y := Y) 0 (by norm_num))).symm ≪≫ stalkHomologyIso

def targetHm3 : (cohomology (-3)).obj (target (Y := Y)) ≅ H (Y := Y) :=
  (cohomology (-3)).mapBiprod _ _ ≪≫
    (isoZeroBiprod (stalk_zero (Y := Y) (-3) (by norm_num))).symm ≪≫ shiftedHomologyIso

lemma target_zero (n : ℤ) (h0 : n ≠ 0) (hm : n ≠ -3) :
    IsZero ((cohomology n).obj (target (Y := Y))) :=
  ((cohomology n).mapBiprod _ _).isZero_iff.mpr
    ((biprod_isZero_iff _ _).mpr ⟨stalk_zero n h0,shifted_zero n hm⟩)

lemma stalkHomologyIso_hom : (stalkHomologyIso (Y := Y)).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app (H (Y := Y))).hom := by
  change (DerivedCategory.homologyFunctor C 0).map
    (𝟙 ((DerivedCategory.singleFunctor C 0).obj (H (Y := Y)))) ≫ _ = _
  rw [CategoryTheory.Functor.map_id,Category.id_comp]

lemma stalk_action (r : SelectionRing) :
    (cohomology 0).map (HDerivedAction (Y := Y) r) ≫ (stalkHomologyIso (Y := Y)).hom =
      (stalkHomologyIso (Y := Y)).hom ≫ HAction (Y := Y) r := by
  rw [stalkHomologyIso_hom]
  change (DerivedCategory.homologyFunctor C 0).map
    (DerivedCategory.Qh.map ((inclusion ℂ).map (HKAction (Y := Y) r))) ≫ _ = _
  dsimp only [HKAction]
  erw [Functor.map_preimage]
  change (DerivedCategory.homologyFunctor C 0).map
    ((DerivedCategory.singleFunctor C 0).map (HAction (Y := Y) r)) ≫ _ = _
  exact (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.naturality
    (HAction (Y := Y) r)

lemma shifted_action (r : SelectionRing) :
    (cohomology (-3)).map ((HDerivedAction (Y := Y) r)⟦(3 : ℤ)⟧') ≫
      (shiftedHomologyIso (Y := Y)).hom =
        (shiftedHomologyIso (Y := Y)).hom ≫ HAction (Y := Y) r := by
  have hst : I.map (HDerivedAction (Y := Y) r) =
      (DerivedCategory.singleFunctor C 0).map (HAction (Y := Y) r) := by
    change DerivedCategory.Qh.map ((inclusion ℂ).map (HKAction (Y := Y) r)) = _
    dsimp only [HKAction]
    erw [Functor.map_preimage]
    rfl
  have hshift : I.map ((HDerivedAction (Y := Y) r)⟦(3 : ℤ)⟧') ≫ (shiftedIso (Y := Y)).hom =
      (shiftedIso (Y := Y)).hom ≫
        (DerivedCategory.singleFunctor C (-3)).map (HAction (Y := Y) r) := by
    have h1 := (I.commShiftIso (3 : ℤ)).hom.naturality (HDerivedAction (Y := Y) r)
    have h2 := ((DerivedCategory.singleFunctors C).shiftIso 3 (-3) 0 (by norm_num)).hom.naturality
      (HAction (Y := Y) r)
    dsimp only [Functor.comp_map] at h1 h2
    rw [hst] at h1
    have hh := (congrArg (fun f => f ≫
      (((DerivedCategory.singleFunctors C).shiftIso 3 (-3) 0 (by norm_num)).app
        (H (Y := Y))).hom) h1).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun g => (I.commShiftIso (3 : ℤ)).hom.app (HDerived (Y := Y)) ≫ g) h2))
    dsimp only [shiftedIso, stalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom]
    erw [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _).symm)

  have h := congrArg (DerivedCategory.homologyFunctor C (-3)).map hshift
  simp only [Functor.map_comp] at h
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-3)).hom.naturality
    (HAction (Y := Y) r)
  dsimp only [Functor.comp_map,Functor.id_map] at hn
  dsimp only [shiftedHomologyIso,Iso.trans_hom,Functor.mapIso_hom,cohomology,Functor.comp_map]
  rw [← Category.assoc,h,Category.assoc]
  exact (congrArg (fun g => (DerivedCategory.homologyFunctor C (-3)).map
    (shiftedIso (Y := Y)).hom ≫ g) hn).trans (Category.assoc _ _ _).symm

lemma targetH0_hom : (targetH0 (Y := Y)).hom =
    (cohomology 0).map biprod.fst ≫ (stalkHomologyIso (Y := Y)).hom := by
  simp [targetH0,isoBiprodZero]
  erw [biprod.lift_fst_assoc]
lemma targetHm3_hom : (targetHm3 (Y := Y)).hom =
    (cohomology (-3)).map biprod.snd ≫ (shiftedHomologyIso (Y := Y)).hom := by
  simp [targetHm3,isoZeroBiprod]
  erw [biprod.lift_snd_assoc]

lemma targetH0_action (r : SelectionRing) :
    (cohomology 0).map (targetAction (Y := Y) r) ≫ (targetH0 (Y := Y)).hom =
      (targetH0 (Y := Y)).hom ≫ HAction (Y := Y) r := by
  rw [targetH0_hom,← Category.assoc,← Functor.map_comp]
  simp only [targetAction,biprod.map_fst,Functor.map_comp,Category.assoc,stalk_action]
lemma targetHm3_action (r : SelectionRing) :
    (cohomology (-3)).map (targetAction (Y := Y) r) ≫ (targetHm3 (Y := Y)).hom =
      (targetHm3 (Y := Y)).hom ≫ HAction (Y := Y) r := by
  rw [targetHm3_hom,← Category.assoc,← Functor.map_comp]
  simp only [targetAction,biprod.map_snd,Functor.map_comp,Category.assoc,shifted_action]
end LittleFinitistic.SelectedTargetHomology

end

end OAI
