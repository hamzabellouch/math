import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation
import OAI.NumberTheory.PiExponent.Approximation.FrameTensorPowers

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def modulePowRestrict (U : X.Opens) (M : X.Modules) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ modulePow U.toScheme (M.restrict U.ι) n
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
      moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)

lemma modulePowRestrict_natural (U : X.Opens) {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) ≫
      (modulePowRestrict U N n).hom =
    (modulePowRestrict U M n).hom ≫
      modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n := by
  induction n with
  | zero =>
    change (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (structureSheaf X)) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ 𝟙 _
    erw [(Scheme.Modules.restrictFunctor U.ι).map_id, Category.id_comp]
  | succ n hn =>
    change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (modulePowMap f n)) ≫
      ((moduleTensorRestrict U N (modulePow X N n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U N n)).hom) =
      ((moduleTensorRestrict U M (modulePow X M n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)).hom) ≫
          moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
            (modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n)
    simp only [moduleTensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
      ← moduleTensorMap_comp, Category.comp_id, hn]
    rw [Category.assoc, ← moduleTensorMap_comp, Category.id_comp]

lemma modulePowMap_restrict_isIso (U : X.Opens) {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n)) := by
  have h := modulePowRestrict_natural U f n
  have heq : (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) =
      (modulePowRestrict U M n).hom ≫
        modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n ≫
          (modulePowRestrict U N n).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

lemma powerSection_restrict_isIso (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n)) := by
  let := modulePowMap_restrict_isIso U s n
  unfold powerSection
  rw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  infer_instance

lemma sectionOpen_le_powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    sectionOpen X s ≤ sectionOpen X (powerSection s n) := by
  refine iSup_le fun U => iSup_le fun hU => ?_
  let := hU
  exact le_iSup_of_le U (le_iSup_of_le (powerSection_restrict_isIso U s n) le_rfl)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def powerRestrictionUnit (U : X.Opens) (n : ℕ) :
    structureSheaf U.toScheme ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (unitPowerIso n).symm ≪≫
      modulePowRestrict U (structureSheaf X) n ≪≫
        (modulePowFunctor n).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
          unitPowerIso n

lemma restrictPowerSection_factor (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        powerSection (restrictSection U.ι s) n := by
  have hs : (Scheme.Modules.restrictUnitIso U.ι).hom ≫ restrictSection U.ι s =
      (Scheme.Modules.restrictFunctor U.ι).map s := by
    let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let e : F.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
      Scheme.Modules.restrictUnitIso U.ι
    exact e.hom_inv_id_assoc (F.map s)
  dsimp only [restrictSection, powerSection, powerRestrictionUnit, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, modulePowFunctor]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  repeat' erw [Category.assoc]
  erw [modulePowRestrict_natural]
  erw [Iso.hom_inv_id_assoc, ← modulePowMap_comp]
  erw [show (Scheme.Modules.restrictUnitIso U.ι).hom ≫
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map s) =
        (Scheme.Modules.restrictFunctor U.ι).map s from hs]
  rfl

end PiExponentSeshadri.Geometry

end

end OAI
