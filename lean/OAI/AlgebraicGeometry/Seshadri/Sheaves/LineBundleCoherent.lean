import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model

namespace OAI

section
noncomputable section
                                            
section
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

def freeUnitIso {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{0}) [HasColimits (SheafOfModules R)] :
    SheafOfModules.free (R := R) PUnit.{1} ≅ SheafOfModules.unit R := by
  change (∐ fun _ : PUnit.{1} => SheafOfModules.unit R) ≅ SheafOfModules.unit R
  refine
    { hom := Sigma.desc (fun _ => 𝟙 _)
      inv := Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  ·
    apply Sigma.hom_ext
    intro i
    cases i
    rw [Sigma.ι_comp_desc_assoc]
    change 𝟙 (SheafOfModules.unit R) ≫
      Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit =
      Sigma.ι (fun _ : PUnit.{1} => SheafOfModules.unit R) PUnit.unit ≫
        𝟙 (∐ fun _ : PUnit.{1} => SheafOfModules.unit R)
    simp only [Category.id_comp, Category.comp_id]
  · simp

variable {X : Scheme.{0}}

def overFrame {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)

variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}} [HasSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat]

def frameGenerators {M : SheafOfModules R} (e : M ≅ SheafOfModules.unit R) :
    M.GeneratingSections where
  I := PUnit.{1}
  s := M.freeHomEquiv ((freeUnitIso R).hom ≫ e.inv)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

instance frameGenerators_finite {M : SheafOfModules R}
    (e : M ≅ SheafOfModules.unit R) : (frameGenerators e).IsFiniteType where
  finite := inferInstanceAs (Finite PUnit.{1})

instance frameGenerators_isIso {M : SheafOfModules R}
    (e : M ≅ SheafOfModules.unit R) : IsIso (frameGenerators e).π := by
  change IsIso ((M.freeHomEquiv (I := PUnit.{1})).symm
    (M.freeHomEquiv ((freeUnitIso R).hom ≫ e.inv)))
  rw [Equiv.symm_apply_apply]
  infer_instance

def LineBundle.localGenerators (L : LineBundle X) : L.sheaf.LocalGeneratorsData where
  I := X
  X x := (L.locallyRankOne x).choose
  coversTop := by
    rw [Opens.coversTop_iff, IsOpenCover]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, (L.locallyRankOne x).choose_spec.1⟩
  generators x := frameGenerators (overFrame (L.locallyRankOne x).choose_spec.2.some)

instance LineBundle.localGenerators_locallyFree (L : LineBundle X) :
    L.localGenerators.IsLocallyFreeData where
  isIso _x := frameGenerators_isIso _

instance LineBundle.locallyFree (L : LineBundle X) : L.sheaf.IsLocallyFree :=
  L.localGenerators.isLocallyFree

instance LineBundle.quasicoherent (L : LineBundle X) : L.sheaf.IsQuasicoherent :=
  L.localGenerators.quasiCoherentData.isQuasicoherent

instance LineBundle.finitePresentation (L : LineBundle X) : L.sheaf.IsFinitePresentation where
  exists_quasicoherentData := by
    let q := L.localGenerators.quasiCoherentData
    have : q.IsFinitePresentation := by
      constructor
      intro i
      constructor
      · exact frameGenerators_finite _
      · constructor
        exact inferInstanceAs (Finite (ULift Empty))
    exact ⟨q, inferInstance⟩

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
