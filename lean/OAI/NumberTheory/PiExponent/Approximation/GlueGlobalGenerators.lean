import OAI.NumberTheory.PiExponent.Ampleness.CoherentAffineFinite
import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation
import OAI.NumberTheory.PiExponent.Approximation.FrameSections

namespace OAI

namespace PiExponent.GlueGlobalGenerators
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
  (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections)
  (t : ∀ i, (σ i).I → GlobalSections X M)
  (ht : ∀ i j, restrictSection (U i).ι (t i j) =
    (M.restrict (U i).ι).unitHomEquiv.symm ((σ i).s j))

include hcover ht

theorem globalEvaluation_epi : Epi
    (M.freeHomEquiv.symm (fun ij : Σ i, (σ i).I => M.unitHomEquiv (t ij.1 ij.2))) := by
  let q := M.freeHomEquiv.symm (fun ij : Σ i, (σ i).I => M.unitHomEquiv (t ij.1 ij.2))
  have hq (i : ι) (j : (σ i).I) : SheafOfModules.ιFree ⟨i,j⟩ ≫ q = t i j := by
    erw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [q, Equiv.apply_symm_apply]
    exact M.unitHomEquiv.symm_apply_apply (t i j)
  change Epi (C := X.Modules) q
  apply (Preadditive.epi_iff_cancel_zero (C := X.Modules) q).mpr
  intro N g hg
  have hz (i : ι) (j : (σ i).I) : t i j ≫ g = 0 := by
    erw [← hq i j, Category.assoc, hg, comp_zero]
  apply CoherentTwist.eq_zero_of_local
  intro x
  have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U i,hxi,?_⟩
  apply (@cancel_epi _ _ _ _ _ (σ i).π (σ i).epi _ _).mp
  erw [comp_zero]
  apply (SheafOfModules.isColimitFreeCofan (σ i).I).hom_ext
  intro j
  change SheafOfModules.ιFree j.as ≫ ((σ i).π ≫
    (Scheme.Modules.restrictFunctor (U i).ι).map g) = SheafOfModules.ιFree j.as ≫ 0
  erw [comp_zero, ← Category.assoc,
    ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply]
  erw [← ht i j.as]
  let R : X.Modules ⥤ (U i).toScheme.Modules := Scheme.Modules.restrictFunctor (U i).ι
  let e : R.obj (O X) ≅ O (U i).toScheme := Scheme.Modules.restrictUnitIso (U i).ι
  change (e.inv ≫ R.map (t i j.as)) ≫ R.map g = 0
  erw [Category.assoc, ← Functor.map_comp, hz, Functor.map_zero, comp_zero]

def globalGenerators : M.GeneratingSections where
  I := Σ i, (σ i).I
  s ij := M.unitHomEquiv (t ij.1 ij.2)
  epi := globalEvaluation_epi M U hcover σ t ht

instance [Finite ι] [hσ : ∀ i, (σ i).IsFiniteType] :
    (globalGenerators M U hcover σ t ht).IsFiniteType where
  finite := by
    let (i : ι) : Finite (σ i).I := (hσ i).finite
    exact inferInstanceAs (Finite (Σ i, (σ i).I))

theorem exists_finite_global_generators [Finite ι] [∀ i, (σ i).IsFiniteType] :
    ∃ q : M.GeneratingSections, q.IsFiniteType :=
  ⟨globalGenerators M U hcover σ t ht, inferInstance⟩

end
end PiExponent.GlueGlobalGenerators

end OAI
