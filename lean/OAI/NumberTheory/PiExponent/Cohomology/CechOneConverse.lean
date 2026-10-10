import OAI.NumberTheory.PiExponent.Cohomology.CechZero
import OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechOneConverse
section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem hasPrimitives_of_ext_one_zero (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hzero : ∀ x : Ext.{u+1} (freeOpen R V) M 1, x = 0) :
    CechHigher.HasPrimitives R U M 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  let : Mono S.f := hS.mono_f
  intro c hc
  have hcI : differential R U S.X₂ (CechHigher.map R U M S.f c) = 0 := by
    rw [← map_differential, hc, CechHigher.map_zero]
  obtain ⟨b, hb⟩ := FreeCechSections.injective_hasPrimitives U R S.X₂ 0
    (CechHigher.map R U M S.f c) hcI
  have hcomp : CechHigher.map R U S.X₂ S.g (CechHigher.map R U M S.f c) = 0 := by
    funext t
    change (c t ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]
  have hclosed : differential R U S.X₃ (CechHigher.map R U S.X₂ S.g b) = 0 := by
    rw [← map_differential, hb, hcomp]
  obtain ⟨g, hg⟩ := CechZero.augmentation_exists R U S.X₃ V hUV hcover _ hclosed
  obtain ⟨t, ht⟩ := CechOne.lift_of_ext_one_zero R S hS V hzero g
  have hkernel : CechHigher.map R U S.X₂ S.g
      (b - augmentation R U S.X₂ V hUV t) = 0 := by
    rw [CechHigher.map_sub, ← CechZero.augmentation_comp, ht, hg, sub_self]
  obtain ⟨a, ha⟩ := lift_kernel_cochain R U S hS _ hkernel
  refine ⟨a, ?_⟩
  apply map_injective R U M S.f
  rw [map_differential, ha, differential_sub, augmentation_closed, sub_zero, hb]

end

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
universe u
variable {Y : Scheme.{u}} {J : Type u} (U : J → Y.Opens) (M : Y.Modules)
local instance : HasExt.{u+1} Y.Modules := HasExt.standard _

private abbrev schemeUnit : Y.Modules := SheafOfModules.unit Y.ringCatSheaf

private abbrev schemeFreeOpen (V : Y.Opens) : Y.Modules := freeOpen Y.ringCatSheaf V

theorem hasPrimitives_of_cohomology_one_zero
    (hcover : (⨆ i, U i) = ⊤)
    (hzero : ∀ x : Ext.{u+1} (C := Y.Modules) schemeUnit M 1, x = 0) :
    CechHigher.HasPrimitives Y.ringCatSheaf U M 0 := by
  let e : schemeFreeOpen ⊤ ≅ schemeUnit :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso Y.ringCatSheaf
  apply hasPrimitives_of_ext_one_zero Y.ringCatSheaf U M ⊤ (fun _ => le_top)
    (by rw [hcover])
  change ∀ x : Ext.{u+1} (C := Y.Modules) (schemeFreeOpen ⊤) M 1, x = 0
  intro x
  have h := congrArg (fun z => (Ext.mk₀ e.hom).comp z (zero_add 1))
    (hzero ((Ext.mk₀ e.inv).comp x (zero_add 1)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end PiExponent.GeometrySupport.CechOneConverse

end

end OAI
