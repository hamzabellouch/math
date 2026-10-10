import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralRepresentationMap
import Mathlib.RepresentationTheory.Subrepresentation

namespace OAI

/-! # The categorical kernel and its concrete group-ring module -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] Submodule.module
variable {G : Type} [Group G] {A B C : Rep.{0} ℤ G}

abbrev integralKernelObject (f : A ⟶ B) : Rep ℤ G := by
  letI : Module ℤ f.hom.ker.toSubmodule := f.hom.ker.toSubmodule.module
  exact Rep.of f.hom.ker.toRepresentation

def integralKernelInclusion (f : A ⟶ B) : integralKernelObject f ⟶ A :=
  Rep.ofHom ⟨f.hom.ker.toSubmodule.subtype, fun _ => rfl⟩

@[simp] theorem integralKernelInclusion_apply (f : A ⟶ B) (a : integralKernelObject f) :
    (integralKernelInclusion f).hom a = a.val := rfl

instance integralKernelInclusion_mono (f : A ⟶ B) : Mono (integralKernelInclusion f) :=
  (Rep.mono_iff_injective _).mpr Subtype.val_injective

@[simp] theorem integralKernelInclusion_comp (f : A ⟶ B) :
    integralKernelInclusion f ≫ f = 0 := by
  ext a
  exact a.property

def integralKernelLift (f : A ⟶ B) (g : C ⟶ A) (hg : g ≫ f = 0) :
    C ⟶ integralKernelObject f :=
  Rep.ofHom ⟨g.hom.toLinearMap.codRestrict f.hom.ker.toSubmodule (fun a => by
    exact congrArg (fun q => q.hom a) hg), fun s => by
      ext a
      exact Rep.hom_comm_apply g s a⟩

@[simp] theorem integralKernelLift_comp (f : A ⟶ B) (g : C ⟶ A) (hg : g ≫ f = 0) :
    integralKernelLift f g hg ≫ integralKernelInclusion f = g := by
  ext
  rfl

def integralKernelIsLimit (f : A ⟶ B) :
    IsLimit (KernelFork.ofι (integralKernelInclusion f) (integralKernelInclusion_comp f)) :=
  KernelFork.IsLimit.ofι' _ _ (fun g hg =>
    ⟨integralKernelLift f g hg, integralKernelLift_comp f g hg⟩)

def integralKernelIso (f : A ⟶ B) : integralKernelObject f ≅ kernel f :=
  (limit.isoLimitCone ⟨_, integralKernelIsLimit f⟩).symm

def integralKernelModuleEquiv (f : A ⟶ B) :
    (integralKernelObject f).ρ.asModule ≃ₗ[ℤ[G]] LinearMap.ker (integralRepresentationMap f) :=
  LinearEquiv.ofBijective
    ((integralRepresentationMap (integralKernelInclusion f)).codRestrict _ (fun a => a.property))
    ⟨fun _a _b h => Subtype.ext (congrArg Subtype.val h), fun a => ⟨⟨a.val, a.property⟩, rfl⟩⟩

theorem integralKernel_finite (f : A ⟶ B)
    (h : (LinearMap.ker (integralRepresentationMap f)).FG) :
    IntegralRepresentationFinite G (kernel f) := by
  have : Module.Finite ℤ[G] (LinearMap.ker (integralRepresentationMap f)) := Module.Finite.of_fg h
  have hf : IntegralRepresentationFinite G (integralKernelObject f) :=
    Module.Finite.equiv (integralKernelModuleEquiv f).symm
  exact hf.of_iso (integralKernelIso f)

end PolycyclicRecognition

end

end OAI
