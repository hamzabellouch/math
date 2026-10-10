import OAI.Algebra.AuslanderReiten.Modules.SplitModules
import OAI.Algebra.AuslanderReiten.Modules.ModuleRestriction

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory

universe u

variable {R S : Type u} [Ring R] [Ring S] (j : R →+* S)
variable {M N : ModuleCat.{u} S} (f : M ⟶ N)

def kernelObject : ModuleCat.{u} S := ModuleCat.of S (LinearMap.ker f.hom)
def cokernelObject : ModuleCat.{u} S := ModuleCat.of S (N ⧸ LinearMap.range f.hom)

def restrictKernelEquiv :
    ((ModuleCat.restrictScalars j).obj (kernelObject f)) ≃ₗ[R]
      LinearMap.ker (((ModuleCat.restrictScalars j).map f).hom) where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictCokernelEquiv :
    ((ModuleCat.restrictScalars j).obj (cokernelObject f)) ≃ₗ[R]
      (((ModuleCat.restrictScalars j).obj N) ⧸ LinearMap.range (((ModuleCat.restrictScalars j).map f).hom)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernel_restrict_projective
    [Module.Projective R ((ModuleCat.restrictScalars j).obj M)]
    [Module.Projective R ((ModuleCat.restrictScalars j).obj N)]
    (hf : Function.Surjective f.hom) :
    Module.Projective R ((ModuleCat.restrictScalars j).obj (kernelObject f)) := by
  let := projective_kernel_of_surjective (((ModuleCat.restrictScalars j).map f).hom) hf
  exact Module.Projective.of_equiv (restrictKernelEquiv j f).symm

theorem kernel_restrict_finite
    [Module.Finite R ((ModuleCat.restrictScalars j).obj M)]
    [Module.Projective R ((ModuleCat.restrictScalars j).obj N)]
    (hf : Function.Surjective f.hom) :
    Module.Finite R ((ModuleCat.restrictScalars j).obj (kernelObject f)) := by
  let := finite_kernel_of_surjective (((ModuleCat.restrictScalars j).map f).hom) hf
  exact Module.Finite.equiv (restrictKernelEquiv j f).symm

theorem cokernel_restrict_projective
    [Module.Injective R ((ModuleCat.restrictScalars j).obj M)]
    [Module.Projective R ((ModuleCat.restrictScalars j).obj N)]
    (hf : Function.Injective f.hom) :
    Module.Projective R ((ModuleCat.restrictScalars j).obj (cokernelObject f)) := by
  let := projective_cokernel_of_injective (((ModuleCat.restrictScalars j).map f).hom) hf
  exact Module.Projective.of_equiv (restrictCokernelEquiv j f).symm

end ArExplicit

end

end OAI
