import Mathlib.Algebra.Module.Submodule.Equiv
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionLength

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem map_scalar_kernel (e : M ≃ₗ[A] N) (x : A) :
    (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))).map e.toLinearMap =
      LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change x • e z = 0
    change x • z = 0 at hz
    rw [← map_smul, hz, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change x • e.symm y = 0
    change x • y = 0 at hy
    rw [← map_smul, hy, map_zero]

theorem map_scalar_range (e : M ≃ₗ[A] N) (x : A) :
    (LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))).map e.toLinearMap =
      LinearMap.range (x • (LinearMap.id : N →ₗ[A] N)) := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨e w, ?_⟩
    change x • e w = e (x • w)
    exact (map_smul e x w).symm
  · rintro ⟨z, rfl⟩
    refine ⟨x • e.symm z, ⟨e.symm z, rfl⟩, ?_⟩
    change e (x • e.symm z) = x • z
    rw [map_smul, e.apply_symm_apply]

noncomputable def scalarKernelEquiv (e : M ≃ₗ[A] N) (x : A) :
    LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M)) ≃ₗ[A]
      LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N)) :=
  e.ofSubmodules _ _ (map_scalar_kernel e x)

noncomputable def scalarCokernelEquiv (e : M ≃ₗ[A] N) (x : A) :
    (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) ≃ₗ[A]
      (N ⧸ LinearMap.range (x • (LinearMap.id : N →ₗ[A] N))) :=
  Submodule.Quotient.equiv _ _ e (map_scalar_range e x)

theorem scalar_kernel_length_eq (e : M ≃ₗ[A] N) (x : A) :
    Module.length A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) =
      Module.length A (LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N))) :=
  (scalarKernelEquiv e x).length_eq

theorem scalar_cokernel_length_eq (e : M ≃ₗ[A] N) (x : A) :
    Module.length A (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) =
      Module.length A (N ⧸ LinearMap.range (x • (LinearMap.id : N →ₗ[A] N))) :=
  (scalarCokernelEquiv e x).length_eq

theorem cyclic_factor_kernel_length (I : Ideal A) (f x : A) :
    Module.length A (LinearMap.ker (x • (LinearMap.id :
      (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) →ₗ[A]
      (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f}))))) =
    Module.length A (((I.colon {f}).colon {x}) ⧸
      (I.colon {f}).submoduleOf ((I.colon {f}).colon {x})) := by
  rw [scalar_kernel_length_eq (W22.cyclicFactorEquiv I f).symm x]
  exact kernel_length_eq_colon (I.colon {f}) x

theorem cyclic_factor_cokernel_length (I : Ideal A) (f x : A) :
    Module.length A
      ((↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) ⧸
        LinearMap.range (x • (LinearMap.id :
          (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) →ₗ[A]
          (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f}))))) =
      Module.length A (A ⧸ ((I.colon {f}) ⊔ Ideal.span {x})) := by
  rw [scalar_cokernel_length_eq (W22.cyclicFactorEquiv I f).symm x]
  exact cokernel_length_eq_cut (I.colon {f}) x

end PiExponentJets.W28.LocalIntersection

end OAI
