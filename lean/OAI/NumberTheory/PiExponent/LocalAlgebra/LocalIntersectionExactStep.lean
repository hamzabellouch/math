import OAI.NumberTheory.PiExponent.Cohomology.EndomorphismEulerAdditivity
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionTransport

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

theorem scalar_euler_cross_add (x : A)
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hExact : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    Module.length A (M₂ ⧸ LinearMap.range (x • (LinearMap.id : M₂ →ₗ[A] M₂))) +
        Module.length A (LinearMap.ker (x • (LinearMap.id : M₁ →ₗ[A] M₁))) +
        Module.length A (LinearMap.ker (x • (LinearMap.id : M₃ →ₗ[A] M₃))) =
      Module.length A (LinearMap.ker (x • (LinearMap.id : M₂ →ₗ[A] M₂))) +
        Module.length A (M₁ ⧸ LinearMap.range (x • (LinearMap.id : M₁ →ₗ[A] M₁))) +
        Module.length A (M₃ ⧸ LinearMap.range (x • (LinearMap.id : M₃ →ₗ[A] M₃))) := by
  apply EndomorphismEuler.endomorphism_euler_cross_add
    (x • LinearMap.id) (x • LinearMap.id) (x • LinearMap.id) f g hExact
  · ext m
    exact map_smul f x m
  · ext m
    exact map_smul g x m
  · exact hf
  · exact hg

theorem cyclic_ideal_step_cross_add (I : Ideal A) (f x : A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) +
        Module.length A (((I.colon {f}).colon {x}) ⧸
          (I.colon {f}).submoduleOf ((I.colon {f}).colon {x})) +
        Module.length A (((I ⊔ Ideal.span {f}).colon {x}) ⧸
          (I ⊔ Ideal.span {f}).submoduleOf ((I ⊔ Ideal.span {f}).colon {x})) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) +
        Module.length A (A ⧸ ((I.colon {f}) ⊔ Ideal.span {x})) +
        Module.length A (A ⧸ ((I ⊔ Ideal.span {f}) ⊔ Ideal.span {x})) := by
  let J : Ideal A := I ⊔ Ideal.span {f}
  let T : Submodule A (A ⧸ I) := Submodule.map I.mkQ J
  let eT : (A ⧸ I.colon {f}) ≃ₗ[A] T :=
    (W22.cyclicFactorEquiv I f).trans (W22.subquotientEquivImage I J)
  let eQ : ((A ⧸ I) ⧸ T) ≃ₗ[A] (A ⧸ J) :=
    Submodule.quotientQuotientEquivQuotient I J le_sup_left
  have h := scalar_euler_cross_add x T.subtype T.mkQ
    (LinearMap.exact_subtype_mkQ T) (Submodule.subtype_injective T)
    (Submodule.mkQ_surjective T)
  rw [scalar_kernel_length_eq eT.symm x, scalar_kernel_length_eq eQ x,
    scalar_cokernel_length_eq eT.symm x, scalar_cokernel_length_eq eQ x] at h
  change Module.length A ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) +
      Module.length A (LinearMap.ker (quotientMul (I.colon {f}) x)) +
      Module.length A (LinearMap.ker (quotientMul J x)) =
    Module.length A (LinearMap.ker (quotientMul I x)) +
      Module.length A ((A ⧸ I.colon {f}) ⧸ LinearMap.range (quotientMul (I.colon {f}) x)) +
      Module.length A ((A ⧸ J) ⧸ LinearMap.range (quotientMul J x)) at h
  simpa only [cokernel_length_eq_cut, kernel_length_eq_colon, J] using h

end PiExponentJets.W28.LocalIntersection

end OAI
