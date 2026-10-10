import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTwistCocycle
import OAI.Algebra.AuslanderReiten.HomComplex.HomCochainScalar

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
include he

omit [IsScalarTower k R M] in
theorem inverse_transport_smul (a : R) (m : M) :
    e.symm (h a • m) = a • e.symm m := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

def transportedHom (n : ℕ) (f : moduleObject k R M n →ₗ[R] M) :
    moduleObject k R M n →ₗ[R] M where
  toFun x := e.symm (f (transport k R M h e n x))
  map_add' x y := by
    exact (congrArg (fun v : object k R M n => e.symm (f v))
      ((transport k R M h e n).map_add x y)).trans
        ((congrArg e.symm (f.map_add _ _)).trans (e.symm.map_add _ _))
  map_smul' a x := by
    exact (congrArg (fun v : object k R M n => e.symm (f v))
      (transport_left k R M h e he n a x)).trans
        ((congrArg e.symm (f.map_smul (h a)
          (show moduleObject k R M n from transport k R M h e n x))).trans
            (inverse_transport_smul k R M h e he a _))

def transportHom (n : ℕ) : (moduleObject k R M n →ₗ[R] M) →ₗ[k]
    (moduleObject k R M n →ₗ[R] M) where
  toFun := transportedHom k R M h e he n
  map_add' f g := by ext x; exact e.symm.map_add _ _
  map_smul' a f := by ext x; exact e.symm.map_smul a _

@[simp] theorem transportHom_apply (n : ℕ) (f : moduleObject k R M n →ₗ[R] M)
    (x : moduleObject k R M n) :
    transportHom k R M h e he n f x = e.symm (f (transport k R M h e n x)) := rfl

theorem transportHom_differential (n : ℕ) (f : moduleObject k R M n →ₗ[R] M) :
    transportHom k R M h e he (n+1) (f.comp (differential k R M n)) =
      (transportHom k R M h e he n f).comp (differential k R M n) := by
  ext x
  change e.symm (f (boundary k R M n (transport k R M h e (n+1) x))) =
    e.symm (f (transport k R M h e n (boundary k R M n x)))
  exact congrArg (fun v : object k R M n => e.symm (f v))
    (transport_boundary k R M h e he n x).symm

variable [CharP k 2]

def homTransport : ExternalTensor.homCochain k R (complex k R M) M ⟶
    ExternalTensor.homCochain k R (complex k R M) M where
  f n := ModuleCat.ofHom (transportHom k R M h e he (n+1))
  comm' i j hij := by
    have hj : i+1=j := hij
    subst j
    rw [ExternalTensor.homCochain_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (transportHom_differential k R M h e he (i+1) f).symm

def canonicalHomTransport :
    ExternalTensor.canonicalHomCochain k R (complex k R M) (ModuleCat.of R M) ⟶
      ExternalTensor.canonicalHomCochain k R (complex k R M) (ModuleCat.of R M) :=
  (ExternalTensor.homCochainScalarIso k R (complex k R M) M).inv ≫
    homTransport k R M h e he ≫
      (ExternalTensor.homCochainScalarIso k R (complex k R M) M).hom

end ArExplicit.ModuleBar

end

end OAI
