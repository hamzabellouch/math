import OAI.Algebra.AuslanderReiten.Complete.CompleteComparison
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

namespace ArExplicit

universe u

variable {R : Type u} [Ring R] [Module.Injective R R]
variable {K L M : Type u}
variable [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
variable [AddCommGroup M] [Module R M]

theorem homExactAt_of_injective (e : K →ₗ[R] L) (d : L →ₗ[R] M)
    (hex : LinearMap.range e = LinearMap.ker d) : HomExactAt e d := by
  intro f hf
  have hk : LinearMap.ker d ≤ LinearMap.ker f := by
    rw [← hex]
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun hf x
  let u : LinearMap.range d →ₗ[R] R :=
    ((LinearMap.ker d).liftQ f hk).comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R R (LinearMap.range d) M
    (LinearMap.range d).subtype Subtype.val_injective u
  refine ⟨g, ?_⟩
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun hg (d.rangeRestrict x)
  change g (d x) = f x
  calc
    g (d x) = u (d.rangeRestrict x) := h
    _ = f x := by
      exact congrArg ((LinearMap.ker d).liftQ f hk)
        (d.quotKerEquivRange_symm_apply_image x (LinearMap.mem_range_self d x))

theorem ExactProjectiveComplex.totallyAcyclic
    {P : ChainComplex (ModuleCat.{u} R) ℤ} (hP : ExactProjectiveComplex P) :
    TotallyAcyclicComplex P where
  toExactProjectiveComplex := hP
  dualExact n := homExactAt_of_injective _ _ (hP.exactAt n)

end ArExplicit

end OAI
