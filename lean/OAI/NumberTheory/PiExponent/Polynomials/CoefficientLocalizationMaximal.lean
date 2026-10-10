import Mathlib.Algebra.Field.Equiv
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Ideal
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateTranscendenceLocalization

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

section MaximalKernel
variable {F A L : Type*} [Field F] [CommRing A] [Field L]
variable [Algebra F A] [Algebra F L] [Algebra.IsAlgebraic F L]

theorem algebraic_field_kernel_isMaximal (f : A →ₐ[F] L) :
    (RingHom.ker f.toRingHom).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Subalgebra.isField_of_algebraic f.range)
    (Ideal.quotientKerEquivRange f).toRingEquiv.toMulEquiv

end MaximalKernel

variable {R A L : Type*} [CommRing R] [CommRing A] [CommRing L]
variable (M : Submonoid R) [Algebra R A] [IsLocalization M A]

include M in

theorem extended_kernel_eq (f : R →+* L) (g : A →+* L)
    (h : g.comp (algebraMap R A) = f) :
    (RingHom.ker f).map (algebraMap R A) = RingHom.ker g := by
  have hk : (RingHom.ker g).comap (algebraMap R A) = RingHom.ker f := by
    ext x
    change g (algebraMap R A x) = 0 ↔ f x = 0
    have he := RingHom.congr_fun h x
    change g (algebraMap R A x) = f x at he
    rw [he]
  rw [← hk]
  exact IsLocalization.map_under M A (RingHom.ker g)

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
