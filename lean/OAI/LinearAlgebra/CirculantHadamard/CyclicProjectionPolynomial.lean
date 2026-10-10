import OAI.LinearAlgebra.CirculantHadamard.CyclicProjection
import OAI.LinearAlgebra.CirculantHadamard.CyclicPolynomial

namespace OAI

universe uR

/-! Polynomial evaluation commutes with the concrete cyclic quotient map. -/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [CommRing R] {m n : ℕ}

/-- The cyclic quotient also preserves the coefficient algebra structure. -/
def cyclicProjectionAlgHom (h : m ∣ n) : Elem R n →ₐ[R] Elem R m :=
  { cyclicProjection R h with
    commutes' := fun r => cyclicProjection_scalar h r }

@[simp] theorem cyclicProjectionAlgHom_apply (h : m ∣ n) (F : Elem R n) :
    cyclicProjectionAlgHom R h F = cyclicProjection R h F := rfl

/-- Polynomial evaluation at the generator commutes with the cyclic quotient. -/
theorem cyclicProjection_aeval (h : m ∣ n) (F : Polynomial R) :
    cyclicProjection R h (Polynomial.aeval (CyclicPolynomial.generator R n) F) =
      Polynomial.aeval (CyclicPolynomial.generator R m) F := by
  change cyclicProjectionAlgHom R h
    (Polynomial.aeval (CyclicPolynomial.generator R n) F) = _
  have hgen : cyclicProjectionAlgHom R h (CyclicPolynomial.generator R n) =
      CyclicPolynomial.generator R m := cyclicProjection_generator (R := R) h
  rw [← Polynomial.aeval_algHom_apply, hgen]

end CirculantHadamard

end

end OAI
