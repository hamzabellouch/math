import OAI.NumberTheory.Jacobsthal.Partitions.NestedCoordinates

namespace OAI

namespace Erdos970

section

namespace ErdosCriticalGeometry

variable (R : Type*) [CommSemiring R]

theorem nestedX_partial_zero (Q : MV R) :
    nestedX R (MvPolynomial.pderiv 0 Q) = (nestedX R Q).derivative := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [hP, Polynomial.derivative_mul]
        ring
      · simp [hP, Polynomial.derivative_mul]
        ring

theorem nestedY_partial_one (Q : MV R) :
    nestedY R (MvPolynomial.pderiv 1 Q) = (nestedY R Q).derivative := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [map_add, hP, hQ]
  | mul_X P i hP =>
      fin_cases i
      · simp [hP, Polynomial.derivative_mul]
        ring
      · simp [hP, Polynomial.derivative_mul]
        ring

end ErdosCriticalGeometry

end

end Erdos970

end OAI
