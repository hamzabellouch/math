import OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame

namespace OAI

noncomputable section
namespace PiExponent

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity

theorem residue_polynomialFrame_eq_frameBasis_dot {E : Type*} [Field E]
    (m : ℕ) (phi : FramePolynomial m →+* E)
    (hy : phi (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
    (j : Fin (m + 1)) (p : FramePolynomial m) :
    phi (polynomialFrame m j p) =
      ∑ i, frameBasis m (phi (MvPolynomial.X 0)) hy j i *
        phi (MvPolynomial.pderiv i p) := by
  refine Fin.cases ?_ (fun l => ?_) j
  · rw [polynomialFrame_zero, logarithmicDerivation_apply, map_add, map_mul,
      map_sum, Fin.sum_univ_succ]
    simp only [frameBasis_zero_zero, frameBasis_zero_succ, one_mul]
  · rw [polynomialFrame_pos m l.succ (Fin.succ_ne_zero l), frameBasis_succ]
    simp [Pi.basisFun_apply, Pi.single_apply]

end PiExponent
end

end OAI
