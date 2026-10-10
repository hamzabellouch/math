import Mathlib

namespace OAI

namespace PolynomialVacuumInterpolation
open Classical

noncomputable def mergeVariable {ι : Type*} (i j : ι) :
    MvPolynomial ι ℂ →+* MvPolynomial ι ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun k => if k=i then MvPolynomial.X j else MvPolynomial.X k)

noncomputable def nodeFactor {ι : Type*} (i j : ι) : MvPolynomial ι ℂ :=
  MvPolynomial.X i - MvPolynomial.X j

end PolynomialVacuumInterpolation

end OAI
