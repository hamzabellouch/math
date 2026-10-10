import OAI.AlgebraicGeometry.StableCoordinate.NonzeroFiber
import OAI.AlgebraicGeometry.StableCoordinate.IteratedQuotient
import OAI.AlgebraicGeometry.StableCoordinate.QuotientTransport

namespace OAI

/-!
# Transport of the proved nonzero-fiber calculation

This module connects the simultaneous-equation calculation in `NonzeroFiber`
to the manuscript's successive quotient `A/(p-l)`, then transports it through
any proved polynomial-presentation equivalence. The eventual exact-polynomial
endpoint supplies the presentation equivalence; these generic transport lemmas
are not substituted for that endpoint.
-/

noncomputable section

namespace StableCoordinate.NonzeroFiber

open MvPolynomial

variable {K : Type*} [Field K]

/-- The manuscript's five-generator single-relation presentation. -/
abbrev Source (K : Type*) [Field K] := P5 K ⧸ Ideal.span {(H : P5 K)}

/-- The distinguished element `p` in the manuscript presentation. -/
def sourceP : Source K := Ideal.Quotient.mk _ (X 0)

/-- Every nonzero fiber of the manuscript presentation is a polynomial algebra. -/
def sourceFiberEquiv (l : K) (hl : l≠0) :
    (Source K ⧸ Ideal.span {sourceP - algebraMap K (Source K) l}) ≃ₐ[K] P3 K :=
  (IteratedQuotient.fiberEquiv K (P5 K) H (X 0) l).trans (nonzeroFiberEquiv l hl)

/-- Transfer the proved nonzero-fiber equivalence through a separately proved
presentation equivalence that carries `p` to a specified polynomial. -/
def transportedFiberEquiv {B : Type*} [CommRing B] [Algebra K B]
    (e : Source K ≃ₐ[K] B) (g : B) (hg : e sourceP=g) (l : K) (hl : l≠0) :
    (B ⧸ Ideal.span {g-algebraMap K B l}) ≃ₐ[K] P3 K :=
  (fiberQuotientEquiv e sourceP g hg l).symm.trans (sourceFiberEquiv l hl)

end StableCoordinate.NonzeroFiber

end

end OAI
