import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

/-!
# Transporting hypersurface coordinate rings

The polynomial-presentation, stabilization, and fiber arguments use algebra
equivalences of ambient rings.  This file records the induced equivalences of
principal quotients, including their action on representatives.  In particular,
transporting a distinguished element transports *all* of its fibers, without
excluding the zero fiber.
-/

noncomputable section

namespace StableCoordinate

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

/-- An ambient algebra equivalence carrying one equation to another induces an
algebra equivalence of their hypersurface coordinate rings. -/
def principalQuotientEquiv (e : A ≃ₐ[k] B) (p : A) (q : B) (hpq : e p = q) :
    (A ⧸ Ideal.span {p}) ≃ₐ[k] (B ⧸ Ideal.span {q}) :=
  Ideal.quotientEquivAlg _ _ e (by
    simp only [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun b : B => Ideal.span {b}) hpq.symm)

@[simp]
theorem principalQuotientEquiv_mk (e : A ≃ₐ[k] B) (p : A) (q : B)
    (hpq : e p = q) (a : A) :
    principalQuotientEquiv e p q hpq (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (e a) := rfl

@[simp]
theorem principalQuotientEquiv_symm_mk (e : A ≃ₐ[k] B) (p : A) (q : B)
    (hpq : e p = q) (b : B) :
    (principalQuotientEquiv e p q hpq).symm (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (e.symm b) := rfl

/-- The equivalence induced on the fiber over an arbitrary scalar `c`.  No
nonzero hypothesis is needed: this is equally valid for the zero fiber. -/
def fiberQuotientEquiv (e : A ≃ₐ[k] B) (p : A) (q : B)
    (hpq : e p = q) (c : k) :
    (A ⧸ Ideal.span {p - algebraMap k A c}) ≃ₐ[k]
      (B ⧸ Ideal.span {q - algebraMap k B c}) :=
  principalQuotientEquiv e _ _ (by simp only [map_sub, hpq, e.commutes])

@[simp]
theorem fiberQuotientEquiv_mk (e : A ≃ₐ[k] B) (p : A) (q : B)
    (hpq : e p = q) (c : k) (a : A) :
    fiberQuotientEquiv e p q hpq c (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (e a) := rfl

@[simp]
theorem fiberQuotientEquiv_symm_mk (e : A ≃ₐ[k] B) (p : A) (q : B)
    (hpq : e p = q) (c : k) (b : B) :
    (fiberQuotientEquiv e p q hpq c).symm (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (e.symm b) := rfl

end StableCoordinate

end

end OAI
