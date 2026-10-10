import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Nonzero fibers of the polynomial hypersurface presentation

Source: `sources/build/source/sections/02-construction.tex`, especially
`con:quadric-identity`, `con:localized-inverse`, and `prop:fibers`.

The variables of `P5 K` are ordered `p,s,u,F,J`. This file proves the
explicit algebra equivalence

`K[p,s,u,F,J] / (H, p-l) ≃ₐ[K] K[x,y,z]` for every nonzero `l : K`.

It uses actual quotient algebras and mutually inverse algebra homomorphisms,
not a pointwise bijection. The identities work over any commutative ring
with an inverse to `p`; the quotient construction is stated over any field.
The transport from the presentation to the exact four-variable polynomial
is supplied separately by the polynomial-presentation equivalence.
-/

noncomputable section

namespace StableCoordinate.NonzeroFiber

variable {K : Type*} [CommRing K]

def quadric (p s u F : K) : K := s^2 - u^2 + p*F

def relation (p s u F J : K) : K :=
  (quadric p s u F)^2 * F - (1+2*s*quadric p s u F)*J - p*J^2-u

def xCoord (p s u F : K) : K := quadric p s u F

def yCoord (p s u F : K) : K := s + quadric p s u F * (quadric p s u F + u^2)

def zCoord (p s u F J : K) : K := s * quadric p s u F + p*J

theorem quadric_identity (p s u F J : K) :
    xCoord p s u F * yCoord p s u F - zCoord p s u F J * (zCoord p s u F J + 1) =
      p * (relation p s u F J + u) := by
  unfold xCoord yCoord zCoord relation quadric
  ring

end StableCoordinate.NonzeroFiber

namespace StableCoordinate.NonzeroFiber

variable {K : Type*} [CommRing K]

def inverseU (t x y z : K) : K := t * (x*y - z*(z+1))
def inverseS (t x y z : K) : K := y-x*(x+(inverseU t x y z)^2)
def inverseF (t x y z : K) : K := t*(x-(inverseS t x y z)^2+(inverseU t x y z)^2)
def inverseJ (t x y z : K) : K := t*(z-inverseS t x y z*x)

theorem x_inverse (p t x y z : K) (hpt : p*t=1) :
    xCoord p (inverseS t x y z) (inverseU t x y z) (inverseF t x y z) = x := by
  unfold xCoord quadric inverseF
  rw [← mul_assoc, hpt, one_mul]
  ring

theorem y_inverse (p t x y z : K) (hpt : p*t=1) :
    yCoord p (inverseS t x y z) (inverseU t x y z) (inverseF t x y z) = y := by
  change inverseS t x y z + xCoord p (inverseS t x y z) (inverseU t x y z)
    (inverseF t x y z) * (xCoord p (inverseS t x y z) (inverseU t x y z)
    (inverseF t x y z) + inverseU t x y z ^ 2) = y
  rw [x_inverse p t x y z hpt]
  unfold inverseS
  ring

theorem z_inverse (p t x y z : K) (hpt : p*t=1) :
    zCoord p (inverseS t x y z) (inverseU t x y z) (inverseF t x y z)
      (inverseJ t x y z) = z := by
  change inverseS t x y z * xCoord p (inverseS t x y z) (inverseU t x y z)
    (inverseF t x y z) + p*inverseJ t x y z = z
  rw [x_inverse p t x y z hpt]
  unfold inverseJ
  rw [← mul_assoc, hpt, one_mul]
  ring

theorem inverseU_forward (p t s u F J : K) (hpt : p*t=1)
    (hH : relation p s u F J = 0) :
    inverseU t (xCoord p s u F) (yCoord p s u F) (zCoord p s u F J) = u := by
  unfold inverseU
  rw [quadric_identity, hH, zero_add, ← mul_assoc, mul_comm t p, hpt, one_mul]

theorem inverseS_forward (p t s u F J : K) (hpt : p*t=1)
    (hH : relation p s u F J = 0) :
    inverseS t (xCoord p s u F) (yCoord p s u F) (zCoord p s u F J) = s := by
  unfold inverseS
  rw [inverseU_forward p t s u F J hpt hH]
  unfold xCoord yCoord
  ring

theorem inverseF_forward (p t s u F J : K) (hpt : p*t=1)
    (hH : relation p s u F J = 0) :
    inverseF t (xCoord p s u F) (yCoord p s u F) (zCoord p s u F J) = F := by
  unfold inverseF
  rw [inverseU_forward p t s u F J hpt hH, inverseS_forward p t s u F J hpt hH]
  unfold xCoord quadric
  have ht : t*p=1 := by simpa [mul_comm] using hpt
  calc
    t * (s ^ 2 - u ^ 2 + p * F - s ^ 2 + u ^ 2) = (t*p)*F := by ring
    _ = F := by rw [ht, one_mul]

theorem inverseJ_forward (p t s u F J : K) (hpt : p*t=1)
    (hH : relation p s u F J = 0) :
    inverseJ t (xCoord p s u F) (yCoord p s u F) (zCoord p s u F J) = J := by
  unfold inverseJ
  rw [inverseS_forward p t s u F J hpt hH]
  unfold zCoord xCoord
  have ht : t*p=1 := by simpa [mul_comm] using hpt
  calc
    t * (s * quadric p s u F + p * J - s * quadric p s u F) = (t*p)*J := by ring
    _ = J := by rw [ht, one_mul]

end StableCoordinate.NonzeroFiber

namespace StableCoordinate.NonzeroFiber

variable {K : Type*} [CommRing K]

theorem relation_inverse (p t x y z : K) (hpt : p*t=1) :
    relation p (inverseS t x y z) (inverseU t x y z) (inverseF t x y z)
      (inverseJ t x y z) = 0 := by
  have hq := quadric_identity p (inverseS t x y z) (inverseU t x y z)
    (inverseF t x y z) (inverseJ t x y z)
  rw [x_inverse p t x y z hpt, y_inverse p t x y z hpt,
    z_inverse p t x y z hpt] at hq
  have hu : p*inverseU t x y z = x*y-z*(z+1) := by
    unfold inverseU
    rw [← mul_assoc, hpt, one_mul]
  have hz : p*relation p (inverseS t x y z) (inverseU t x y z)
      (inverseF t x y z) (inverseJ t x y z) = 0 := by
    calc
      _ = p*(relation p (inverseS t x y z) (inverseU t x y z)
        (inverseF t x y z) (inverseJ t x y z) + inverseU t x y z) -
        p*inverseU t x y z := by ring
      _ = 0 := by rw [← hq, hu, sub_self]
  calc
    _ = t*(p*relation p (inverseS t x y z) (inverseU t x y z)
      (inverseF t x y z) (inverseJ t x y z)) := by
        rw [← mul_assoc, mul_comm t p, hpt, one_mul]
    _ = 0 := by rw [hz, mul_zero]

end StableCoordinate.NonzeroFiber

namespace StableCoordinate.NonzeroFiber

open MvPolynomial

section Quotient
variable {K : Type*} [Field K]

abbrev P5 (K : Type*) [CommRing K] := MvPolynomial (Fin 5) K
abbrev P3 (K : Type*) [CommRing K] := MvPolynomial (Fin 3) K

def H : P5 K := relation (X 0) (X 1) (X 2) (X 3) (X 4)

def fiberIdeal (l : K) : Ideal (P5 K) := Ideal.span {H, X 0-C l}

abbrev Fiber (l : K) := P5 K ⧸ fiberIdeal l

def mk (l : K) : P5 K →ₐ[K] Fiber l := Ideal.Quotient.mkₐ K (fiberIdeal l)

def decode (l : K) : Fin 5 → P3 K :=
  ![C l,
    inverseS (C l⁻¹) (X 0) (X 1) (X 2),
    inverseU (C l⁻¹) (X 0) (X 1) (X 2),
    inverseF (C l⁻¹) (X 0) (X 1) (X 2),
    inverseJ (C l⁻¹) (X 0) (X 1) (X 2)]

def forward (l : K) : P5 K →ₐ[K] P3 K := MvPolynomial.aeval (decode l)

@[simp] theorem forward_X (l : K) (i : Fin 5) : forward l (X i) = decode l i :=
  MvPolynomial.aeval_X _ _

@[simp] theorem forward_C (l c : K) : forward l (C c) = C c :=
  MvPolynomial.aeval_C _ _

theorem constants_inv (l : K) (hl : l≠0) :
    (C l : P3 K)*C l⁻¹=1 := by rw [← map_mul, mul_inv_cancel₀ hl, map_one]

theorem forward_H (l : K) (hl : l≠0) : forward l H = 0 := by
  unfold H
  simp only [relation, quadric, map_sub, map_add, map_mul, map_pow, map_one,
    map_ofNat, forward_X]
  change relation (C l) (inverseS (C l⁻¹) (X 0) (X 1) (X 2))
    (inverseU (C l⁻¹) (X 0) (X 1) (X 2))
    (inverseF (C l⁻¹) (X 0) (X 1) (X 2))
    (inverseJ (C l⁻¹) (X 0) (X 1) (X 2)) = 0
  exact relation_inverse (C l : P3 K) (C l⁻¹) (X 0) (X 1) (X 2) (constants_inv l hl)

theorem forward_relation (l : K) : forward l (X 0-C l) = 0 := by
  simp [decode]

theorem forward_kills (l : K) (hl : l≠0) : ∀ a ∈ fiberIdeal l, forward l a=0 := by
  intro a ha
  rcases Ideal.mem_span_pair.mp ha with ⟨b,c,rfl⟩
  simp [forward_H l hl, forward_relation l]

def toPoly (l : K) (hl : l≠0) : Fiber l →ₐ[K] P3 K :=
  Ideal.Quotient.liftₐ (fiberIdeal l) (forward l) (forward_kills l hl)

@[simp] theorem toPoly_mk (l : K) (hl : l≠0) (a : P5 K) :
    toPoly l hl (mk l a)=forward l a := by
  rfl

def encode (l : K) : Fin 3 → Fiber l :=
  ![xCoord (mk l (X 0)) (mk l (X 1)) (mk l (X 2)) (mk l (X 3)),
    yCoord (mk l (X 0)) (mk l (X 1)) (mk l (X 2)) (mk l (X 3)),
    zCoord (mk l (X 0)) (mk l (X 1)) (mk l (X 2)) (mk l (X 3)) (mk l (X 4))]

def fromPoly (l : K) : P3 K →ₐ[K] Fiber l := MvPolynomial.aeval (encode l)

@[simp] theorem fromPoly_X (l : K) (i : Fin 3) : fromPoly l (X i)=encode l i :=
  MvPolynomial.aeval_X _ _

@[simp] theorem fromPoly_C (l c : K) : fromPoly l (C c)=algebraMap K (Fiber l) c :=
  MvPolynomial.aeval_C _ _

end Quotient
end StableCoordinate.NonzeroFiber

namespace StableCoordinate.NonzeroFiber

open MvPolynomial
variable {K : Type*} [Field K]

theorem mk_H (l : K) : mk l H = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

theorem mk_p (l : K) : mk l (X 0) = algebraMap K (Fiber l) l := by
  have hr : mk l (X 0-C l) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  simpa only [map_sub, AlgHom.commutes, algebraMap_eq] using sub_eq_zero.mp hr

theorem mk_relation (l : K) :
    relation (mk l (X 0)) (mk l (X 1)) (mk l (X 2)) (mk l (X 3)) (mk l (X 4))=0 := by
  simpa only [H, relation, quadric, map_sub, map_add, map_mul, map_pow, map_one,
    map_ofNat] using mk_H l

theorem mk_unit (l : K) (hl : l≠0) :
    mk l (X 0)*algebraMap K (Fiber l) l⁻¹=1 := by
  rw [mk_p, ← map_mul, mul_inv_cancel₀ hl, map_one]

theorem toPoly_fromPoly (l : K) (hl : l≠0) :
    (toPoly l hl).comp (fromPoly l) = AlgHom.id K (P3 K) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [encode, xCoord, quadric, decode] using
      (x_inverse (C l : P3 K) (C l⁻¹) (X 0) (X 1) (X 2) (constants_inv l hl))
  · simpa [encode, xCoord, yCoord, quadric, decode] using
      (y_inverse (C l : P3 K) (C l⁻¹) (X 0) (X 1) (X 2) (constants_inv l hl))
  · simpa [encode, xCoord, zCoord, quadric, decode] using
      (z_inverse (C l : P3 K) (C l⁻¹) (X 0) (X 1) (X 2) (constants_inv l hl))

end StableCoordinate.NonzeroFiber

namespace StableCoordinate.NonzeroFiber

open MvPolynomial
variable {K : Type*} [Field K]

theorem fromPoly_toPoly (l : K) (hl : l≠0) :
    (fromPoly l).comp (toPoly l hl) = AlgHom.id K (Fiber l) := by
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  change fromPoly l (toPoly l hl (mk l (X i))) = mk l (X i)
  rw [toPoly_mk, forward_X]
  fin_cases i
  · simpa [decode] using (mk_p l).symm
  · simpa [decode, encode, inverseS, inverseU] using
      (inverseS_forward (mk l (X 0)) (algebraMap K (Fiber l) l⁻¹)
        (mk l (X 1)) (mk l (X 2)) (mk l (X 3)) (mk l (X 4))
        (mk_unit l hl) (mk_relation l))
  · simpa [decode, encode, inverseU] using
      (inverseU_forward (mk l (X 0)) (algebraMap K (Fiber l) l⁻¹)
        (mk l (X 1)) (mk l (X 2)) (mk l (X 3)) (mk l (X 4))
        (mk_unit l hl) (mk_relation l))
  · simpa [decode, encode, inverseF, inverseS, inverseU] using
      (inverseF_forward (mk l (X 0)) (algebraMap K (Fiber l) l⁻¹)
        (mk l (X 1)) (mk l (X 2)) (mk l (X 3)) (mk l (X 4))
        (mk_unit l hl) (mk_relation l))
  · simpa [decode, encode, inverseJ, inverseS, inverseU] using
      (inverseJ_forward (mk l (X 0)) (algebraMap K (Fiber l) l⁻¹)
        (mk l (X 1)) (mk l (X 2)) (mk l (X 3)) (mk l (X 4))
        (mk_unit l hl) (mk_relation l))

/-- The explicit algebraic nonzero-fiber calculation, valid over any field. -/
def nonzeroFiberEquiv (l : K) (hl : l≠0) : Fiber l ≃ₐ[K] P3 K :=
  AlgEquiv.ofAlgHom (toPoly l hl) (fromPoly l) (toPoly_fromPoly l hl) (fromPoly_toPoly l hl)

end StableCoordinate.NonzeroFiber

end

end OAI
