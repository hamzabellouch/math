import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Polynomial identities for the cusp and the explicit hypersurface

The polynomials `S` and `P` give the identity
`(x + s³)² + (y - s²)³ = s * (1 + F)`. The Bézout certificate is valid over
every commutative ring. In the ambient complex polynomial ring, the variables
are ordered as `h, u, v, w`.
-/

noncomputable section
namespace AbhyankarSathaye

def S {B : Type*} [CommRing B] (h u v w : B) : B :=
  2*u^3*v + 3*u^4*w + h*(v^2 - 3*u^2*w^2) + h^2*w^3

def P {B : Type*} [CommRing B] (x y s : B) : B :=
  -2*s^2*x + 3*s*y^2 - 3*s^3*y

def Alpha {B : Type*} [CommRing B] (x s : B) : B :=
  1 + 2*s^2*x + 4*s^5

def Beta {B : Type*} [CommRing B] (x y s : B) : B :=
  (3*s^3 - 3*s*y)*(1 + 2*s^2*x) - 4*s^4*y^2

theorem cusp_universal {B : Type*} [CommRing B] (h u v w : B) :
    (u^3 + h*v)^2 + (-u^2 + h*w)^3 = h*S h u v w := by
  unfold S
  ring

theorem shift_universal {B : Type*} [CommRing B] (x y s : B) :
    (x + s^3)^2 + (y - s^2)^3 = x^2 + y^3 - s*P x y s := by
  unfold P
  ring

theorem bezout_certificate {B : Type*} [CommRing B] (h x y s : B) :
    Alpha x s*h + Beta x y s*y - 1 =
      (1 + 2*s^2*x)*(h - 1 - P x y s) - 4*s^4*(x^2 + y^3 - s*h) := by
  unfold Alpha Beta P
  ring

abbrev R := MvPolynomial (Fin 4) ℂ

def h : R := MvPolynomial.X 0
def u : R := MvPolynomial.X 1
def v : R := MvPolynomial.X 2
def w : R := MvPolynomial.X 3
def x : R := u^3 + h*v
def y : R := -u^2 + h*w
def s : R := S h u v w
def p : R := P x y s
def F : R := h - p - 1
def shiftX : R := x + s^3
def shiftY : R := y - s^2

theorem cusp : x^2 + y^3 = h*s := cusp_universal h u v w

theorem shift : shiftX^2 + shiftY^3 = x^2 + y^3 - s*p :=
  shift_universal x y s

theorem ambient : shiftX^2 + shiftY^3 = s*(1 + F) := by
  rw [shift, cusp]
  unfold F
  ring

end AbhyankarSathaye

end

end OAI
