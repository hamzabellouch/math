import OAI.AlgebraicGeometry.AbhyankarSathaye.Identities

namespace OAI

/-!
A relative Bézout identity over an arbitrary commutative ring.
The inverse of `c` is specified by the equation `c * d = 1`.
-/
namespace AbhyankarSathaye.CommutingDerivations

variable {K : Type*} [CommRing K]

def parameterA (c x s : K) : K := c + 2*s^2*x + 4*s^5

def parameterB (c x y s : K) : K :=
  (3*s^3 - 3*s*y)*(c + 2*s^2*x) - 4*s^4*y^2

theorem parameter_bezout_certificate (h c s x y : K) :
    parameterA c x s*h + parameterB c x y s*y - c^2 =
      (c + 2*s^2*x)*(h - c - P x y s) -
        4*s^4*(x^2 + y^3 - s*h) := by
  unfold parameterA parameterB P
  ring

theorem parameter_bezout_unit (h c d s x y : K)
    (hcusp : x^2 + y^3 = s*h) (hsection : h = c + P x y s)
    (hunit : c*d = 1) :
    (d^2*parameterA c x s)*h + (d^2*parameterB c x y s)*y = 1 := by
  have hz : h - c - P x y s = 0 := by rw [hsection]; ring
  have hb : parameterA c x s*h + parameterB c x y s*y = c^2 := by
    apply sub_eq_zero.mp
    rw [parameter_bezout_certificate, hz, hcusp, sub_self]
    ring
  calc
    _ = d^2*(parameterA c x s*h + parameterB c x y s*y) := by ring
    _ = d^2*c^2 := by rw [hb]
    _ = (c*d)^2 := by ring
    _ = 1 := by rw [hunit]; ring

theorem parameter_shift (h c s x y : K)
    (hcusp : x^2 + y^3 = s*h) (hsection : h = c + P x y s) :
    (x + s^3)^2 + (y - s^2)^3 = c*s := by
  rw [shift_universal, hcusp, hsection]
  ring

theorem parameter_recover_s (h c d s x y : K)
    (hcusp : x^2 + y^3 = s*h) (hsection : h = c + P x y s)
    (hunit : c*d = 1) :
    d*((x + s^3)^2 + (y - s^2)^3) = s := by
  rw [parameter_shift h c s x y hcusp hsection]
  calc
    d*(c*s) = (c*d)*s := by ring
    _ = s := by rw [hunit, one_mul]

section Maps
variable {L H : Type*} [CommRing L] [FunLike H K L] [RingHomClass H K L]

@[simp] theorem map_parameterA (f : H) (c x s : K) :
    f (parameterA c x s) = parameterA (f c) (f x) (f s) := by
  simp [parameterA, map_ofNat]

@[simp] theorem map_parameterB (f : H) (c x y s : K) :
    f (parameterB c x y s) = parameterB (f c) (f x) (f y) (f s) := by
  simp [parameterB, map_ofNat]

end Maps
end AbhyankarSathaye.CommutingDerivations

end OAI
