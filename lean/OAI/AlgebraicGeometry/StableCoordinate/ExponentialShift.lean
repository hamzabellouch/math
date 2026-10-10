import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic

namespace OAI

/-!
# Explicit polynomial exponential shift

This file proves the exponential substitution used in Section 2 of the source,
without presupposing any locally nilpotent derivation infrastructure.  The six
variables are ordered `p, s, u, F, J, w`.  All formulas work over any commutative
ring: no characteristic-zero or field hypothesis is required for this step.
-/

namespace StableCoordinate.ExponentialShift

open MvPolynomial

variable (k : Type*) [CommRing k]

abbrev P := MvPolynomial (Fin 6) k

noncomputable def p : P k := X 0
noncomputable def s : P k := X 1
noncomputable def u : P k := X 2
noncomputable def F : P k := X 3
noncomputable def J : P k := X 4
noncomputable def w : P k := X 5

noncomputable def x : P k := s k ^ 2 - u k ^ 2 + p k * F k
noncomputable def H : P k := x k ^ 2 * F k - (1 + 2 * s k * x k) * J k -
  p k * J k ^ 2 - u k

noncomputable def t (c : k) : P k := C c * w k
noncomputable def d (c : k) : P k := 2 * u k * t k c - p k * t k c ^ 2

noncomputable def substitution (c : k) : Fin 6 → P k :=
  ![p k,
    s k + p k * x k * d k c,
    u k - p k * t k c,
    F k - (2 * s k * x k + 1) * d k c - p k * x k ^ 2 * d k c ^ 2,
    J k - x k ^ 2 * d k c,
    w k]

noncomputable def shift (c : k) : P k →ₐ[k] P k :=
  aeval (substitution k c)

@[simp] theorem shift_p (c : k) : shift k c (p k) = p k := by
  simp [shift, p, substitution]
@[simp] theorem shift_s (c : k) : shift k c (s k) = s k + p k * x k * d k c := by
  simp [shift, s, substitution]
@[simp] theorem shift_u (c : k) : shift k c (u k) = u k - p k * t k c := by
  simp [shift, u, substitution]
@[simp] theorem shift_F (c : k) : shift k c (F k) =
    F k - (2 * s k * x k + 1) * d k c - p k * x k ^ 2 * d k c ^ 2 := by
  simp [shift, F, substitution]
@[simp] theorem shift_J (c : k) : shift k c (J k) = J k - x k ^ 2 * d k c := by
  simp [shift, J, substitution]
@[simp] theorem shift_w (c : k) : shift k c (w k) = w k := by
  simp [shift, w, substitution]
@[simp] theorem shift_t (c b : k) : shift k c (t k b) = t k b := by
  simp [t, shift, w, substitution]
@[simp] theorem t_neg (c : k) : t k (-c) = -t k c := by
  simp [t]

private theorem quadratic_invariant {A : Type*} [CommRing A]
    (p s u F t : A) :
    let x := s ^ 2 - u ^ 2 + p * F
    let d := 2 * u * t - p * t ^ 2
    (s + p * x * d) ^ 2 - (u - p * t) ^ 2 +
      p * (F - (2 * s * x + 1) * d - p * x ^ 2 * d ^ 2) = x := by
  dsimp
  ring

@[simp] theorem shift_x (c : k) : shift k c (x k) = x k := by
  simp only [x, map_add, map_sub, map_pow, map_mul, shift_s, shift_u, shift_p, shift_F]
  exact quadratic_invariant (p k) (s k) (u k) (F k) (t k c)

@[simp] theorem shift_d_neg (c : k) : shift k c (d k (-c)) = -d k c := by
  simp only [d, map_sub, map_mul, map_ofNat, map_pow, shift_u, shift_t, shift_p, t_neg, map_neg]
  ring

private theorem inverse_F {A : Type*} [CommRing A] (p s F x d : A) :
    (F - (2 * s * x + 1) * d - p * x ^ 2 * d ^ 2) -
      (2 * (s + p * x * d) * x + 1) * -d - p * x ^ 2 * (-d) ^ 2 = F := by
  ring

@[simp] theorem shift_comp_neg (c : k) :
    (shift k c).comp (shift k (-c)) = AlgHom.id k (P k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change shift k c (shift k (-c) (p k)) = p k
    simp
  · change shift k c (shift k (-c) (s k)) = s k
    simp only [shift_s, map_add, map_mul, shift_p, shift_x, shift_d_neg]
    ring
  · change shift k c (shift k (-c) (u k)) = u k
    simp only [shift_u, map_sub, map_mul, shift_p, shift_t, t_neg, map_neg]
    ring
  · change shift k c (shift k (-c) (F k)) = F k
    simp only [shift_F, map_sub, map_add, map_mul, map_ofNat, map_one, map_pow,
      shift_s, shift_x, shift_d_neg, shift_p]
    exact inverse_F (p k) (s k) (F k) (x k) (d k c)
  · change shift k c (shift k (-c) (J k)) = J k
    simp only [shift_J, map_sub, map_mul, map_pow, shift_x, shift_d_neg]
    ring
  · change shift k c (shift k (-c) (w k)) = w k
    simp

/-- The explicit exponential substitution, with inverse obtained by negating its parameter. -/
noncomputable def shiftEquiv (c : k) : P k ≃ₐ[k] P k :=
  AlgEquiv.ofAlgHom (shift k c) (shift k (-c)) (shift_comp_neg k c)
    (by simpa only [neg_neg] using shift_comp_neg k (-c))

@[simp] theorem shiftEquiv_apply (c : k) (a : P k) :
    shiftEquiv k c a = shift k c a := rfl

private theorem equation_shift {A : Type*} [CommRing A]
    (p s u F J x t d : A) :
    x ^ 2 * (F - (2 * s * x + 1) * d - p * x ^ 2 * d ^ 2) -
      (1 + 2 * (s + p * x * d) * x) * (J - x ^ 2 * d) -
      p * (J - x ^ 2 * d) ^ 2 - (u - p * t) =
      (x ^ 2 * F - (1 + 2 * s * x) * J - p * J ^ 2 - u) + p * t := by
  ring

/-- The crucial equation transport: the automorphism adds `p * c * w` to `H`. -/
theorem shift_H (c : k) : shift k c (H k) = H k + p k * t k c := by
  simp only [H, map_sub, map_mul, map_add, map_pow, map_one, map_ofNat,
    shift_x, shift_F, shift_s, shift_J, shift_p, shift_u]
  exact equation_shift (p k) (s k) (u k) (F k) (J k) (x k) (t k c) (d k c)

/-- Section 2's `exp(w Δ)` is an actual algebra automorphism fixing `p` and
sending `H` to `H + p*w`. -/
theorem exponential_shift_exists :
    ∃ e : P k ≃ₐ[k] P k, e (p k) = p k ∧ e (H k) = H k + p k * w k := by
  refine ⟨shiftEquiv k 1, ?_, ?_⟩
  · simp
  · simpa [t] using shift_H k 1

end StableCoordinate.ExponentialShift

end OAI
