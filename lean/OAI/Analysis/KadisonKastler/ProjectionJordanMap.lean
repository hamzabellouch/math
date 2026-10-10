import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

namespace OAI

/-! # Projection preservation from unitary preservation

Two scalar phases on a projection determine both its adjoint and its
square. Thus a unital complex-linear map preserving unitaries preserves
projections and orthogonal projection products, without an analytic
expansion of the exponential.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Put one unit-modulus scalar on a projection and one on its complement. -/
def projectionPhaseUnitary (p : A) (hp : IsStarProjection p)
    (z : ℂ) (hz : star z * z = 1) : unitary A :=
  ⟨1 - p + z • p, by
    have hz' : z * star z = 1 := by rwa [mul_comm]
    constructor
    · simp only [star_add, star_sub, star_one, star_smul, hp.isSelfAdjoint.star_eq,
        add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
        hp.one_sub.isIdempotentElem.eq, hp.mul_one_sub_self,
        hp.one_sub_mul_self, hp.isIdempotentElem.eq, hz', smul_zero,
        one_smul, add_zero, zero_add, sub_add_cancel]
    · simp only [star_add, star_sub, star_one, star_smul, hp.isSelfAdjoint.star_eq,
        add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
        hp.one_sub.isIdempotentElem.eq, hp.mul_one_sub_self,
        hp.one_sub_mul_self, hp.isIdempotentElem.eq, hz, smul_zero,
        one_smul, add_zero, zero_add, sub_add_cancel]⟩

private theorem phase_square_expansion (x : B) (z : ℂ) :
    star (1 - x + z • x) * (1 - x + z • x) =
      1 + ((z - 1) • x + (star z - 1) • star x +
        ((star z - 1) * (z - 1)) • (star x * x)) := by
  simp only [star_add, star_sub, star_one, star_smul,
    add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  module

private theorem unitary_phase_equation
    (F : A →ₗ[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary A, F u ∈ unitary B)
    (p : A) (hp : IsStarProjection p) (z : ℂ) (hz : star z * z = 1) :
    (z - 1) • F p + (star z - 1) • star (F p) +
      ((star z - 1) * (z - 1)) • (star (F p) * F p) = 0 := by
  have hu := Unitary.star_mul_self_of_mem (hFu (projectionPhaseUnitary p hp z hz))
  change star (F (1 - p + z • p)) * F (1 - p + z • p) = 1 at hu
  rw [map_add, map_sub, map_smul, hF1, phase_square_expansion] at hu
  exact add_left_cancel (show (1 : B) + _ = 1 + 0 by simpa only [add_zero] using hu)

/-- A unital complex-linear unitary-preserving map preserves projections. -/
theorem map_isStarProjection_of_map_unitary
    (F : A →ₗ[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary A, F u ∈ unitary B)
    (p : A) (hp : IsStarProjection p) : IsStarProjection (F p) := by
  have hm := unitary_phase_equation F hF1 hFu p hp (-1) (by norm_num)
  have hi := unitary_phase_equation F hF1 hFu p hp Complex.I (by simp)
  have hm' : (-2 : ℂ) • F p + (-2 : ℂ) • star (F p) +
      (4 : ℂ) • (star (F p) * F p) = 0 := by
    have hminus : (-1 : ℂ) - 1 = -2 := by norm_num
    rw [star_neg, star_one, hminus] at hm
    have hfour : (-2 : ℂ) * (-2) = 4 := by norm_num
    rw [hfour] at hm
    exact hm
  have hIc : (star Complex.I - 1) * (Complex.I - 1) = (2 : ℂ) := by
    norm_num [Complex.star_def, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  have hi' : (Complex.I - 1) • F p + (-Complex.I - 1) • star (F p) +
      (2 : ℂ) • (star (F p) * F p) = 0 := by
    rw [hIc] at hi
    simpa only [show star Complex.I = -Complex.I by simp] using hi
  have hstar0 : Complex.I • (F p - star (F p)) = 0 := by
    calc
      _ = ((Complex.I - 1) • F p + (-Complex.I - 1) • star (F p) +
          (2 : ℂ) • (star (F p) * F p)) -
          (1 / 2 : ℂ) • ((-2 : ℂ) • F p + (-2 : ℂ) • star (F p) +
            (4 : ℂ) • (star (F p) * F p)) := by module
      _ = 0 := by rw [hi', hm']; simp
  have hstar : star (F p) = F p :=
    (sub_eq_zero.mp ((smul_eq_zero.mp hstar0).resolve_left Complex.I_ne_zero)).symm
  have hsq0 : (4 : ℂ) • (F p * F p - F p) = 0 := by
    rw [hstar] at hm'
    calc
      _ = (-2 : ℂ) • F p + (-2 : ℂ) • F p + (4 : ℂ) • (F p * F p) := by module
      _ = 0 := hm'
  exact ⟨sub_eq_zero.mp ((smul_eq_zero.mp hsq0).resolve_left (by norm_num)), hstar⟩

/-- Projection preservation also preserves orthogonality. -/
theorem map_projection_mul_eq_zero_of_map_unitary
    (F : A →ₗ[ℂ] B) (hF1 : F 1 = 1)
    (hFu : ∀ u : unitary A, F u ∈ unitary B)
    (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    F p * F q = 0 := by
  let : IsAddTorsionFree B := .of_isTorsionFree ℂ B
  have hFp := map_isStarProjection_of_map_unitary F hF1 hFu p hp
  have hFq := map_isStarProjection_of_map_unitary F hF1 hFu q hq
  have hsum := map_isStarProjection_of_map_unitary F hF1 hFu (p + q) (hp.add hq hpq)
  rw [map_add] at hsum
  have hprod : F p * (F p + F q) = F p := by
    apply (hFp.sub_iff_mul_eq_left hsum).mp
    simpa only [add_sub_cancel_left] using hFq
  rw [mul_add, hFp.isIdempotentElem.eq] at hprod
  exact add_left_cancel (show F p + F p * F q = F p + 0 by simpa only [add_zero] using hprod)

end

end KadisonKastler

end OAI
