import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Module

namespace OAI

/-! # Norm geometry used in the projection theorem

A quadratic norm bound at the identity of a corner forces the real
first-order term to vanish.  This is the elementary norm argument in
Tomiyama's proof, separated from any operator-field representation.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : Type*} [CStarAlgebra B]

local instance tomiyamaOrder : PartialOrder B := CStarAlgebra.spectralOrder B
local instance tomiyamaStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

private theorem le_zero_of_inverse_bounds (a b : B)
    (h : ∀ n : ℕ, a ≤ (((n : ℝ) + 1)⁻¹) • b) : a ≤ 0 := by
  have ht : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹) • b) atTop (𝓝 (0 : B)) := by
    simpa only [one_div, zero_smul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const b)
  exact ge_of_tendsto ht (Eventually.of_forall h)

private theorem corner_real_term_nonpos (p x : B) (hp : IsStarProjection p)
    (hpx : p * x = x) (hxp : x * p = x) (C : ℝ)
    (h : ∀ t : ℝ, ‖p + t • x‖ ^ 2 ≤ 1 + C * t ^ 2) :
    x + star x ≤ 0 := by
  have hps : p * star x = star x := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hxp
  have hsp : star x * p = star x := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpx
  have hstep (t : ℝ) (ht : 0 < t) : x + star x ≤ t • (C • p) := by
    let z := p + t • x
    have hpz : p * z = z := by
      dsimp [z]
      rw [mul_add, mul_smul_comm, hp.isIdempotentElem.eq, hpx]
    have hzp : z * p = z := by
      dsimp [z]
      rw [add_mul, smul_mul_assoc, hp.isIdempotentElem.eq, hxp]
    have hpsz : p * star z = star z := by
      simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hzp
    have hb : star z * z ≤ (1 + C * t ^ 2) • (1 : B) := by
      calc
        star z * z ≤ algebraMap ℝ B (‖z‖ ^ 2) :=
          CStarAlgebra.star_mul_le_algebraMap_norm_sq z
        _ ≤ (1 + C * t ^ 2) • (1 : B) := by
          rw [Algebra.algebraMap_eq_smul_one]
          exact smul_le_smul_of_nonneg_right (h t) zero_le_one
    have hb' := hp.isSelfAdjoint.conjugate_le_conjugate hb
    have hleft : p * (star z * z) * p = star z * z := by
      rw [← mul_assoc p, hpsz, mul_assoc, hzp]
    have hright : p * ((1 + C * t ^ 2) • (1 : B)) * p =
        (1 + C * t ^ 2) • p := by
      rw [mul_smul_comm, mul_one, smul_mul_assoc, hp.isIdempotentElem.eq]
    rw [hleft, hright] at hb'
    have hexpand : star z * z =
        p + t • (x + star x) + t ^ 2 • (star x * x) := by
      simp only [z, star_add, star_smul, star_trivial, hp.isSelfAdjoint.star_eq,
        add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        hp.isIdempotentElem.eq, hpx, hsp]
      module
    rw [hexpand] at hb'
    have hquad : (0 : B) ≤ t ^ 2 • (star x * x) :=
      smul_nonneg (sq_nonneg t) (star_mul_self_nonneg x)
    have hle : p + t • (x + star x) ≤ (1 + C * t ^ 2) • p :=
      (le_add_of_nonneg_right hquad).trans hb'
    have hsplit : (1 + C * t ^ 2) • p = p + t • (t • (C • p)) := by
      module
    rw [hsplit] at hle
    exact (smul_le_smul_iff_of_pos_left ht).mp ((add_le_add_iff_left p).mp hle)
  apply le_zero_of_inverse_bounds (x + star x) (C • p)
  intro n
  exact hstep _ (inv_pos.mpr (by positivity))

/-- A quadratic norm bound at a projection makes a corner element
skew-adjoint. This also applies to the zero corner. -/
theorem corner_skewAdjoint_of_quadratic_bound (p x : B) (hp : IsStarProjection p)
    (hpx : p * x = x) (hxp : x * p = x) (C : ℝ)
    (h : ∀ t : ℝ, ‖p + t • x‖ ^ 2 ≤ 1 + C * t ^ 2) :
    star x = -x := by
  have hle := corner_real_term_nonpos p x hp hpx hxp C h
  have hneg := corner_real_term_nonpos p (-x) hp
    (by rw [mul_neg, hpx]) (by rw [neg_mul, hxp]) C (fun t => by
      simpa only [smul_neg, neg_smul, neg_sq] using h (-t))
  have hge : 0 ≤ x + star x := by
    simpa only [star_neg, ← neg_add, neg_nonpos] using hneg
  have he : x + star x = 0 := le_antisymm hle hge
  exact eq_neg_of_add_eq_zero_left (by rwa [add_comm])

/-- Applying the tangent argument to the imaginary multiple detects
self-adjointness using only the norm. -/
theorem isSelfAdjoint_of_quadratic_norm_bound (x : B) (C : ℝ)
    (h : ∀ t : ℝ, ‖1 + t • (Complex.I • x)‖ ^ 2 ≤ 1 + C * t ^ 2) :
    IsSelfAdjoint x := by
  have hs := corner_skewAdjoint_of_quadratic_bound 1 (Complex.I • x)
    (IsStarProjection.one B) (one_mul _) (mul_one _) C h
  have he : (-Complex.I) • star x = (-Complex.I) • x := by
    simpa only [star_smul, Complex.star_def, Complex.conj_I, neg_smul] using hs
  exact (smul_right_injective B (neg_ne_zero.mpr Complex.I_ne_zero)) he

end

end KadisonKastler

end OAI
