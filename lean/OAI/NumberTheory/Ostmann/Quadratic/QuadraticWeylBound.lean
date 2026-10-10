import OAI.NumberTheory.Ostmann.QuadraticCenter.RationalPhaseGlobal
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDifferencing

namespace OAI

/-! # A concrete quadratic Weyl bound from one differencing step -/

namespace Ostmann

open scoped BigOperators

/-- The bound is uniform in the linear coefficient. It is derived from the
finite block-packing argument, with no external exponential-sum hypothesis. -/
theorem quadratic_weyl_bound (α β : ℝ) (a : ℤ) (r N : ℕ)
    (hr : 2 ≤ r) (hcop : a.natAbs.Coprime r)
    (happrox : |2 * α - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2) :
    ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2 ≤
      64 * ((N : ℝ) / r + 1) * ((N : ℝ) + r * (1 + Real.log r)) := by
  by_cases hN : N = 0
  · subst N
    have hl : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let w := fun h : ℕ => ‖∑ j ∈ Finset.range (N - h), realAdditivePhase (2 * α * h) ^ j‖
  have hs : (∑ h ∈ Finset.range N, w (h + 1)) ≤ ∑ h ∈ Finset.range (N + 1), w h := by
    rw [Finset.sum_range_succ']
    have hw0 : 0 ≤ w 0 := norm_nonneg _
    linarith
  have hd : ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2 ≤
      (N : ℝ) + 2 * ∑ h ∈ Finset.range N, w (h + 1) := by
    simpa only [w, Nat.cast_add, Nat.cast_one] using quadratic_differencing_bound α β N
  have hg := rational_phase_global_bound (2 * α) a r N (N + 1) (fun h => N - h)
    hr hcop happrox (fun h _ => Nat.sub_le _ _)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hlog : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  let A := (N : ℝ) / r + 1
  let B := (N : ℝ) + r * (1 + Real.log r)
  have hA : 1 ≤ A := by
    have hh : 0 ≤ (N : ℝ) / r := by positivity
    dsimp [A]
    linarith
  have hB : (N : ℝ) ≤ B := by
    have hh : 0 ≤ (r : ℝ) * (1 + Real.log r) := by positivity
    dsimp [B]
    linarith
  have hB0 : 0 ≤ B := (Nat.cast_nonneg N).trans hB
  have hcoef : 4 * ((N + 1 : ℕ) : ℝ) / r + 1 ≤ 8 * A := by
    have hh : ((N : ℝ) + 1) / r ≤ 2 * ((N : ℝ) / r) := by
      calc
        _ ≤ (2 * (N : ℝ)) / r := div_le_div_of_nonneg_right (by linarith) hrR.le
        _ = _ := by ring
    dsimp [A]
    push_cast
    rw [mul_div_assoc]
    nlinarith
  have hg' : (∑ h ∈ Finset.range (N + 1), w h) ≤ 16 * A * B := by
    apply hg.trans
    have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ 2 * B by positivity)
    simpa only [B] using hm.trans_eq (by ring)
  have hNB : (N : ℝ) ≤ A * B := by
    have hh := mul_le_mul_of_nonneg_right hA hB0
    nlinarith
  have hAB : 0 ≤ A * B := by positivity
  dsimp [A, B] at hg' hNB hAB ⊢
  nlinarith

end Ostmann

end OAI
