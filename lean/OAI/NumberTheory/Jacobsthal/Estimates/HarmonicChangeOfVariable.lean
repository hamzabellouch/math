import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import OAI.NumberTheory.Jacobsthal.Paths.FiniteHistorySupport

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.HarmonicChangeOfVariable

open Set MeasureTheory
open FinitePathGeometry

theorem exponent_hasDerivAt {r t : ℝ} (ht : 0 < t) :
    HasDerivAt (nextExponent r) (-r / (t + 1) ^ 2) t := by
  have h := (hasDerivAt_const t r).div ((hasDerivAt_id t).add_const 1) (by linarith : t + 1 ≠ 0)
  convert! h using 1
  simp only [id_eq, zero_mul, zero_sub, mul_one]

theorem inverse_exponent {r t : ℝ} (hr : 0 < r) (_ht : 0 < t) :
    r / nextExponent r t - 1 = t := by
  unfold nextExponent
  field_simp
  ring

theorem harmonic_jacobian {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    |deriv (nextExponent r) t| / nextExponent r t = 1 / (t + 1) := by
  rw [(exponent_hasDerivAt ht).deriv, abs_of_neg (div_neg_of_neg_of_pos (by linarith)
    (sq_pos_of_pos (by linarith)))]
  unfold nextExponent
  field_simp

theorem harmonic_substitution (H : ℝ → ℝ) {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in nextExponent r b..nextExponent r a, H (r / x - 1) / x) =
      ∫ t in a..b, H t / (t + 1) := by
  let G : ℝ → ℝ := fun x => H (r / x - 1) / x
  have hc : ContinuousOn (nextExponent r) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact (exponent_hasDerivAt (r := r) (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Ioo (min a b) (max a b),
      HasDerivAt (nextExponent r) (-r / (t + 1) ^ 2) t := by
    intro t ht
    rw [min_eq_left hab, max_eq_right hab] at ht
    exact exponent_hasDerivAt (by linarith [ht.1])
  have hn : ∀ t ∈ Ioo (min a b) (max a b), -r / (t + 1) ^ 2 ≤ 0 := by
    intro t _
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := G) hc hd hn
  have hl : (∫ t in a..b, (G ∘ nextExponent r) t * (-r / (t + 1) ^ 2)) =
      -(∫ t in a..b, H t / (t + 1)) := by
    calc
      _ = ∫ t in a..b, -(H t / (t + 1)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        simp only [Function.comp_apply, G, inverse_exponent hr ht0]
        unfold nextExponent
        field_simp
      _ = _ := intervalIntegral.integral_neg
  calc
    _ = -(∫ x in nextExponent r a..nextExponent r b, G x) :=
      intervalIntegral.integral_symm _ _
    _ = _ := by rw [← hsub, hl, neg_neg]

end NumberTheoryLean.HarmonicChangeOfVariable

end

end Erdos970

end OAI
