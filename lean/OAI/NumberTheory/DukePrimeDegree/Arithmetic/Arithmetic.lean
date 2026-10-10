import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace OAI

/-!
# Arithmetic estimates for prime-degree torus packets

The real-variable comparison controls the contribution of a nontrivial
zero after applying Stark (1974), Lemmas 3 and 8. The discriminant and
local-moment estimates relate the arithmetic counting scales.
-/

open Filter
open scoped Topology ENNReal

namespace DukePrimeDegree

/-- Uniform comparison of a zero's contribution to the logarithmic
 derivative, once its rescaled distance from 1 is bounded below.
 The constant is slightly larger than the manuscript's, which is harmless. -/
theorem zero_contribution_comparison
    {X Y U c : ℝ} (hX : 0 ≤ X) (hU : 0 < U) (hU4 : U ≤ 4)
    (hc : 0 < c) (hgap : c ^ 2 ≤ X ^ 2 + Y ^ 2) :
    (X + U) / ((X + U) ^ 2 + Y ^ 2) ≤
      (8 + 8 / c ^ 2) * ((X + 1) / ((X + 1) ^ 2 + Y ^ 2)) := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hd : 0 < (X + U) ^ 2 + Y ^ 2 := by positivity
  have he : 0 < (X + 1) ^ 2 + Y ^ 2 := by positivity
  have hsmall : X ^ 2 + Y ^ 2 ≤ (X + U) ^ 2 + Y ^ 2 := by nlinarith
  have hratio : (X + 1) ^ 2 + Y ^ 2 ≤
      (2 + 2 / c ^ 2) * ((X + U) ^ 2 + Y ^ 2) := by
    have hbound : c ^ 2 ≤ (X + U) ^ 2 + Y ^ 2 := hgap.trans hsmall
    have hdiv : 2 ≤ (2 / c ^ 2) * ((X + U) ^ 2 + Y ^ 2) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc2).mpr
      nlinarith
    have hpoly : (X + 1) ^ 2 + Y ^ 2 ≤
        2 * ((X + U) ^ 2 + Y ^ 2) + 2 := by nlinarith [sq_nonneg (X - 1), sq_nonneg Y]
    nlinarith
  have hnum : X + U ≤ 4 * (X + 1) := by linarith
  apply (div_le_iff₀ hd).mpr
  rw [mul_assoc, div_mul_eq_mul_div, ← mul_div_assoc, le_div_iff₀ he]
  have hprod := mul_le_mul hnum hratio (le_of_lt he) (by positivity : 0 ≤ 4 * (X + 1))
  convert hprod using 1; ring

/-- The packet discriminant bound suffices to transfer divergence
 from the multiplier-order discriminant to the counting scale. -/
theorem scale_tendsto_atTop {D Q : ℕ → ℝ} {k : ℕ}
    (hQ : ∀ i, 0 ≤ Q i) (hbound : ∀ i, D i ≤ Q i ^ k)
    (hD : Tendsto D atTop atTop) : Tendsto Q atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 hD) ((max b 0) ^ k + 1)] with i hi
  have hlt : max b 0 < Q i := by
    by_contra h
    have hp := pow_le_pow_left₀ (hQ i) (le_of_not_gt h) k
    linarith [hbound i]
  exact (le_max_left b 0).trans hlt.le

/-- Markov's estimate for arbitrary (possibly correlated) local shells.
 All sums are extended nonnegative sums, so no convergence hypothesis is
 needed. This is the tail extraction used in `lem:local-moment`. -/
theorem weighted_tail_le_moment {α : Type*} (mass size : α → ℝ≥0∞)
    (R : ℝ≥0∞) (s : ℝ) (hs : 0 ≤ s) (hR : R ≠ 0) (hRtop : R ≠ ∞) :
    (∑' i, if R < size i then mass i else 0) ≤
      (R ^ s)⁻¹ * ∑' i, mass i * size i ^ s := by
  have hpow : R ^ s ≠ 0 := by
    exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hR) hRtop).ne'
  calc
    (∑' i, if R < size i then mass i else 0)
      ≤ ∑' i, (R ^ s)⁻¹ * (mass i * size i ^ s) := by
        apply ENNReal.tsum_le_tsum
        intro i
        split_ifs with hi
        · calc
            mass i = (R ^ s)⁻¹ * (mass i * R ^ s) := by
              rw [mul_left_comm, ENNReal.inv_mul_cancel hpow]
              · simp
              · exact ENNReal.rpow_ne_top_of_nonneg hs hRtop
            _ ≤ _ := mul_le_mul_right
              (mul_le_mul_right (ENNReal.rpow_le_rpow hi.le hs) (mass i)) _
        · exact zero_le
    _ = _ := ENNReal.tsum_mul_left

/-- Absorb the harmless `q^(s/16)` loss in the moment bound into the
cutoff `Q^(1/8)`. This is the exponent calculation giving `Q^(-s/16)`
in the local-weight tail estimate, using only `q ≤ Q`. -/
theorem tail_exponent_absorption {q Q s : ℝ} (hq : 0 ≤ q) (hQ : 0 < Q)
    (hqQ : q ≤ Q) (hs : 0 ≤ s) :
    Q ^ (-s / 8) * q ^ (s / 16) ≤ Q ^ (-s / 16) := by
  calc
    Q ^ (-s / 8) * q ^ (s / 16) ≤ Q ^ (-s / 8) * Q ^ (s / 16) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq hqQ (by positivity))
        (Real.rpow_nonneg hQ.le _)
    _ = Q ^ (-s / 16) := by
      rw [← Real.rpow_add hQ]
      congr 1
      ring

end DukePrimeDegree

end OAI
