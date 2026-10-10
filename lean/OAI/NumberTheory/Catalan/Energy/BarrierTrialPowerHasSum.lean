import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.GetD
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneDescartesX0

namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem barrierFiniteCoeff_power_hasSum (cs : List ℤ) (x : ℝ) :
    HasSum (fun k : ℕ => barrierFiniteCoeff cs (k + 1) * x ^ k)
      ((barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x) := by
  have hs : HasSum
      (fun k : ℕ => ((cs.getD k 0 : ℝ) / 100000000) * x ^ k)
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) * x ^ k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  have hvalue : (barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) * x ^ k := by
    simp only [barrierFinitePowerDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, eval₂_X_pow, map_div₀, map_intCast, map_ofNat]
  rw [hvalue]
  simpa [barrierFiniteCoeff] using hs

private theorem barrierTailRow_power_hasSum (z r : ℂ) (hz : ‖z‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re * x ^ k)
      (r * z / barrierTailLinearDen z x).re := by
  have hratio : ‖(x : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |x| * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg z)
      _ < 1 := by simpa only [one_mul] using hz
  have hc : HasSum
      (fun k : ℕ => (r * z ^ (k + 1)) * ((x ^ k : ℝ) : ℂ))
      (r * z / barrierTailLinearDen z x) := by
    convert (hasSum_geometric_of_norm_lt_one hratio).mul_left (r * z) using 1
    · funext k
      simp only [Complex.ofReal_pow, mul_pow, pow_succ]
      ring
    · simp only [barrierTailLinearDen, div_eq_mul_inv]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    Complex.hasSum_re hc

private theorem barrierTail_power_hasSum (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ =>
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re * x ^ k)
      (tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re := by
  revert htail
  induction tail with
  | nil =>
      intro _
      simp
  | cons zr tail ih =>
      intro htail
      have hr := barrierTailRow_power_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul] using hr.add ht

theorem barrierTrial_power_hasSum (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => barrierTrial cs tail (k + 1) * x ^ k)
      ((barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x +
        (tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re) := by
  simpa [barrierTrial, add_mul] using
    (barrierFiniteCoeff_power_hasSum cs x).add (barrierTail_power_hasSum tail htail hx)

end InternalCatalan

end

end OAI
