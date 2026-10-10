import Mathlib.Data.List.GetD
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import OAI.NumberTheory.Catalan.Energy.BarrierChebyshevUSeries
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneDescartesX0

namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem barrierFiniteCoeff_U_hasSum (cs : List ℤ) (x : ℝ) :
    HasSum (fun k : ℕ => barrierFiniteCoeff cs (k + 1) *
      (Chebyshev.U ℝ (k : ℤ)).eval x)
      ((barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x) := by
  have hs : HasSum
      (fun k : ℕ => ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x)
      (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hlen : cs.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [List.getD_eq_default cs 0 hlen]
    norm_num
  have hvalue : (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
        (Chebyshev.U ℝ (k : ℤ)).eval x := by
    simp only [barrierFiniteUDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, map_div₀, map_intCast, map_ofNat]
    simp only [eval₂_eq_eval_map, Chebyshev.map_U]
  rw [hvalue]
  simpa [barrierFiniteCoeff] using hs

private theorem barrierTailRow_U_hasSum (z r : ℂ) (hz : ‖z‖ < 1)
    {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => (r * z ^ (k + 1)).re * (Chebyshev.U ℝ (k : ℤ)).eval x)
      (r * z / barrierTailQuadraticDen z x).re := by
  have hc : HasSum
      (fun k : ℕ => (r * z ^ (k + 1)) *
        (((Chebyshev.U ℝ (k : ℤ)).eval x : ℝ) : ℂ))
      (r * z / barrierTailQuadraticDen z x) := by
    convert (barrierChebyshevU_hasSum hx hz).mul_left (r * z) using 1
    · funext k
      rw [pow_succ]
      ring
    · simp only [barrierTailQuadraticDen, div_eq_mul_inv, one_mul]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
    Complex.hasSum_re hc

private theorem barrierTail_U_hasSum (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ =>
      (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ (k + 1))).sum.re *
        (Chebyshev.U ℝ (k : ℤ)).eval x)
      (tail.map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re := by
  revert htail
  induction tail with
  | nil =>
      intro _
      simp
  | cons zr tail ih =>
      intro htail
      have hr := barrierTailRow_U_hasSum zr.1 zr.2 (htail zr List.mem_cons_self) hx
      have ht := ih (fun w hw => htail w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, Complex.add_re, add_mul] using hr.add ht

theorem barrierTrial_U_hasSum (cs : List ℤ) (tail : List (ℂ × ℂ))
    (htail : ∀ zr ∈ tail, ‖zr.1‖ < 1) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun k : ℕ => barrierTrial cs tail (k + 1) *
      (Chebyshev.U ℝ (k : ℤ)).eval x)
      ((barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x +
        (tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) := by
  simpa [barrierTrial, add_mul] using
    (barrierFiniteCoeff_U_hasSum cs x).add (barrierTail_U_hasSum tail htail hx)

end InternalCatalan

end

end OAI
