import Mathlib.Analysis.Calculus.Deriv.Polynomial
import OAI.NumberTheory.Catalan.Energy.BarrierFinitePotentialRat
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneDescartesX0

namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

private theorem barrierFiniteT_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => a * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y /
        ((k + 1 : ℕ) : ℝ))
      (a * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hindex : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by simp
  have ht : HasDerivAt
      (fun y : ℝ => (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y)
      (((k + 1 : ℕ) : ℝ) * (Chebyshev.U ℝ (k : ℤ)).eval x) x := by
    simpa only [Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast,
      hindex, Int.cast_natCast, eval_natCast] using
      (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).hasDerivAt x
  apply ((ht.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]

private theorem barrierFiniteS_term_hasDerivAt (a : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => a * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
      (a * x ^ k) x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : HasDerivAt (fun y : ℝ => y ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (k + 1) x
  apply ((hp.const_mul a).div_const ((k + 1 : ℕ) : ℝ)).congr_deriv
  field_simp [hk]

theorem barrierTrialT_nil_hasDerivAt (cs : List ℤ) (x : ℝ) :
    HasDerivAt (barrierTrialT (barrierTrial cs []))
      ((barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x) x := by
  have hf : barrierTrialT (barrierTrial cs []) =
      (fun y : ℝ => ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) *
          (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval y / ((k + 1 : ℕ) : ℝ)) := by
    funext y
    exact barrierTrialT_nil_eq_sum cs y
  have hd : (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * (Chebyshev.U ℝ (k : ℤ)).eval x := by
    simp only [barrierFiniteUDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, map_div₀, map_intCast, map_ofNat]
    simp only [eval₂_eq_eval_map, Chebyshev.map_U]
  rw [hf, hd]
  exact HasDerivAt.fun_sum (fun k _ =>
    barrierFiniteT_term_hasDerivAt ((cs.getD k 0 : ℝ) / 100000000) k x)

theorem barrierTrialS_nil_hasDerivAt (cs : List ℤ) (x : ℝ) :
    HasDerivAt (barrierTrialS (barrierTrial cs []))
      ((barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x) x := by
  have hf : barrierTrialS (barrierTrial cs []) =
      (fun y : ℝ => ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
    funext y
    exact barrierTrialS_nil_eq_sum cs y
  have hd : (barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * x ^ k := by
    simp only [barrierFinitePowerDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, eval₂_X_pow, map_div₀, map_intCast, map_ofNat]
  rw [hf, hd]
  exact HasDerivAt.fun_sum (fun k _ =>
    barrierFiniteS_term_hasDerivAt ((cs.getD k 0 : ℝ) / 100000000) k x)

end InternalCatalan

end

end OAI
