import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPowerSeriesSubstitution
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.Nilpotent.Exp

namespace OAI

/-! # Finite exponential and logarithm identities

Formal power-series identities evaluate in an associative rational algebra
at a nilpotent element. All expressions are finite polynomials.
-/

noncomputable section
namespace PolycyclicRecognition

variable {A : Type*} [Ring A] [Algebra ℚ A]

def finiteNilpotentLog (n : ℕ) (a : A) : A :=
  Polynomial.aeval a (PowerSeries.trunc n (PowerSeries.log ℚ))

theorem nilpotentPowerSeriesEval_exp (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    nilpotentPowerSeriesEval a n ha (PowerSeries.exp ℚ) = IsNilpotent.exp a := by
  change Polynomial.aeval a (PowerSeries.trunc (n + 1) (PowerSeries.exp ℚ)) = _
  rw [Polynomial.aeval_def, PowerSeries.eval₂_trunc_eq_sum_range, IsNilpotent.exp_eq_sum ha]
  apply Finset.sum_congr rfl
  intro k _
  rw [PowerSeries.coeff_exp]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, one_div, Algebra.smul_def]

theorem finiteNilpotentLog_pow (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    finiteNilpotentLog (n + 1) a ^ (n + 1) = 0 :=
  nilpotentPowerSeriesEval_nilpotent a n ha (PowerSeries.log ℚ) PowerSeries.constantCoeff_log

theorem finiteNilpotentLog_exp (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    finiteNilpotentLog (n + 1) (IsNilpotent.exp a - 1) = a := by
  have hg : (PowerSeries.exp ℚ - 1).constantCoeff = 0 := by simp
  have h := nilpotentPowerSeriesEval_subst a n ha
    (PowerSeries.log ℚ) (PowerSeries.exp ℚ - 1) hg
  rw [PowerSeries.subst_log_exp_sub_one, nilpotentPowerSeriesEval_X, map_sub,
    nilpotentPowerSeriesEval_exp, map_one] at h
  exact h.symm

theorem exp_finiteNilpotentLog (a : A) (n : ℕ) (ha : a ^ (n + 1) = 0) :
    IsNilpotent.exp (finiteNilpotentLog (n + 1) a) = 1 + a := by
  have h := nilpotentPowerSeriesEval_subst a n ha
    (PowerSeries.exp ℚ) (PowerSeries.log ℚ) PowerSeries.constantCoeff_log
  rw [PowerSeries.subst_exp_log, map_add, map_one, nilpotentPowerSeriesEval_X] at h
  have hb := finiteNilpotentLog_pow a n ha
  have he := nilpotentPowerSeriesEval_exp (finiteNilpotentLog (n + 1) a) n hb
  change Polynomial.aeval (finiteNilpotentLog (n + 1) a)
    (PowerSeries.trunc (n + 1) (PowerSeries.exp ℚ)) = _ at he
  change 1 + a = Polynomial.aeval (finiteNilpotentLog (n + 1) a)
    (PowerSeries.trunc (n + 1) (PowerSeries.exp ℚ)) at h
  exact (h.trans he).symm

end PolycyclicRecognition

end

end OAI
