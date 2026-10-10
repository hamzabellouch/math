import OAI.NumberTheory.TwoPoint.Bounds.ShiftMatrixWords

namespace OAI

/-! Signed expectation and comparison of the forced-word trace expansion. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {V E S Ω Ω' : Type*} [Fintype V] [DecidableEq V] [Fintype E]
  [Fintype Ω] [Fintype Ω']

noncomputable def shiftClosedWeight (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) (k : ℕ) (i : V) (u v : Fin k → E) : ℝ := by
  classical
  exact if shiftWordEnd next (embed i) u = shiftWordEnd next (embed i) v then
    shiftWordWeight embed next weight (embed i) u *
      shiftWordWeight embed next weight (embed i) v else 0

theorem average_shiftMatrix_moment (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : Ω → E → S → ℝ) (μ : FiniteLaw Ω) (k : ℕ) :
    μ.average (fun ω => matrixFrobeniusSq (shiftMatrix embed next (weight ω) ^ k)) =
      ∑ i, ∑ u : Fin k → E, ∑ v : Fin k → E,
        μ.average (fun ω => shiftClosedWeight embed next (weight ω) k i u v) := by
  simp only [shiftMatrix_moment_forced_words embed hinj, shiftClosedWeight,
    FiniteLaw.average, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]

/-- The signed expectations are compared before taking absolute values.
There is one initial-site factor, and no intermediate-site factor. -/
theorem shiftMatrix_moment_comparison (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : Ω → E → S → ℝ) (weight' : Ω' → E → S → ℝ)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (k : ℕ) (ε : ℝ)
    (hcompare : ∀ i u v,
      |μ.average (fun ω => shiftClosedWeight embed next (weight ω) k i u v) -
        ν.average (fun ω => shiftClosedWeight embed next (weight' ω) k i u v)| ≤ ε) :
    |μ.average (fun ω => matrixFrobeniusSq (shiftMatrix embed next (weight ω) ^ k)) -
      ν.average (fun ω => matrixFrobeniusSq (shiftMatrix embed next (weight' ω) ^ k))| ≤
      (Fintype.card V : ℝ) * (Fintype.card E : ℝ) ^ (2 * k) * ε := by
  classical
  rw [average_shiftMatrix_moment embed hinj, average_shiftMatrix_moment embed hinj,
    ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ i, ∑ u : Fin k → E, ∑ v : Fin k → E,
        |μ.average (fun ω => shiftClosedWeight embed next (weight ω) k i u v) -
          ν.average (fun ω => shiftClosedWeight embed next (weight' ω) k i u v)| := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro i _
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro u _
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : V, ∑ _u : Fin k → E, ∑ _v : Fin k → E, ε :=
      sum_le_sum (fun i _ => sum_le_sum (fun u _ => sum_le_sum (fun v _ => hcompare i u v)))
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow]
      rw [show 2 * k = k + k by omega, pow_add]
      ring

end TwoPointCorrelations

end OAI
