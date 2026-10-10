import OAI.NumberTheory.CubicMoment.Estimates.PrimeChebyshevDeweight
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! A finite-lattice bound covers the bounded initial interval in the
explicit angular prime theorem. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primeChebyshev_trivial (ψ : Eisenstein → ℂ)
    (hψ : ∀ p, primaryPrime p → ‖ψ p‖ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    ‖primeChebyshev ψ X‖ ≤ 18*X*Real.log X := by
  have hsub : primeCutoff X ⊆ nonzeroNormBall X := by
    intro p hp
    exact mem_nonzeroNormBall.mpr ⟨(mem_primeCutoff.mp hp).2,(mem_primeCutoff.mp hp).1.2.ne_zero⟩
  have hcard := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (nonzeroNormBall_card_le (by linarith : 0 ≤ X))
  rw [primeChebyshev,primeCutoffSum_eq_sum]
  calc
    _ ≤ ∑ p ∈ primeCutoff X, ‖ψ p*(Real.log (norm p):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ primeCutoff X, Real.log X := by
      apply Finset.sum_le_sum
      intro p hp
      have hpp := (mem_primeCutoff.mp hp).1
      have hpn : 1 ≤ norm p := one_le_norm hpp.2.ne_zero
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hpn)]
      exact (mul_le_of_le_one_left (Real.log_nonneg hpn) (hψ p hpp)).trans
        (Real.log_le_log (by linarith) (mem_primeCutoff.mp hp).2)
    _ = ((primeCutoff X).card:ℝ)*Real.log X := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hX)

lemma primeChebyshev_bounded_range (ψ : Eisenstein → ℂ)
    (hψ : ∀ p, primaryPrime p → ‖ψ p‖ ≤ 1) {X Y : ℝ} (hX : 3 ≤ X) (hXY : X ≤ Y) :
    ‖primeChebyshev ψ X‖ ≤ 18*Y*(Real.sqrt X*(Real.log X)^2) := by
  have hXp : 0 < X := by linarith
  have hL : 1 ≤ Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans hX)
    simpa only [Real.log_exp] using hh
  have hsqrt : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hXp.le).mpr (by linarith)
  have hlog : Real.log X ≤ Real.sqrt X*(Real.log X)^2 := by
    calc
      _ ≤ (Real.log X)^2 := by nlinarith
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) hsqrt
  calc
    _ ≤ 18*X*Real.log X := primeChebyshev_trivial ψ hψ (by linarith)
    _ ≤ 18*Y*Real.log X := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by nlinarith)

end CubicFirstMoment

end

end OAI
