import OAI.NumberTheory.JointDickman.Arithmetic.TotientProductTruncation
import OAI.NumberTheory.JointDickman.Amplification.SingularSeriesTail
import Mathlib.Data.Nat.Factorial.Basic

namespace OAI

/-! # A periodic finite-factor approximation to the lag singular series -/
namespace JointDickman
open Finset Classical

noncomputable def periodicSingularSeries (Y Q n : ℕ) : ℝ :=
  totientLocalProduct Y n * ∑ q ∈ range Q, singularSeriesCoefficient n q

theorem totientLocalProduct_modEq {Y m n : ℕ}
    (h : m ≡ n [MOD Y.factorial]) : totientLocalProduct Y m = totientLocalProduct Y n := by
  apply prod_congr rfl
  intro p hp
  have hpY := Nat.mem_primesLE.mp hp
  have hd := h.dvd_iff (Nat.dvd_factorial hpY.2.pos hpY.1)
  simp only [hd]

theorem singularSeriesCoefficient_modEq {Q m n : ℕ}
    (h : m ≡ n [MOD Q.factorial]) {q : ℕ} (hq : q < Q) :
    singularSeriesCoefficient m q = singularSeriesCoefficient n q := by
  by_cases hq0 : q = 0
  · simp [hq0,singularSeriesCoefficient]
  have hqP : q ∣ Q.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hq0) hq.le
  have hh := (h.of_dvd hqP).gcd_eq
  have hc : q.Coprime m ↔ q.Coprime n := by
    change Nat.gcd q m = 1 ↔ Nat.gcd q n = 1
    rw [Nat.gcd_comm q m,Nat.gcd_comm q n,hh]
  simp only [singularSeriesCoefficient,hc]

theorem periodicSingularSeries_modEq (Y Q : ℕ) {m n : ℕ}
    (h : m ≡ n [MOD (max Y Q).factorial]) :
    periodicSingularSeries Y Q m = periodicSingularSeries Y Q n := by
  have hY := h.of_dvd (Nat.factorial_dvd_factorial (le_max_left Y Q))
  have hQ := h.of_dvd (Nat.factorial_dvd_factorial (le_max_right Y Q))
  unfold periodicSingularSeries
  rw [totientLocalProduct_modEq hY]
  congr 1
  exact sum_congr rfl (fun q hq => singularSeriesCoefficient_modEq hQ (mem_range.mp hq))

theorem periodicSingularSeries_periodic (Y Q : ℕ) :
    Function.Periodic (periodicSingularSeries Y Q) (max Y Q).factorial := by
  intro n
  exact periodicSingularSeries_modEq Y Q (by simp [Nat.ModEq])

end JointDickman

end OAI
