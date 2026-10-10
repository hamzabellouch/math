import OAI.NumberTheory.OrdinaryCorrelations.Elliott.Cesaro

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset

namespace OrdinaryCorrelations.ElliottReductions

theorem biased_sequence_of_failure (a : ℕ → ℂ)
    (hfail : ¬ Tendsto (cesaro a) atTop (nhds 0)) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ ∃ N : ℕ → ℕ,
      Tendsto N atTop atTop ∧ (∀ j, 0 < N j) ∧
        ∀ j, γ * (N j : ℝ) ≤ ‖∑ n ∈ Icc 1 (N j), a n‖ := by
  classical
  rw [Metric.tendsto_atTop] at hfail
  push Not at hfail
  obtain ⟨ε, hε, hb⟩ := hfail
  choose N hNl hNb using fun j : ℕ => hb (j + 1)
  have hN : ∀ j, 0 < N j := fun j => lt_of_lt_of_le (Nat.zero_lt_succ j) (hNl j)
  have hlim : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans ((Nat.le_succ j).trans (hNl j))
  refine ⟨min ε 1, lt_min hε zero_lt_one, min_le_right _ _, N, hlim, hN, ?_⟩
  intro j
  have hraw := hNb j
  simp only [_root_.dist_zero_right, cesaro, norm_mul, norm_inv, Complex.norm_natCast] at hraw
  rw [mul_comm, ← div_eq_mul_inv] at hraw
  have hNj : (0 : ℝ) < N j := by exact_mod_cast hN j
  exact (mul_le_mul_of_nonneg_right (min_le_left ε 1) hNj.le).trans
    ((le_div_iff₀ hNj).mp hraw)

end OrdinaryCorrelations.ElliottReductions

end

end OAI
