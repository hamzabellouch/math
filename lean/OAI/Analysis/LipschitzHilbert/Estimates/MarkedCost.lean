import OAI.Analysis.LipschitzHilbert.Estimates.MarkedShells
import OAI.Analysis.LipschitzHilbert.Trees.UnaryEnergy

namespace OAI

/-! The actual logarithmic marked-residual estimate of §10, `src-27`
and `res:marked-cost`, from the square sum and positive marked drops. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem marked_log_correction_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n a p d : ℝ} (hn : 0 < n) (hp : 1 ≤ p) (hd : 0 < d) (A A₀ : E) :
    Real.log (vertexAmount n A a p / d) - Real.log (vertexAmount n A₀ a p / d) ≤
      p * n ^ ((a - 1) / p - 1) * ‖A - A₀‖ := by
  rw [Real.log_div (vertexAmount_pos (a := a) (p := p) hn A).ne' hd.ne',
    Real.log_div (vertexAmount_pos (a := a) (p := p) hn A₀).ne' hd.ne', sub_sub_sub_cancel_right]
  exact (le_abs_self _).trans (log_vertexAmount_lipschitz hn hp A A₀)

theorem marked_log_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ → ℝ) (hn : Antitone n) (S : Finset ℕ)
    (A A₀ : ℕ → E) (denominator : ℕ → ℝ)
    {a p c M B : ℝ} (hp : 1 ≤ p) (hc : 0 < c) (hM : 1 ≤ M)
    (hμ : (a - 1) / p ≤ 1 / 12) (hB : 0 ≤ B)
    (hdrop : ∀ i ∈ S, c ≤ n i - n (i + 1))
    (hmass : ∀ i ∈ S, M ≤ n i) (hden : ∀ i ∈ S, 0 < denominator i)
    (hsquare : (∑ i ∈ S, ‖A i - A₀ i‖ ^ 2) ≤ B ^ 2) :
    (∑ i ∈ S, (Real.log (vertexAmount (n i) (A i) a p / denominator i) -
        Real.log (vertexAmount (n i) (A₀ i) a p / denominator i))) ≤
      p * Real.sqrt (2 * (1 + 3 / c)) *
        M ^ (-(1 / 2 : ℝ) + (a - 1) / p) * B := by
  have hM0 : 0 < M := by linarith
  have hnp (i : ℕ) (hi : i ∈ S) : 0 < n i := hM0.trans_le (hmass i hi)
  have hweights := marked_weight_sum n hn S hc hM hμ hdrop hmass
  have hweightSquare :
      (∑ i ∈ S, (n i ^ ((a - 1) / p - 1)) ^ 2) ≤
        2 * (1 + 3 / c) * M ^ (-1 + 2 * ((a - 1) / p)) := by
    convert hweights using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hnp i hi).le]
    congr 1
    ring
  have hrootWeight : Real.sqrt (∑ i ∈ S, (n i ^ ((a - 1) / p - 1)) ^ 2) ≤
      Real.sqrt (2 * (1 + 3 / c)) * M ^ (-(1 / 2 : ℝ) + (a - 1) / p) := by
    apply (Real.sqrt_le_sqrt hweightSquare).trans_eq
    rw [Real.sqrt_mul (by positivity)]
    simp_rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hM0.le]
    congr 2
    ring
  have hrootResidual : Real.sqrt (∑ i ∈ S, ‖A i - A₀ i‖ ^ 2) ≤ B := by
    exact (Real.sqrt_le_sqrt hsquare).trans_eq (Real.sqrt_sq hB)
  calc
    _ ≤ ∑ i ∈ S, p * n i ^ ((a - 1) / p - 1) * ‖A i - A₀ i‖ :=
      Finset.sum_le_sum fun i hi => marked_log_correction_le (hnp i hi) hp (hden i hi) _ _
    _ = p * ∑ i ∈ S, n i ^ ((a - 1) / p - 1) * ‖A i - A₀ i‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ p * (Real.sqrt (∑ i ∈ S, (n i ^ ((a - 1) / p - 1)) ^ 2) *
        Real.sqrt (∑ i ∈ S, ‖A i - A₀ i‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S _ _) (by linarith)
    _ ≤ p * ((Real.sqrt (2 * (1 + 3 / c)) *
        M ^ (-(1 / 2 : ℝ) + (a - 1) / p)) * B) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul hrootWeight hrootResidual (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
