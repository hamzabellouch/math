import OAI.Analysis.LipschitzHilbert.Estimates.MartingaleGoodLambda

namespace OAI

/-! Iterating the first-crossing contraction gives a geometric tail with
constants independent of the number of time steps. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

theorem martingale_geometric_tail (hF : Martingale F ℱ μ) (N : ℕ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) (k : ℕ) :
    μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) ((k : ℝ) * (D + 2 * A)) N) ≤
      (1 / 2 : ℝ) ^ k * μ.real univ := by
  induction k with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, pow_zero, one_mul] using
      (measureReal_mono (μ := μ) (subset_univ
        (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) 0 N)))
  | succ k ih =>
    have hlambda : 0 ≤ (k : ℝ) * (D + 2 * A) := mul_nonneg (Nat.cast_nonneg k) (by linarith)
    have h := martingale_goodLambda hF N hA hD hlambda hBMO hjump
    have heq : (k : ℝ) * (D + 2 * A) + D + 2 * A =
        ((k + 1 : ℕ) : ℝ) * (D + 2 * A) := by push_cast; ring
    rw [heq] at h
    exact h.trans (by simpa only [pow_succ, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2))

theorem martingale_terminal_geometric_tail (hF : Martingale F ℱ μ) (N : ℕ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) (k : ℕ) :
    μ.real {x | (k : ℝ) * (D + 2 * A) < ‖F N x - F 0 x‖} ≤
      (1 / 2 : ℝ) ^ k * μ.real univ := by
  apply (measureReal_mono (μ := μ) (show
    {x | (k : ℝ) * (D + 2 * A) < ‖F N x - F 0 x‖} ⊆
      finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) ((k : ℝ) * (D + 2 * A)) N from
        fun _ hx => ⟨N,le_rfl,hx⟩)).trans
  exact martingale_geometric_tail hF N hA hD hBMO hjump k

end LipschitzHilbert

end

end OAI
