import OAI.Analysis.KadisonKastler.FrequencySmoothing

namespace OAI

/-! # Positive smoothing heights tending to the boundary -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

def smoothingHeight (δ : ℝ) (n : ℕ) : ℝ := δ / ((n : ℝ) + 1)

theorem smoothingHeight_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    0 < smoothingHeight δ n := div_pos hδ (by positivity)

theorem smoothingHeight_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    smoothingHeight δ n ≤ δ := by
  change δ / ((n : ℝ) + 1) ≤ δ
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem smoothingHeight_tendsto (δ : ℝ) :
    Tendsto (smoothingHeight δ) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa only [smoothingHeight, one_div, div_eq_mul_inv, mul_zero, one_mul] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem poissonBoundaryApprox_smoothingHeight_tendsto
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (δ t : ℝ) (x : H) :
    Tendsto (fun n => poissonBoundaryApprox W hW t (smoothingHeight δ n) x) atTop
      (𝓝 ((W t : H →L[ℂ] H) x)) :=
  (poissonBoundaryApprox_tendsto W hW t x).comp (smoothingHeight_tendsto δ)

theorem poissonBoundaryApprox_star_smoothingHeight_tendsto
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hWs : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x))
    (δ t : ℝ) (x : H) :
    Tendsto (fun n => star (poissonBoundaryApprox W hW t (smoothingHeight δ n)) x) atTop
      (𝓝 (star (W t : H →L[ℂ] H) x)) :=
  (poissonBoundaryApprox_star_tendsto W hW hWs t x).comp (smoothingHeight_tendsto δ)

theorem norm_poissonBoundaryApprox_smoothingHeight_le_two
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) (n : ℕ) (t : ℝ) :
    ‖poissonBoundaryApprox W hW t (smoothingHeight δ n)‖ ≤ 2 := by
  have hr := smoothingHeight_pos hδ n
  have hrδ := smoothingHeight_le hδ.le n
  have he := Real.abs_exp_sub_one_le
    (show |smoothingHeight δ n| ≤ 1 by rw [abs_of_pos hr]; linarith)
  rw [abs_of_pos hr] at he
  exact (norm_poissonBoundaryApprox_le W hW t (smoothingHeight δ n)).trans
    (by linarith [le_abs_self (Real.exp (smoothingHeight δ n) - 1)])

end

end KadisonKastler

end OAI
