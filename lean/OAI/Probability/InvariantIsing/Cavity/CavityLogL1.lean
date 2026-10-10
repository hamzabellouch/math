import OAI.Probability.InvariantIsing.Cavity.CavityMovingLog

namespace OAI

/-! Removing a small change in a capped normalizer.  A uniform second
moment of its negative logarithm makes convergence in mean sufficient. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_log_floor_lipschitz {z w δ : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hδ : 0 < δ) :
    |Real.log (z + δ) - Real.log (w + δ)| ≤ |z - w| / δ := by
  have hone {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
      Real.log (a + δ) - Real.log (b + δ) ≤ (a - b) / δ := by
    have hbδ : 0 < b + δ := by positivity
    have haδ : 0 < a + δ := by linarith
    calc
      _ ≤ (a - b) / (b + δ) := by
        rw [← Real.log_div haδ.ne' hbδ.ne']
        apply (Real.log_le_sub_one_of_pos (div_pos haδ hbδ)).trans_eq
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hδ (by linarith)
  rcases le_total w z with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by positivity)
        (by linarith : w + δ ≤ z + δ))), abs_of_nonneg (sub_nonneg.mpr h)]
    exact hone hw h
  · rw [abs_sub_comm (Real.log _), abs_sub_comm z,
        abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by positivity)
          (by linarith : z + δ ≤ w + δ))), abs_of_nonneg (sub_nonneg.mpr h)]
    exact hone hz h

theorem cavity_log_of_mean_distance
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z W : (n : ℕ) → Ω n → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M K : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hZ0 : ∀ n ω, 0 < Z n ω) (hW0 : ∀ n ω, 0 < W n ω)
    (hZM : ∀ n ω, Z n ω ≤ M) (hWM : ∀ n ω, W n ω ≤ M)
    (hiZ : ∀ n, Integrable (fun ω => (max (-Real.log (Z n ω)) 0)^2) (P n))
    (hiW : ∀ n, Integrable (fun ω => (max (-Real.log (W n ω)) 0)^2) (P n))
    (hKZ : ∀ n, (∫ ω, (max (-Real.log (Z n ω)) 0)^2 ∂P n) ≤ K)
    (hKW : ∀ n, (∫ ω, (max (-Real.log (W n ω)) 0)^2 ∂P n) ≤ K)
    (hdist : Tendsto (fun n => ∫ ω, |Z n ω - W n ω| ∂P n) atTop (𝓝 0)) :
    Tendsto (fun n => (∫ ω, Real.log (Z n ω) ∂P n) -
      ∫ ω, Real.log (W n ω) ∂P n) atTop (𝓝 0) := by
  apply cavity_moving_unfloored_log P P Z W hZ hW hM hK
    hZ0 hW0 hZM hWM hiZ hiW hKZ hKW
  intro δ hδ
  have hi n : Integrable (fun ω => |Z n ω - W n ω|) (P n) := by
    apply integrable_of_measurable_abs_le ((hZ n).sub (hW n)).abs (c := 2*M)
    intro ω
    rw [abs_abs]
    exact (abs_sub (Z n ω) (W n ω)).trans (by
      rw [abs_of_pos (hZ0 n ω), abs_of_pos (hW0 n ω)]
      linarith [hZM n ω, hWM n ω])
  apply squeeze_zero_norm (fun n => ?_) (by simpa using hdist.div_const δ)
  rw [Real.norm_eq_abs, ← integral_sub
    (cavity_floored_log_integrable (P n) (Z n) (hZ n) (hZ0 n) (hZM n) hδ)
    (cavity_floored_log_integrable (P n) (W n) (hW n) (hW0 n) (hWM n) hδ)]
  calc
    _ ≤ ∫ ω, |Real.log (Z n ω + δ) - Real.log (W n ω + δ)| ∂P n :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, |Z n ω - W n ω| / δ ∂P n :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) ((hi n).div_const δ)
        (ae_of_all _ fun ω => cavity_log_floor_lipschitz (hZ0 n ω).le (hW0 n ω).le hδ)
    _ = _ := by rw [integral_div]

end InvariantIsing

end

end OAI
