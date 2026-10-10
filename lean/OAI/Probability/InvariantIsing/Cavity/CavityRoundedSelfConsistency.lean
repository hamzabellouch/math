import OAI.Probability.InvariantIsing.Cavity.CavitySelfConsistencyLimit

namespace OAI

/-! The cavity identity is initially tested at the rounded overlap.
Passing those tests to the limiting overlap gives the L1 conclusion. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_rounding_test_difference (p : OverlapPath)
    (q B : ℕ → OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => q n s) atTop (𝓝 (p s)))
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) -
        ∫ s, Φ (q n s) * (B n s - q n s) ∂pathMeasure) atTop (𝓝 0) := by
  let F := fun n s => Φ (p s) * (B n s - p s) - Φ (q n s) * (B n s - q n s)
  have hΦ (z : ℝ) : |Φ z| ≤ ‖Φ‖ := by
    simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm z
  have hdiff (v w : OverlapPath) (s : ℝ) : |v s - w s| ≤ 1 :=
    abs_le.mpr ⟨by linarith [v.nonneg s, w.le_one s],
      by linarith [v.le_one s, w.nonneg s]⟩
  have hi (v w : OverlapPath) : Integrable (fun s => Φ (v s) * (w s - v s)) pathMeasure := by
    apply Integrable.of_bound ((Φ.continuous.measurable.comp v.measurable).mul
      (w.measurable.sub v.measurable)).aestronglyMeasurable ‖Φ‖
    exact ae_of_all _ fun s => by
      change |Φ (v s) * (w s - v s)| ≤ ‖Φ‖
      rw [abs_mul]
      exact (mul_le_mul (hΦ _) (hdiff w v s)
        (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
  have hbound (n : ℕ) (s : ℝ) : |F n s| ≤
      |Φ (p s) - Φ (q n s)| + ‖Φ‖ * |q n s - p s| := by
    have he : F n s = (Φ (p s) - Φ (q n s)) * (B n s - p s) +
        Φ (q n s) * (q n s - p s) := by dsimp only [F]; ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add
      ((mul_le_mul_of_nonneg_left (hdiff (B n) p s) (abs_nonneg _)).trans_eq (mul_one _))
      (mul_le_mul_of_nonneg_right (hΦ _) (abs_nonneg _))
  have hlim := tendsto_integral_of_dominated_convergence (μ := pathMeasure)
    (F := F) (f := fun _ => (0 : ℝ)) (fun _ => 3 * ‖Φ‖)
    (fun n => ((hi p (B n)).sub (hi (q n) (B n))).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]
      have ha : |Φ (p s) - Φ (q n s)| ≤ 2 * ‖Φ‖ :=
        (abs_sub _ _).trans (by linarith [hΦ (p s), hΦ (q n s)])
      have hb := mul_le_mul_of_nonneg_left (hdiff (q n) p s) (norm_nonneg Φ)
      exact (hbound n s).trans (by linarith)) (by
      filter_upwards [hq] with s hs
      have hφ := Φ.continuous.continuousAt.tendsto.comp hs
      have hb : Tendsto (fun n => |Φ (p s) - Φ (q n s)| + ‖Φ‖ * |q n s - p s|)
          atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => Φ (p s)) atTop (𝓝 (Φ (p s))) := tendsto_const_nhds
        simpa only [Function.comp_apply, sub_self, abs_zero, mul_zero, zero_add] using
          ((hc.sub hφ).abs.add ((hs.sub_const (p s)).abs.const_mul ‖Φ‖))
      apply squeeze_zero_norm (fun n => ?_) hb
      simpa only [Real.norm_eq_abs] using hbound n s)
  have he (n : ℕ) : (∫ s, F n s ∂pathMeasure) =
      (∫ s, Φ (p s) * (B n s - p s) ∂pathMeasure) -
        ∫ s, Φ (q n s) * (B n s - q n s) ∂pathMeasure :=
    integral_sub (hi p (B n)) (hi (q n) (B n))
  simpa only [he, integral_zero] using hlim

theorem cavity_rounded_self_consistency_l1 (p : OverlapPath)
    (q B : ℕ → OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => q n s) atTop (𝓝 (p s)))
    (htied : ∀ n x y, p x = p y → B n x = B n y)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (q n s) * (B n s - q n s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, |B n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  apply cavity_self_consistency_l1 p B htied
  intro Φ
  have h := (cavity_rounding_test_difference p q B hq Φ).add (htest Φ)
  simpa only [sub_add_cancel, add_zero] using h

/-- Finite-grid endpoints may be removed from a common full-measure set;
ties there suffice for the actual rounded cavity fields. -/
theorem cavity_rounded_self_consistency_l1_on (p : OverlapPath)
    (q B : ℕ → OverlapPath)
    (hq : ∀ᵐ s ∂pathMeasure, Tendsto (fun n => q n s) atTop (𝓝 (p s)))
    (D : Set ℝ) (hDae : ∀ᵐ s ∂pathMeasure, s ∈ D)
    (htied : ∀ n x, x ∈ D → ∀ y, y ∈ D → p x = p y → B n x = B n y)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, Tendsto
      (fun n => ∫ s, Φ (q n s) * (B n s - q n s) ∂pathMeasure) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, |B n s - p s| ∂pathMeasure) atTop (𝓝 0) := by
  apply cavity_self_consistency_l1_on p B D hDae htied
  intro Φ
  have h := (cavity_rounding_test_difference p q B hq Φ).add (htest Φ)
  simpa only [sub_add_cancel, add_zero] using h

end InvariantIsing

end

end OAI
