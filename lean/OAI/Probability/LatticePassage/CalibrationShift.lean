import OAI.Probability.LatticePassage.MetricCalibration

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset Filter Topology

lemma scaleVertex_succ (k : ℕ) (d : Vertex) :
    scaleVertex (k+1) d = d + scaleVertex k d := by
  rw [scaleVertex_add]
  simp [scaleVertex, add_comm]

theorem averagedTargetCocycle_shift_identity (d x y : Vertex) (N : ℕ) (ω : Environment) :
    averagedTargetCocycle d N (environmentTranslation d ω) x y -
      averagedTargetCocycle d N ω (d+x) (d+y) =
        (targetCocycle (scaleVertex (N+1) d) ω (d+x) (d+y) -
          targetCocycle d ω (d+x) (d+y)) / N := by
  unfold averagedTargetCocycle
  rw [← sub_div, ← sum_sub_distrib]
  have he : ∀ k : ℕ,
      targetCocycle (scaleVertex (k+1) d) (environmentTranslation d ω) x y =
        targetCocycle (scaleVertex (k+1+1) d) ω (d+x) (d+y) := by
    intro k
    rw [scaleVertex_succ (k+1), targetCocycle_translation]
  simp_rw [he]
  rw [sum_range_sub (fun k : ℕ => targetCocycle (scaleVertex (k+1) d) ω (d+x) (d+y)) N]
  simp [scaleVertex]

theorem averagedTargetCocycle_shift_bound (d x y : Vertex) (N : ℕ) :
    ∀ᵐ ω ∂environmentLaw,
      |averagedTargetCocycle d N (environmentTranslation d ω) x y -
        averagedTargetCocycle d N ω (d+x) (d+y)| ≤
          2 * passageTime ω (d+x) (d+y) / N := by
  filter_upwards [targetCocycle_dominated] with ω hω
  rw [averagedTargetCocycle_shift_identity, abs_div,
    show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have h := abs_sub_le (targetCocycle (scaleVertex (N+1) d) ω (d+x) (d+y)) 0
    (targetCocycle d ω (d+x) (d+y))
  simp only [sub_zero, zero_sub, abs_neg] at h
  have h₁ := hω (scaleVertex (N+1) d) (d+x) (d+y)
  have h₂ := hω d (d+x) (d+y)
  linarith

theorem averagedTargetCocycle_shift_integral (d x y : Vertex) (N : ℕ) :
    (∫ ω : Environment,
      |averagedTargetCocycle d N (environmentTranslation d ω) x y -
        averagedTargetCocycle d N ω (d+x) (d+y)| ∂environmentLaw) ≤
      2 * (latticeDistance x y : ℝ) / N := by
  have hi := ((environmentTranslation_preserving d).integrable_comp_of_integrable
    (integrable_averagedTargetCocycle d x y N)).sub
    (integrable_averagedTargetCocycle d (d+x) (d+y) N)
  apply (integral_mono_ae hi.abs
    (((integrable_passageTime (d+x) (d+y)).const_mul 2).div_const N)
    (averagedTargetCocycle_shift_bound d x y N)).trans
  rw [integral_div, integral_const_mul, mean_passageTime_translation]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact mul_le_mul_of_nonneg_left (mean_passageTime_le_distance x y) (by norm_num)

theorem averagedTargetCocycle_shift_tendsto (d x y : Vertex) :
    Tendsto (fun N : ℕ => ∫ ω : Environment,
      |averagedTargetCocycle d N (environmentTranslation d ω) x y -
        averagedTargetCocycle d N ω (d+x) (d+y)| ∂environmentLaw) atTop (𝓝 0) := by
  exact squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (averagedTargetCocycle_shift_integral d x y)
    (tendsto_const_div_atTop_nhds_zero_nat (2*(latticeDistance x y : ℝ)))

end CompanionFPP

end OAI
