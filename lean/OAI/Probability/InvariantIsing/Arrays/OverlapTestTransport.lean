import OAI.Probability.InvariantIsing.Cavity.CavityMagneticBlockModulus

namespace OAI

/-! L1 replacement transports the physical constrained overlap tests
to the magnetic block paths used in the variational problem. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing

lemma integrable_overlap_weighted_test (q a : OverlapPath) (Φ : ℝ →ᵇ ℝ) :
    Integrable (fun s => Φ (q s)*(a s-q s)) pathMeasure := by
  apply integrable_of_measurable_abs_le
    ((Φ.continuous.measurable.comp q.measurable).mul (a.measurable.sub q.measurable))
  intro s
  change |Φ (q s)*(a s-q s)| ≤ ‖Φ‖
  rw [abs_mul]
  have hd : |a s-q s| ≤ 1 := abs_le.mpr
    ⟨by linarith [a.nonneg s,q.le_one s], by linarith [a.le_one s,q.nonneg s]⟩
  exact (mul_le_mul (Φ.norm_coe_le_norm _) hd (abs_nonneg _) (norm_nonneg Φ)).trans_eq (mul_one _)

lemma overlap_weighted_test_sub_le (q a b : OverlapPath) (Φ : ℝ →ᵇ ℝ) :
    |(∫ s, Φ (q s)*(a s-q s) ∂pathMeasure) -
      ∫ s, Φ (q s)*(b s-q s) ∂pathMeasure| ≤
      ‖Φ‖ * ∫ s, |a s-b s| ∂pathMeasure := by
  rw [← integral_sub (integrable_overlap_weighted_test q a Φ)
    (integrable_overlap_weighted_test q b Φ)]
  have he : (fun s => Φ (q s)*(a s-q s)-Φ (q s)*(b s-q s)) =
      (fun s => Φ (q s)*(a s-b s)) := by funext s; ring
  rw [he]
  calc
    _ ≤ ∫ s, |Φ (q s)*(a s-b s)| ∂pathMeasure := abs_integral_le_integral_abs
    _ ≤ ∫ s, ‖Φ‖ * |a s-b s| ∂pathMeasure := by
      apply integral_mono
      · have hi := (integrable_overlap_weighted_test q a Φ).sub
          (integrable_overlap_weighted_test q b Φ)
        change Integrable (fun s => Φ (q s)*(a s-q s)-Φ (q s)*(b s-q s)) pathMeasure at hi
        rw [he] at hi
        exact hi.abs
      · exact (a.integrable.sub b.integrable).abs.const_mul _
      · intro s
        change |Φ (q s)*(a s-b s)| ≤ ‖Φ‖ * |a s-b s|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (Φ.norm_coe_le_norm _) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

theorem overlap_weighted_test_l1_transport (q a b : ℕ → OverlapPath)
    (hab : Tendsto (fun n => ∫ s, |a n s-b n s| ∂pathMeasure) atTop (𝓝 0))
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun n => (∫ s, Φ (q n s)*(a n s-q n s) ∂pathMeasure) -
      ∫ s, Φ (q n s)*(b n s-q n s) ∂pathMeasure) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_) (by simpa using hab.const_mul ‖Φ‖)
  simpa only [Real.norm_eq_abs] using overlap_weighted_test_sub_le (q n) (a n) (b n) Φ

end InvariantIsing

end

end OAI
