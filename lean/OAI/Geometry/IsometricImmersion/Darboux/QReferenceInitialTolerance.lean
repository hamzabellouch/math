import OAI.Geometry.IsometricImmersion.Comparison.QFirstJetComparison
import OAI.Geometry.IsometricImmersion.Taylor.TaylorCauchyData

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor

theorem exists_reference_XX_tolerance (B : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ a b : QFirstInput,
      ‖a‖ ≤ B → d ≤ qFirstDet a → c ≤ |qFirstXX a| →
      ‖b - a‖ ≤ epsilon → c / 2 ≤ |qFirstXX b| := by
  obtain ⟨H, _, _, hH, _, _, hcompare⟩ := exists_uniform_qFirst_comparison B hd hc
  let D := 4 * max B 0 + 2
  have hD : 0 < D := by dsimp [D]; positivity
  let epsilon := min 1 (min (d / (2 * D)) (c / (2 * (H + 1))))
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  refine ⟨epsilon, he, ?_⟩
  intro a b ha hdet hxx hdist
  have he1 : epsilon ≤ 1 := min_le_left _ _
  have hed : epsilon ≤ d / (2 * D) := (min_le_right _ _).trans (min_le_left _ _)
  have hec : epsilon ≤ c / (2 * (H + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hdist0 : 0 ≤ ‖b - a‖ := norm_nonneg _
  have hdsmall : D * ‖b - a‖ ≤ d / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * D by positivity)).mp (hdist.trans hed)
    nlinarith
  have hcsmall : H * ‖b - a‖ ≤ c / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * (H + 1) by positivity)).mp (hdist.trans hec)
    nlinarith
  exact (hcompare a b ha hdet hxx (hdist.trans he1) hdsmall hcsmall).1 b
    (right_mem_segment ℝ a b)

theorem exists_actual_reference_XX_tolerance (G W : ℝ) {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (g h : MetricField) (w : DarbouxState),
      ‖actualCurvatureFirstInput g (statePoint w)‖ ≤ G → ‖w‖ ≤ W →
      d ≤ (g (statePoint w)).det → c ≤ |stateQDenominator g w| →
      ‖actualCurvatureFirstInput h (statePoint w) - actualCurvatureFirstInput g (statePoint w)‖ ≤ epsilon →
      c / 2 ≤ |stateQDenominator h w| := by
  obtain ⟨epsilon, he, htol⟩ := exists_reference_XX_tolerance (max G W) hd hc
  refine ⟨epsilon, he, ?_⟩
  intro g h w hg hw hdet hxx hdist
  have ha : ‖qFirstBundle g w‖ ≤ max G W := by
    change max ‖actualCurvatureFirstInput g (statePoint w)‖ ‖w‖ ≤ max G W
    exact max_le_max hg hw
  exact htol (qFirstBundle g w) (qFirstBundle h w) ha hdet hxx
    (by simpa only [qFirstBundle_distance] using hdist)

theorem exists_reference_linearCauchy_XX_tolerance (G W : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (g h : MetricField) (z : Coord → ℝ) (U : Set Coord),
      ContDiffOn ℝ ∞ z U → IsOpen U → ∀ left right a : ℝ,
      (∀ x ∈ Ioo left right, (![x, a] : Coord) ∈ U) →
      ∀ x ∈ Ioo left right,
      ‖actualCurvatureFirstInput g ![x, a]‖ ≤ G → ‖qSolutionJet z ![x, a]‖ ≤ W →
      d ≤ (g ![x, a]).det → c ≤ |covHessian g z ![x, a] 0 0| →
      ‖actualCurvatureFirstInput h ![x, a] - actualCurvatureFirstInput g ![x, a]‖ ≤ epsilon →
      c / 2 ≤ |covHessian h (linearCauchy a (heightCauchyValue z a) (heightCauchyVelocity z a))
        ![x, a] 0 0| := by
  obtain ⟨epsilon, he, htol⟩ := exists_actual_reference_XX_tolerance G W hd hc
  refine ⟨epsilon, he, ?_⟩
  intro g h z U hz hU left right a hcut x hx hg hw hdet hxx hdist
  rw [linearCauchy_height_initial_hessian hz hU left right a hcut hx]
  have hb := htol g h (qSolutionJet z ![x, a])
    (by simpa only [statePoint_qSolutionJet] using hg) hw
    (by simpa only [statePoint_qSolutionJet] using hdet)
    (by simpa only [stateQDenominator_qSolutionJet] using hxx)
    (by simpa only [statePoint_qSolutionJet] using hdist)
  simpa only [stateQDenominator_qSolutionJet] using hb

end SmoothLocal.Pulse

end

end OAI
