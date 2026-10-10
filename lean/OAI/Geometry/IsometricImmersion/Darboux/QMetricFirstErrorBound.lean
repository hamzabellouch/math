import OAI.Geometry.IsometricImmersion.Comparison.QFirstJetComparison

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_uniform_qMetricFirstError_bound (B D : ℝ) {d c : ℝ}
    (hD : 0 ≤ D) (hd : 0 < d) (hc : 0 < c) :
    ∃ H C : ℝ, 0 ≤ H ∧ 0 ≤ C ∧
      ∀ (gTau gStar : MetricField) (w : DarbouxState) (epsilon : ℝ),
        ‖qFirstBundle gStar w‖ ≤ B → d ≤ (gStar (statePoint w)).det →
        c ≤ |stateQDenominator gStar w| →
        ‖actualCurvatureFirstInput gTau (statePoint w)-
          actualCurvatureFirstInput gStar (statePoint w)‖ ≤ epsilon →
        epsilon ≤ 1 → (4*max B 0+2)*epsilon ≤ d/2 → H*epsilon ≤ c/2 →
        |curvatureDensity gTau (statePoint w)| ≤ D →
        c/2 ≤ |stateQDenominator gTau w| ∧
        |qMetricFirstError gTau gStar w| ≤ C*epsilon := by
  obtain ⟨H,F,L,hH,hF,hL,hcompare⟩ := exists_uniform_qFirst_comparison B hd hc
  refine ⟨H,D*F+L,hH,add_nonneg (mul_nonneg hD hF) hL,?_⟩
  intro gTau gStar w epsilon hB hdet hxx hdist he1 hsmall hxxsmall hdensity
  have hscale : 0 ≤ 4*max B 0+2 := by linarith [le_max_right B 0]
  have hb : ‖qFirstBundle gTau w-qFirstBundle gStar w‖ ≤ epsilon := by
    simpa only [qFirstBundle_distance] using hdist
  obtain ⟨hfloor,hfactor,hlower⟩ := hcompare (qFirstBundle gStar w) (qFirstBundle gTau w)
    hB hdet hxx (hb.trans he1)
    ((mul_le_mul_of_nonneg_left hb hscale).trans hsmall)
    ((mul_le_mul_of_nonneg_left hb hH).trans hxxsmall)
  have hxxTau : c/2 ≤ |stateQDenominator gTau w| := by
    simpa only [qFirstXX_bundle] using
      hfloor (qFirstBundle gTau w) (right_mem_segment ℝ _ _)
  have hfactorBase : |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w| ≤
      F*‖qFirstBundle gTau w-qFirstBundle gStar w‖ := by
    simpa only [qFirstDensityFactor_bundle] using hfactor
  have hlowerBase : |qMetricFirstLower gTau w-qMetricFirstLower gStar w| ≤
      L*‖qFirstBundle gTau w-qFirstBundle gStar w‖ := by
    simpa only [qFirstLower_bundle] using hlower
  have hfactor' : |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w| ≤ F*epsilon :=
    hfactorBase.trans (mul_le_mul_of_nonneg_left hb hF)
  have hlower' : |qMetricFirstLower gTau w-qMetricFirstLower gStar w| ≤ L*epsilon :=
    hlowerBase.trans (mul_le_mul_of_nonneg_left hb hL)
  refine ⟨hxxTau,?_⟩
  unfold qMetricFirstError
  calc
    _ ≤ |curvatureDensity gTau (statePoint w)| *
          |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w|+
        |qMetricFirstLower gTau w-qMetricFirstLower gStar w| := by
      simpa only [abs_mul] using abs_add_le
        (curvatureDensity gTau (statePoint w)*(qMetricDensityFactor gTau w-qMetricDensityFactor gStar w))
        (qMetricFirstLower gTau w-qMetricFirstLower gStar w)
    _ ≤ D*(F*epsilon)+L*epsilon := add_le_add
      (mul_le_mul hdensity hfactor' (abs_nonneg _) hD) hlower'
    _ = _ := by ring

theorem exists_actual_Q_forcing_error_bound (B D A : ℝ) {d c : ℝ}
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hd : 0 < d) (hc : 0 < c) :
    ∃ H C : ℝ, 0 ≤ H ∧ 0 ≤ C ∧
      ∀ (gTau gStar : MetricField) (U : Set Coord),
        SmoothPositiveOn gTau U → SmoothPositiveOn gStar U → IsOpen U →
        ∀ (z : Coord → ℝ) (p : Coord), p ∈ U → ∀ epsilon leading : ℝ,
          ‖qFirstBundle gStar (qSolutionJet z p)‖ ≤ B → d ≤ (gStar p).det →
          c ≤ |covHessian gStar z p 0 0| →
          ‖actualCurvatureFirstInput gTau p-actualCurvatureFirstInput gStar p‖ ≤ epsilon →
          epsilon ≤ 1 → (4*max B 0+2)*epsilon ≤ d/2 → H*epsilon ≤ c/2 →
          |curvatureDensity gTau p| ≤ D → |forcingCoefficient gStar z p| ≤ A →
          |(sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p))-
              2*forcingCoefficient gStar z p*leading| ≤
            2*A*|(curvatureDensity gTau p-curvatureDensity gStar p)-leading|+C*epsilon := by
  obtain ⟨H,C,hH,hC,herror⟩ := exists_uniform_qMetricFirstError_bound B D hD hd hc
  refine ⟨H,C,hH,hC,?_⟩
  intro gTau gStar U hgTau hgStar hU z p hp epsilon leading hB hdet hxx hdist
    he1 hsmall hxxsmall hdensity hforce
  obtain ⟨hfloor,herr⟩ := herror gTau gStar (qSolutionJet z p) epsilon hB
    (by simpa only [statePoint_qSolutionJet] using hdet)
    (by simpa only [stateQDenominator_qSolutionJet] using hxx)
    (by simpa only [statePoint_qSolutionJet] using hdist) he1 hsmall hxxsmall
    (by simpa only [statePoint_qSolutionJet] using hdensity)
  have hxxStar : covHessian gStar z p 0 0 ≠ 0 := by
    intro hz
    rw [hz,abs_zero] at hxx
    linarith
  have hxxTau : covHessian gTau z p 0 0 ≠ 0 := by
    rw [stateQDenominator_qSolutionJet] at hfloor
    intro hz
    rw [hz,abs_zero] at hfloor
    linarith
  rw [actual_Q_metric_forcing_leading_identity hgTau hgStar hU z hp hxxTau hxxStar]
  have hfactor : |2*forcingCoefficient gStar z p| ≤ 2*A := by
    simpa only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_left hforce (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ |2*forcingCoefficient gStar z p| *
        |(curvatureDensity gTau p-curvatureDensity gStar p)-leading|+
        |qMetricFirstError gTau gStar (qSolutionJet z p)| := by
      simpa only [abs_mul] using abs_add_le
        (2*forcingCoefficient gStar z p*((curvatureDensity gTau p-curvatureDensity gStar p)-leading))
        (qMetricFirstError gTau gStar (qSolutionJet z p))
    _ ≤ _ := add_le_add
      (mul_le_mul hfactor le_rfl (abs_nonneg _) (mul_nonneg (by norm_num) hA)) herr

end SmoothLocal.Pulse

end

end OAI
