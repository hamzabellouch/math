import OAI.Geometry.IsometricImmersion.Darboux.QFirstJetFunctions
import OAI.Geometry.IsometricImmersion.Calculus.BoundedClassInitialJet

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_forcingCoefficient_bound (B : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U : Set Coord),
      SmoothPositiveOn g U → ∀ p ∈ U,
      ‖qFirstBundle g (qSolutionJet z p)‖ ≤ B → d ≤ (g p).det →
      c ≤ |covHessian g z p 0 0| → |forcingCoefficient g z p| ≤ A := by
  obtain ⟨A,hA⟩ := (qFirstTube_isCompact B hd c).exists_bound_of_continuousOn
    (qFirstDensityFactor_contDiffOn.continuousOn.mono (qFirstTube_subset_domain B hd hc))
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro g z U hg p hp hB hdet hxx
  have hin : qFirstBundle g (qSolutionJet z p) ∈ qFirstTube B d c := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using hB
    · change d ≤ qFirstDet (qFirstBundle g (qSolutionJet z p))
      simpa only [qFirstDet_bundle,statePoint_qSolutionJet] using hdet
    · change c ≤ |qFirstXX (qFirstBundle g (qSolutionJet z p))|
      simpa only [qFirstXX_bundle,stateQDenominator_qSolutionJet] using hxx
  have hne := abs_pos.mp (hc.trans_le hxx)
  have hh := hA _ hin
  rw [qFirstDensityFactor_bundle,qMetricDensityFactor_at_height hg z hp hne,
    Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hnonneg := abs_nonneg (forcingCoefficient g z p)
  linarith [le_max_left A 0]

theorem exists_actual_curvatureDensity_bound (G : ℝ) (hG : 0 ≤ G) {d : ℝ} (hd : 0 < d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ p ∈ U,
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      d ≤ (g p).det → |curvatureDensity g p| ≤ D := by
  obtain ⟨C,hC⟩ := (curvatureFirstTube_isCompact G d).exists_bound_of_continuousOn
    (curvatureFirstFunction_contDiffOn.continuousOn.mono (curvatureFirstTube_subset_domain G hd))
  refine ⟨2*G+max C 0,by positivity,?_⟩
  intro g U hg hU p hp hjet hdet
  have hfirst : ‖actualCurvatureFirstInput g p‖ ≤ G := by
    apply actual_first_input_norm_le hG
    · intro i j
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hjet i j 0 (by norm_num)
    · intro i j k
      exact (norm_iteratedCoordPartial_le_jet (hg.1 j k) hU [i] hp).trans
        (hjet j k 1 (by norm_num))
  have hin : actualCurvatureFirstInput g p ∈ curvatureFirstTube G d :=
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hfirst,hdet⟩
  have hlow : |curvatureLowerTerm g p| ≤ max C 0 := by
    exact (hC _ hin).trans (le_max_left _ _)
  have hsecond (i j k l : Fin 2) : |coordPartial i (coordPartial j (fun q => g q k l)) p| ≤ G :=
    (norm_iteratedCoordPartial_le_jet (hg.1 k l) hU [i,j] hp).trans (hjet k l 2 (by norm_num))
  have habs : |coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p+
      coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p| ≤ 2*G :=
    (abs_add_le _ _).trans ((add_le_add (hsecond 0 0 1 1) (hsecond 1 1 0 0)).trans_eq (by ring))
  have hhalf : |(coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p+
      coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p)/2| ≤ G := by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  unfold curvatureDensity
  rw [gaussianCurvature_density_principal_part hg hU hp]
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans ((add_le_add (hsecond 0 1 0 1) hhalf).trans_eq (by ring))) hlow))

end SmoothLocal.Pulse

end

end OAI
