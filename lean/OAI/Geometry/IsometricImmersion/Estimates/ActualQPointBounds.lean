import OAI.Geometry.IsometricImmersion.Estimates.ActualQCompactBounds
import OAI.Geometry.IsometricImmersion.Metrics.ActualTestMetricPositive
import OAI.Geometry.IsometricImmersion.Estimates.ActualQWeightedRemainder
import OAI.Geometry.IsometricImmersion.Comparison.QMetricApproximationInputs
import OAI.Geometry.IsometricImmersion.Coordinates.ActualCentralShearMargins
import OAI.Geometry.IsometricImmersion.Coordinates.ActualPatchQRectangle

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem exists_actual_Q_point_bounds_from_reference_floor
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d c kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (N : ℕ) (hN : 1 < N) :
    ∃ A D dcompare : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ 0 < dcompare ∧
      ∀ delta : ℝ, 0 < delta → ∀ᶠ tau : ℕ in atTop,
        2 ≤ tau ∧ N ≤ tau ∧
        SmoothPositiveOn (testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ)) modelOpenSquare ∧
        ∀ (gTau : MetricField) (U : Set Coord) (z : Coord → ℝ),
          SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
          BoundedAdmissibleHeight gTau M z →
          (∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            c ≤ |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0|) →
          ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            QPulsePointBounds gStar gTau z modelOpenSquare q0 (boundedClassWidth kappa M*r/16)
              delta (tau : ℝ) N (8*G) (G+1) (max (8*G) (boundedClassShearedStateBudget q0 M))
              D A d dcompare c (metricApproximationAccuracy tau)
              (qPulseFirstJetBudget (boundedClassWidth kappa M*r/16)
                (div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)) N delta (tau : ℝ)) p := by
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let BQ := max (8*G) (boundedClassShearedStateBudget q0 M)
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have ha : 0 < a := div_pos (mul_pos hL hr) (by norm_num)
  have hq1 : |q0| ≤ 1 := hq0.trans (by norm_num)
  obtain ⟨A,hA,hforce⟩ := exists_actual_forcingCoefficient_bound BQ hd hc
  obtain ⟨D,hD,hdensity⟩ := exists_actual_curvatureDensity_bound G hG hd
  obtain ⟨dcompare,epsilon,hdcompare,he,_,hdetTolerance⟩ := exists_metric_value_det_tolerance hgStar hV hSV
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  refine ⟨A,D,dcompare,hA,hD,hdcompare,?_⟩
  intro delta hdelt
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [testMetric_positive_on_modelSquare_eventually hgStar hV hSV q0 a ha N (by omega) delta,
    pulseTensor_finite_coeff_jets_eventually_small q0 a ha 1 N hN delta (by norm_num : (0 : ℝ) < 1),
    pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N (by omega) delta he,
    hwidth,eventually_ge_atTop 2,eventually_ge_atTop N] with tau hpositive hsmall hsmall0 hw ht2 htN
  let test := testMetric gStar q0 a N delta (tau : ℝ)
  have htest : SmoothPositiveOn test modelOpenSquare :=
    ⟨fun i j => (testMetric_coeff_contDiffOn hgStar q0 a N delta (tau : ℝ) i j).mono hOV,
      fun p hp => hpositive p (modelOpenSquare_subset hp)⟩
  refine ⟨ht2,htN,htest,?_⟩
  intro gTau U z hgTau hU hSU hclass hgB hdet happ href p hp
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hx : |p 0| ≤ L*r := (abs_le.mpr hp.1).trans (by linarith [mul_pos hL hr])
  have ht : |p 1| ≤ r := (abs_le.mpr hp.2).trans hbr
  have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
  have hpC := inverseShear_slab_mem_centralBox hL1 hr.le hLr hq0 hx ht
  have hpO := centralBox_subset_modelOpenSquare hpC
  have hpS := centralBox_subset_modelSquare hpC
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgTauO : SmoothPositiveOn gTau modelOpenSquare :=
    ⟨fun i j => (hgTau.1 i j).mono hOU,fun p hp => hgTau.2 p (hOU hp)⟩
  have hfirst := sheared_first_input_norm_le_of_original_jets hgStar hV (hSV hpS) hG hq1
    (fun i j k hk => hgStarB i j k (by omega) _ hpS)
  have hdetRef : d ≤ (metricInShearCoordinates gStar q0 p).det := by
    rw [metricDet_in_shear_coordinates]
    exact hdStar _ hpS
  have htestJet (i j : Fin 2) (k : ℕ) (hk : k ≤ 1) :
      ‖iteratedFDeriv ℝ k (fun q => test q i j) (inverseShearCoordinates q0 p)‖ ≤ G+1 := by
    have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j) :=
      (contDiff_apply ℝ ℝ j).comp
        ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta (tau : ℝ)))
    change ‖iteratedFDeriv ℝ k ((fun q => gStar q i j)+
      (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j)) (inverseShearCoordinates q0 p)‖ ≤ _
    rw [iteratedFDeriv_add_apply
      (((hgStar.1 i j).contDiffAt (hV.mem_nhds (hSV hpS))).of_le (WithTop.coe_le_coe.mpr le_top))
      (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
    exact (norm_add_le _ _).trans (add_le_add (hgStarB i j k (by omega) _ hpS) (hsmall.2 i j k hk _))
  have htestFirst : ‖actualCurvatureFirstInput test (inverseShearCoordinates q0 p)‖ ≤ G+1 := by
    apply actual_first_input_norm_le (by linarith)
    · intro i j
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using htestJet i j 0 (by norm_num)
    · intro i j k
      exact (norm_iteratedCoordPartial_le_jet (htest.1 j k) modelOpenSquare_isOpen [i] hpO).trans
        (htestJet j k 1 le_rfl)
  have htestDet : dcompare ≤ (test (inverseShearCoordinates q0 p)).det := by
    apply hdetTolerance _ _ hpS
    intro i j
    have hh := hsmall0.2 i j 0 le_rfl (inverseShearCoordinates q0 p)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,test,testMetric,Pi.add_apply,
      Matrix.add_apply,add_sub_cancel_left] using hh
  have herr := actual_metric_jet_approximation_inputs hgTauO htest modelOpenSquare_isOpen hpO
    (fun i j k hk => happ i j k (hk.trans ht2) _ hpS)
  have hstate : ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ boundedClassShearedStateBudget q0 M := by
    apply bounded_class_sheared_solution_state_bound hclass q0 hpS
    refine ⟨hx.trans (hLr.trans (by norm_num)),ht.trans ?_⟩
    have hrsmall : r ≤ L*r := by nlinarith
    exact hrsmall.trans (hLr.trans (by norm_num))
  have hbundle : ‖qFirstBundle (metricInShearCoordinates gStar q0)
      (qSolutionJet (heightInShearCoordinates z q0) p)‖ ≤ BQ := by
    change max ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0)
      (statePoint (qSolutionJet (heightInShearCoordinates z q0) p))‖
      ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ BQ
    rw [statePoint_qSolutionJet]
    exact max_le_max hfirst hstate
  have hbase := actual_sheared_first_jet_error_from_Ctau hgStarO htest hgTauO modelOpenSquare_isOpen
    hq1 ha (by omega : 0 < N) ht2 (by omega : N-1 ≤ tau) hpO
      (fun i j k hk => happ i j k hk _ hpS)
  have hdetTau : d ≤ (gTau (inverseShearCoordinates q0 p)).det := by
    have hh := hdet _ hpS
    rwa [abs_of_pos (hgTau.2 _ (hSU hpS)).det_pos] at hh
  have hDactual := hdensity gTau U hgTau hU _ (hSU hpS)
    (fun i j k hk => hgB i j k hk _ hpS) hdetTau
  have hAactual := hforce (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0)
    (inverseShearCoordinates q0 ⁻¹' V) (metricInShearCoordinates_smoothPositive hgStar q0)
      p (hSV hpS) hbundle hdetRef (href p hp)
  exact ⟨hpO,hfirst,hdetRef,htestFirst,htestDet,herr.1,herr.2,hbundle,href p hp,hbase,hDactual,hAactual⟩

end SmoothLocal.Perturbation

end

end OAI
