import OAI.Geometry.IsometricImmersion.Metrics.ActualLowMetricBudget
import OAI.Geometry.IsometricImmersion.Pulses.PulseEdgeReferenceDistance

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem exists_metric_value_det_tolerance
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ d epsilon : ℝ, 0 < d ∧ 0 < epsilon ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ (g : MetricField) (p : Coord), p ∈ modelSquare →
        (∀ i j : Fin 2, |g p i j-gStar p i j| ≤ epsilon) → d ≤ (g p).det := by
  obtain ⟨B,hB,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV 0
  obtain ⟨d0,hd0,hfloor⟩ := modelSquare_isCompact.exists_forall_le'
    ((metricDet_contDiffOn hgStar).continuousOn.mono hSV)
    (fun p hp => (hgStar.2 p (hSV hp)).det_pos)
  let D := 4*B+2
  have hD : 0 < D := by dsimp [D]; positivity
  let epsilon := min 1 (d0/(2*D))
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  refine ⟨d0/2,epsilon,by positivity,he,?_,?_⟩
  · intro p hp
    exact (by linarith : d0/2 ≤ d0).trans (hfloor p hp)
  intro g p hp hclose
  have hgB : ‖gStar p‖ ≤ B := by
    apply (Matrix.norm_le_iff hB).2
    intro i j
    simpa only [norm_iteratedFDeriv_zero] using hbase i j 0 le_rfl p hp
  have hdist : ‖g p-gStar p‖ ≤ epsilon := by
    apply (Matrix.norm_le_iff he.le).2
    intro i j
    simpa only [Matrix.sub_apply,Real.norm_eq_abs] using hclose i j
  have hdetdiff := det_sub_le_small_first_distance (gStar p) (g p) hB he.le
    (min_le_left _ _) hgB hdist
  have hsmall : D*epsilon ≤ d0/2 := by
    have htwoD : (0 : ℝ) < 2*D := mul_pos (by norm_num) hD
    have h := (le_div_iff₀ htwoD).mp (min_le_right 1 (d0/(2*D)))
    change epsilon*(2*D) ≤ d0 at h
    nlinarith
  have hdif : |(g p).det-(gStar p).det| ≤ d0/2 := hdetdiff.trans hsmall
  linarith [(abs_le.mp hdif).1,hfloor p hp]

theorem exists_actual_determinant_floor_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ d : ℝ, 0 < d ∧ (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, 0 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ gTau : MetricField,
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            ∀ p ∈ modelSquare, d ≤ (gTau p).det := by
  obtain ⟨d,epsilon,hd,he,hstar,htol⟩ := exists_metric_value_det_tolerance hgStar hV hSV
  refine ⟨d,hd,hstar,?_⟩
  intro q0 a ha N hN delta
  obtain ⟨tau0,_,herror⟩ := exists_first_error_threshold (by positivity : 0 < 4*epsilon)
  have hehalf : 0 < epsilon/2 := by positivity
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N hN delta hehalf,
    eventually_ge_atTop tau0] with tau hpulse htau
  intro gTau happ p hp
  apply htol gTau p hp
  intro i j
  have herrorhalf : metricApproximationAccuracy tau ≤ epsilon/2 := by
    have h := herror tau htau
    linarith
  have hE : |gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j| ≤ epsilon/2 := by
    have hzero : |gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j| ≤
        metricApproximationAccuracy tau := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
        happ i j 0 (Nat.zero_le tau) p hp
    exact hzero.trans herrorhalf
  have hP : |pulseTensor q0 a N delta (tau : ℝ) p i j| ≤ epsilon/2 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hpulse.2 i j 0 le_rfl p
  have heq : gTau p i j-gStar p i j =
      (gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j)+
        pulseTensor q0 a N delta (tau : ℝ) p i j := by
    change gTau p i j-gStar p i j =
      (gTau p i j-(gStar p i j+pulseTensor q0 a N delta (tau : ℝ) p i j))+
        pulseTensor q0 a N delta (tau : ℝ) p i j
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add hE hP).trans_eq (by ring))

theorem exists_actual_low_metric_data_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) (m : ℕ) :
    ∃ G d : ℝ, 0 < G ∧ 0 < d ∧
      (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, m < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop, m ≤ tau ∧
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) := by
  obtain ⟨G,hG,hGstar,hjets⟩ := exists_low_metric_budget_before_pulse_parameters hgStar hV hSV m
  obtain ⟨d,hd,hdstar,hfloor⟩ := exists_actual_determinant_floor_before_pulse_parameters hgStar hV hSV
  refine ⟨G,d,hG,hd,hGstar,hdstar,?_⟩
  intro q0 a ha N hmN delta
  filter_upwards [hjets q0 a ha N hmN delta,hfloor q0 a ha N (by omega) delta]
    with tau hjetTau hfloorTau
  refine ⟨hjetTau.1,?_⟩
  intro gTau U hgTau hU hSU happ
  exact ⟨hjetTau.2 gTau U hgTau hU hSU happ,
    fun p hp => (hfloorTau gTau happ p hp).trans (le_abs_self _)⟩

end SmoothLocal.Pulse

end

end OAI
