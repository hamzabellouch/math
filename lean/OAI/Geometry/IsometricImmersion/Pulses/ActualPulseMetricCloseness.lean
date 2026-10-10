import OAI.Geometry.IsometricImmersion.Metrics.ActualLowMetricBudget
import OAI.Geometry.IsometricImmersion.Pulses.PulseEdgeReferenceDistance
import OAI.Geometry.IsometricImmersion.Calculus.ShearMetricFullJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem metric_difference_jet_le_actual_pulse_error
    {gStar gTau : MetricField} {V U : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hgTau : SmoothPositiveOn gTau U)
    (hV : IsOpen V) (hU : IsOpen U) {p : Coord} (hpV : p ∈ V) (hpU : p ∈ U)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) (k : ℕ) {P E : ℝ}
    (hpulse : ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤ P)
    (herror : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) p‖ ≤ E) :
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j-gStar q i j) p‖ ≤ P+E := by
  have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  have hbs := (hgStar.1 i j).contDiffAt (hV.mem_nhds hpV)
  have hgs := (hgTau.1 i j).contDiffAt (hU.mem_nhds hpU)
  have hts : ContDiffAt ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) p :=
    hbs.add hps.contDiffAt
  have heq : (fun q => gTau q i j-gStar q i j) =
      (fun q => gTau q i j-testMetric gStar q0 a N delta tau q i j)+
        (fun q => pulseTensor q0 a N delta tau q i j) := by
    funext q
    simp only [testMetric,Pi.add_apply,Matrix.add_apply]
    ring
  rw [heq,iteratedFDeriv_add_apply
    ((hgs.sub hts).of_le (WithTop.coe_le_coe.mpr le_top))
    (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_add_le _ _).trans ((add_le_add herror hpulse).trans_eq (add_comm E P))

theorem actual_metric_finite_reference_closeness
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (q0 a : ℝ) (ha : 0 < a) (m N : ℕ) (hmN : m < N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ m ≤ tau ∧
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
            testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
        ∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-gStar q i j) p‖ ≤ epsilon := by
  obtain ⟨tau0,_,haccuracy⟩ := exists_first_error_threshold (by positivity : 0 < 4*epsilon)
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha m N hmN delta
    (half_pos hepsilon),eventually_ge_atTop tau0,eventually_ge_atTop m] with tau hpulse htau hmtau
  refine ⟨hpulse.1,hmtau,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  have he : metricApproximationAccuracy tau ≤ epsilon/2 := by linarith [haccuracy tau htau]
  have hb := metric_difference_jet_le_actual_pulse_error hgStar hgTau hV hU
    (hSV hp) (hSU hp) q0 a N delta (tau : ℝ) i j k
    (hpulse.2 i j k hk p) ((happ i j k (hk.trans hmtau) p hp).trans he)
  exact hb.trans_eq (by ring)

theorem actual_sheared_metric_finite_reference_closeness
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {q0 a : ℝ} (hq0 : |q0| ≤ 1) (ha : 0 < a) (m N : ℕ) (hmN : m < N)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ m ≤ tau ∧
      ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
            testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
        ∀ i j : Fin 2, ∀ k ≤ m, ∀ p : Coord,
          inverseShearCoordinates q0 p ∈ modelSquare →
          ‖iteratedFDeriv ℝ k (fun q => metricInShearCoordinates gStar q0 q i j-
            metricInShearCoordinates gTau q0 q i j) p‖ ≤ epsilon := by
  let e := epsilon/(4*2^m)
  have he : 0 < e := div_pos hepsilon (by positivity)
  filter_upwards [actual_metric_finite_reference_closeness hgStar hV hSV q0 a ha m N hmN he delta]
    with tau htau
  refine ⟨htau.1,htau.2.1,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hpW : inverseShearCoordinates q0 p ∈ W := ⟨hSU hp,hSV hp⟩
  have hgW (i j : Fin 2) := (hgTau.1 i j).mono (inter_subset_left : W ⊆ U)
  have hsW (i j : Fin 2) := (hgStar.1 i j).mono (inter_subset_right : W ⊆ V)
  have herr (i j : Fin 2) :
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j-gTau q i j) (inverseShearCoordinates q0 p)‖ ≤ e := by
    have hdiff := htau.2.2 gTau U hgTau hU hSU happ i j k hk _ hp
    have heq : (fun q => gStar q i j-gTau q i j) =
        -(fun q => gTau q i j-gStar q i j) := by
      funext point
      simp only [Pi.neg_apply, neg_sub]
    rw [heq,iteratedFDeriv_neg_apply,norm_neg]
    exact hdiff
  have hshear := sheared_metric_full_jet_difference_le hsW hgW hW hq0 he.le hpW k herr i j
  apply hshear.trans
  calc
    4*2^k*e ≤ 4*2^m*e := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) (by norm_num)) he.le
    _ = epsilon := by dsimp only [e]; field_simp

end SmoothLocal.Pulse

end

end OAI
