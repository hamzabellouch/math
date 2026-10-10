import OAI.Geometry.IsometricImmersion.Comparison.FiniteApproximationJets
import OAI.Geometry.IsometricImmersion.Pulses.PulseDerivativeBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem pulseTensor_coeff_derivative_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (i j : Fin 2) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤
      pulseDerivativeBound q0 a ha delta k*tau^k/tau^N := by
  let L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ := metricCoefficientCLM i j
  have h := L.norm_iteratedFDeriv_comp_left (pulseTensor_contDiff q0 a N delta tau).contDiffAt
    (WithTop.coe_le_coe.mpr le_top) (n := k) (x := p)
  change ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤
    ‖L‖*‖iteratedFDeriv ℝ k (pulseTensor q0 a N delta tau) p‖ at h
  exact h.trans ((mul_le_mul_of_nonneg_right (metricCoefficientCLM_norm_le i j)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      pulseTensor_derivative_le q0 a ha N delta ht k p))

theorem pulseTensor_finite_coeff_jets_eventually_small
    (q0 a : ℝ) (ha : 0 < a) (m N : ℕ) (hmN : m < N) (delta : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧ ∀ i j : Fin 2, ∀ k ≤ m, ∀ p : Coord,
      ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j) p‖ ≤ epsilon := by
  have heach (k : Fin (m+1)) : ∀ᶠ tau : ℕ in atTop,
      pulseDerivativeBound q0 a ha delta k.val*(tau : ℝ)^k.val/(tau : ℝ)^N < epsilon :=
    ((fixed_order_pulse_bound_tendsto_zero q0 a ha delta N k.val (by omega)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop)).eventually
        (eventually_lt_nhds hepsilon)
  have hall : ∀ᶠ tau : ℕ in atTop, ∀ k : Fin (m+1),
      pulseDerivativeBound q0 a ha delta k.val*(tau : ℝ)^k.val/(tau : ℝ)^N < epsilon :=
    Filter.eventually_all.mpr heach
  filter_upwards [eventually_ge_atTop 1,hall] with tau htau hbound
  refine ⟨htau,?_⟩
  intro i j k hk p
  have hkBound := hbound ⟨k,by omega⟩
  change pulseDerivativeBound q0 a ha delta k*(tau : ℝ)^k/(tau : ℝ)^N < epsilon at hkBound
  exact (pulseTensor_coeff_derivative_le q0 a ha N delta (by exact_mod_cast htau) i j k p).trans
    hkBound.le

theorem metric_jet_norm_le_from_actual_pulse_approximation
    {gStar gTau : MetricField} {V U : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hgTau : SmoothPositiveOn gTau U)
    (hV : IsOpen V) (hU : IsOpen U) {p : Coord} (hpV : p ∈ V) (hpU : p ∈ U)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) (k : ℕ) {B P E : ℝ}
    (hbase : ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ B)
    (hpulse : ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤ P)
    (herror : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) p‖ ≤ E) :
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ B+P+E := by
  have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  have hbs := (hgStar.1 i j).contDiffAt (hV.mem_nhds hpV)
  have hgs := (hgTau.1 i j).contDiffAt (hU.mem_nhds hpU)
  have hts : ContDiffAt ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) p :=
    hbs.add hps.contDiffAt
  have hsplit := iteratedFDeriv_add_apply (i := k)
    (hbs.of_le (WithTop.coe_le_coe.mpr le_top))
    (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  have htest : ‖iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p‖ ≤ B+P := by
    change ‖iteratedFDeriv ℝ k ((fun q => gStar q i j)+
      (fun q => pulseTensor q0 a N delta tau q i j)) p‖ ≤ _
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hbase hpulse)
  have hsub := iteratedFDeriv_sub_apply (i := k)
    (hgs.of_le (WithTop.coe_le_coe.mpr le_top))
    (hts.of_le (WithTop.coe_le_coe.mpr le_top))
  change ‖iteratedFDeriv ℝ k ((fun q => gTau q i j)-
    (fun q => testMetric gStar q0 a N delta tau q i j)) p‖ ≤ E at herror
  rw [hsub] at herror
  calc
    _ = ‖(iteratedFDeriv ℝ k (fun q => gTau q i j) p-
          iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p)+
          iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p‖ := by
            rw [sub_add_cancel]
    _ ≤ E+(B+P) := (norm_add_le _ _).trans (add_le_add herror htest)
    _ = B+P+E := by ring

theorem exists_low_metric_budget_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) (m : ℕ) :
    ∃ G : ℝ, 0 < G ∧
      (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, m < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop, m ≤ tau ∧
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            ∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G := by
  obtain ⟨B,hB,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  refine ⟨B+2,by linarith,?_,?_⟩
  · intro i j k hk p hp
    exact (hbase i j k hk p hp).trans (by linarith)
  intro q0 a ha N hmN delta
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha m N hmN delta
    (by norm_num : (0 : ℝ)<1),eventually_ge_atTop m] with tau hsmall hmtau
  refine ⟨hmtau,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  have hb := metric_jet_norm_le_from_actual_pulse_approximation hgStar hgTau hV hU
    (hSV hp) (hSU hp) q0 a N delta (tau : ℝ) i j k (hbase i j k hk p hp)
      (hsmall.2 i j k hk p) (happ i j k (hk.trans hmtau) p hp)
  exact hb.trans (by linarith [metricApproximationAccuracy_le_one hsmall.1])

end SmoothLocal.Pulse

end

end OAI
