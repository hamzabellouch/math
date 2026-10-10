import OAI.Geometry.IsometricImmersion.Pulses.PulseNeighborhood
import OAI.Geometry.IsometricImmersion.Metrics.MetricPatchOpen

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem exists_pulse_spatial_radius (q0 : ℝ) {L r0 : ℝ} (hL : 0 < L) (hr0 : 0 < r0) :
    ∃ r : ℝ, 0 < r ∧ r < r0 ∧ r < 1/2 ∧
      0 < L*r/16 ∧ L*r/16 ≤ 1/10 ∧ |q0| *(L*r/16) < 1/10 := by
  let r : ℝ := min (r0/2) (min (1/4) (1/(L*(1+|q0|))))
  have hden : 0 < L*(1+|q0|) := mul_pos hL (by positivity)
  have hr : 0 < r := lt_min (by positivity) (lt_min (by norm_num) (one_div_pos.mpr hden))
  have hrA : r ≤ r0/2 := min_le_left _ _
  have hrB : r ≤ (1 : ℝ)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hrC : r ≤ 1/(L*(1+|q0|)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : L*r*(1+|q0|) ≤ 1 := by
    have hh := (le_div_iff₀ hden).mp hrC
    nlinarith only [hh]
  have hLr : 0 < L*r := mul_pos hL hr
  have hqLr : 0 ≤ |q0| *(L*r) := mul_nonneg (abs_nonneg _) hLr.le
  have haxis : L*r/16 ≤ (1 : ℝ)/16 := by nlinarith [hprod, hqLr]
  have hshear : |q0| *(L*r/16) ≤ (1 : ℝ)/16 := by nlinarith [hprod, hLr]
  refine ⟨r, hr, ?_, ?_, div_pos hLr (by norm_num), ?_, ?_⟩
  · linarith [hrA]
  · linarith [hrB]
  · exact haxis.trans (by norm_num)
  · exact hshear.trans_lt (by norm_num)

theorem exists_N_before_delta_eventually_integer_testMetric (g0 : MetricField)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ ∈ O, perturbedMetric g0 θ =
          testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ) := by
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_testMetric g0 hO hη q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (hmem delta hd)

theorem exists_N_before_delta_eventually_positive_testMetric
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation}
    (hη : η ∈ O) (hηmetric : η ∈ metricPatchSet g0 kappa)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ : SymmetricPerturbation, θ ∈ O ∧ θ ∈ metricPatchSet g0 kappa ∧
          perturbedMetric g0 θ = testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ) ∧
          SmoothPositiveOn (testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ)) U ∧
          ∀ p ∈ centralBox,
            gaussianCurvature (testMetric (perturbedMetric g0 η) q0 a N delta (tau : ℝ)) p < -kappa/2 := by
  have hOmetric : IsOpen (O ∩ metricPatchSet g0 kappa) :=
    hO.inter (metricPatchSet_isOpen hg0 hU hSU kappa)
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_integer_testMetric g0
    hOmetric ⟨hη, hηmetric⟩ q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨θ, hθ, heq⟩ := ht.2
  have hpositive : SmoothPositiveOn (perturbedMetric g0 θ) U :=
    perturbedMetric_smoothPositiveOn hg0 θ hθ.2.1
  have hcentral : ∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 θ) p < -kappa/2 := hθ.2.2
  refine ⟨ht.1, θ, hθ.1, hθ.2, heq, ?_, ?_⟩
  · rwa [← heq]
  · rwa [← heq]

theorem exists_N_before_delta_eventually_relative_metric_neighborhood
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {η : metricPatchSet g0 kappa} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1/10) (hq : |q0| *a < 1/10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
        ∃ θ : metricPatchSet g0 kappa, θ ∈ O ∧
          perturbedMetric g0 θ.val = testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ) ∧
          SmoothPositiveOn (testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ)) U ∧
          ∀ p ∈ centralBox,
            gaussianCurvature (testMetric (perturbedMetric g0 η.val) q0 a N delta (tau : ℝ)) p < -kappa/2 := by
  have hOa : IsOpen (Subtype.val '' O : Set SymmetricPerturbation) :=
    (metricPatchSet_isOpen hg0 hU hSU kappa).isOpenMap_subtype_val O hO
  have hηa : η.val ∈ (Subtype.val '' O : Set SymmetricPerturbation) := ⟨η, hη, rfl⟩
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_positive_testMetric hg0 hU hSU
    hOa hηa η.property q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨θ, hθO, hθmetric, heq, hpositive, hcentral⟩ := ht.2
  obtain ⟨θ', hθ', hvalue⟩ := hθO
  refine ⟨ht.1, θ', hθ', ?_, hpositive, hcentral⟩
  simpa only [hvalue] using heq

end SmoothLocal.Pulse

end

end OAI
