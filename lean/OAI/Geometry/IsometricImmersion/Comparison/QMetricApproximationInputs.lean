import OAI.Geometry.IsometricImmersion.Pulses.QPulseFirstJetBudget

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem iteratedCoordPartial_sub_actual {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun q => f q-h q) p =
      iteratedCoordPartial ds f p-iteratedCoordPartial ds h p := by
  rw [iteratedCoordPartial_eq_jet (hf.sub hh) hU ds hp]
  change iteratedFDeriv ℝ ds.length (f-h) p (coordinateDirections ds) = _
  rw [iteratedFDeriv_sub_apply (i := ds.length)
    ((hf.contDiffAt (hU.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hh.contDiffAt (hU.mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)),
    sub_apply,
    ←iteratedCoordPartial_eq_jet hf hU ds hp,←iteratedCoordPartial_eq_jet hh hU ds hp]

theorem actual_metric_word_difference_le {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) (ds : List (Fin 2)) {epsilon : ℝ}
    (hjet : ‖iteratedFDeriv ℝ ds.length (fun q => g q i j-h q i j) p‖ ≤ epsilon) :
    |iteratedCoordPartial ds (fun q => g q i j) p-
      iteratedCoordPartial ds (fun q => h q i j) p| ≤ epsilon := by
  have hb := (norm_iteratedCoordPartial_le_jet ((hg.1 i j).sub (hh.1 i j)) hU ds hp).trans hjet
  rw [iteratedCoordPartial_sub_actual (hg.1 i j) (hh.1 i j) hU ds hp,
    Real.norm_eq_abs] at hb
  exact hb

theorem actual_metric_jet_approximation_inputs {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {epsilon : ℝ}
    (hjets : ∀ i j : Fin 2, ∀ k ≤ 2,
      ‖iteratedFDeriv ℝ k (fun q => g q i j-h q i j) p‖ ≤ epsilon) :
    ‖actualCurvatureFirstInput g p-actualCurvatureFirstInput h p‖ ≤ epsilon ∧
      ∀ i j k l : Fin 2,
        |coordPartial i (coordPartial j (fun q => g q k l)) p-
          coordPartial i (coordPartial j (fun q => h q k l)) p| ≤ epsilon := by
  have he : 0 ≤ epsilon := (norm_nonneg _).trans (hjets 0 0 0 (by omega))
  have hval (i j : Fin 2) : |g p i j-h p i j| ≤ epsilon := by
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp i j []
      (hjets i j 0 (by omega))
  have hder (d i j : Fin 2) :
      |coordPartial d (fun q => g q i j) p-coordPartial d (fun q => h q i j) p| ≤ epsilon := by
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp i j [d]
      (hjets i j 1 (by omega))
  constructor
  · change max ‖(fun i j => g p i j-h p i j)‖
      ‖(fun d i j => coordPartial d (fun q => g q i j) p-
        coordPartial d (fun q => h q i j) p)‖ ≤ epsilon
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg he).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hval i j
    · apply (pi_norm_le_iff_of_nonneg he).mpr
      intro d
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg he).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hder d i j
  · intro i j k l
    simpa only [iteratedCoordPartial] using actual_metric_word_difference_le hg hh hU hp k l [i,j]
      (hjets k l 2 (by omega))

theorem actual_sheared_first_jet_error_from_Ctau
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta : ℝ} {N n : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta n) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (hN : 0 < N) (hn : 2 ≤ n) (hlarge : N-1 ≤ n)
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjets : ∀ i j : Fin 2, ∀ k ≤ n,
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j-testMetric gStar q0 a N delta n q i j)
        (inverseShearCoordinates q0 p)‖ ≤ 1/(n : ℝ)^n) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      qPulseFirstJetBudget a ha N delta n := by
  apply actual_sheared_first_jet_error_nat hgStar hgTest hgTau hU hq ha hN
    (by omega) hlarge hp
  exact (actual_metric_jet_approximation_inputs hgTau hgTest hU hp
    (fun i j k hk => hjets i j k (hk.trans hn))).1

end SmoothLocal.Pulse

end

end OAI
