import OAI.Geometry.IsometricImmersion.Darboux.QMomentAbsorption

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise
namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_moment_positive_lower
    (B Bcompare BQ D A Dref Cref : ℝ) {d dcompare c e : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c) (he : 0 < e)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ c3 H Cfirst Ctest Ccompare : ℝ,
      0 < c3 ∧ 0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, 0 ≤ epsilon → 0 ≤ epsilonQ →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            epsilon ≤ tau/tau^N → epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau →
            (∀ p ∈ pulseStrip a delta tau,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p) →
            (∀ p ∈ pulseStrip a delta tau,
              covHessian (metricInShearCoordinates gTau q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0) →
            (∀ p ∈ pulseStrip a delta tau,
              e ≤ heightEnergy (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p) →
            (∀ p ∈ pulseStrip a delta tau, (metricInShearCoordinates gStar q0 p).det ≤ Dref) →
            (∀ p ∈ pulseStrip a delta tau,
              |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0| ≤ Cref) →
            c3*delta*tau/tau^N ≤
              |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| := by
  obtain ⟨c3,H,Cfirst,Ctest,Ccompare,hc3,hH,hCf,hCt,hCc,hbase⟩ :=
    exists_actual_Q_moment_lower_with_remainder B Bcompare BQ D A Dref Cref
      hd hdcompare hc he hD hA ha N hN
  refine ⟨c3/2,H,Cfirst,Ctest,Ccompare,half_pos hc3,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨Tbase,hTbase,hbaseT⟩ := hbase delta hdelta
  obtain ⟨Tabs,_,habs⟩ := qMoment_budget_absorption_threshold ha hc3 hA hCf hCt hCc N delta hdelta.le
  refine ⟨max Tbase Tabs,hTbase.trans (le_max_left _ _),?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ heps hepsQ
    heps1 hesmall hepsQ1 hepsQsmall hxxsmall heScale heQScale hpoint hxxTau hE hdetup hxxup
  have hbase' := hbaseT tau ((le_max_left _ _).trans ht) gStar gTau q0 U hgStar hgTest hgTau hU z hz
    epsilon epsilonQ heps hepsQ heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint hxxTau hE hdetup hxxup
  have habs' := habs tau ((le_max_right _ _).trans ht) epsilon epsilonQ heScale heQScale
  have hhalf : (c3/2)*delta*tau/tau^N = (c3*delta*tau/tau^N)/2 := by ring
  rw [hhalf] at habs' ⊢
  linarith

end SmoothLocal.Pulse

end

end OAI
