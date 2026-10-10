import OAI.Geometry.IsometricImmersion.Estimates.ActualQWeightedRemainder
import OAI.Geometry.IsometricImmersion.Darboux.QSpatialJets

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem pulsePrincipalLeading_contDiff (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulsePrincipalLeading a N delta tau) := by
  unfold pulsePrincipalLeading temporalCutoff
  exact ((contDiff_const.mul ((axisBump_contDiff a).comp (contDiff_apply ℝ ℝ 0))).mul
    ((axisBump_contDiff (1/2)).comp
      ((contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const delta))).mul
      (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0)))

theorem sheared_Q_on_height_contDiffOn {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) (hSU : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ U)
    (hxx : ∀ p ∈ S, covHessian (metricInShearCoordinates g q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => sixVariableQ (metricInShearCoordinates g q0)
      (qSolutionJet (heightInShearCoordinates z q0) p)) S := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates g q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : S ⊆ V := fun p hp => hSU p hp
  apply (sixVariableQ_contDiffOn hgV hV).comp ((qSolutionJet_contDiffOn hV hzV).mono hSV)
  intro p hp
  change statePoint (qSolutionJet (heightInShearCoordinates z q0) p) ∈ V ∧
    stateQDenominator (metricInShearCoordinates g q0)
      (qSolutionJet (heightInShearCoordinates z q0) p) ≠ 0
  rw [statePoint_qSolutionJet,stateQDenominator_qSolutionJet]
  exact ⟨hSV hp,hxx p hp⟩

theorem actualShearedQLeading_contDiffOn {gStar : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn gStar U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (hSU : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ U)
    (hxx : ∀ p ∈ S, covHessian (metricInShearCoordinates gStar q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (actualShearedQLeading gStar z q0 a N delta tau) S := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : S ⊆ V := fun p hp => hSU p hp
  exact (contDiffOn_const.mul (forcingCoefficient_contDiffOn hgV hzV hV hSV hxx)).mul
    (pulsePrincipalLeading_contDiff a N delta tau).contDiffOn

theorem exists_actual_Q_moment_lower_with_remainder
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
            c3*delta*tau/tau^N-
                qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
                  (2*delta/tau)*(∫ x : ℝ, axisBump a x) ≤
              |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| := by
  obtain ⟨c3,hc3,hLead⟩ := exists_actual_leading_forcing_moment_lower ha he hc Dref Cref N
  obtain ⟨Tlead,hTlead⟩ := eventually_atTop.mp hLead
  obtain ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,hError⟩ :=
    exists_actual_Q_weighted_remainder_bound B Bcompare BQ D A hd hdcompare hc hD hA ha N hN
  refine ⟨c3,H,Cfirst,Ctest,Ccompare,hc3,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨Terror,hTerror,hErrorT⟩ := hError delta hdelta
  refine ⟨max Terror Tlead,hTerror.trans (le_max_left _ _),?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ heps hepsQ
    heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint hxxTau hE hdetup hxxup
  have htE : Terror ≤ tau := (le_max_left _ _).trans ht
  have htL : Tlead ≤ tau := (le_max_right _ _).trans ht
  have hSU : ∀ p ∈ pulseStrip a delta tau, inverseShearCoordinates q0 p ∈ U :=
    fun p hp => (hpoint p hp).point_mem
  have hxxStar : ∀ p ∈ pulseStrip a delta tau,
      covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    intro p hp hz0
    have hm := (hpoint p hp).referenceXX
    rw [hz0,abs_zero] at hm
    linarith
  have hFc : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau) :=
    ((sheared_Q_on_height_contDiffOn hgTau hz hU q0 hSU hxxTau).sub
      (sheared_Q_on_height_contDiffOn hgStar hz hU q0 hSU hxxStar)).continuousOn
  have hLc := (actualShearedQLeading_contDiffOn hgStar hz hU q0 a N delta tau hSU hxxStar).continuousOn
  have herr := hErrorT tau htE gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ
    heps hepsQ heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint
  rw [pulseWeightedMoment_sub hFc hLc] at herr
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : pulseStrip a delta tau ⊆ V := fun p hp => hSU p hp
  have hlead := hTlead tau htL delta hdelta (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) V hgV hzV hV hSV hE hdetup
    (fun p hp => (hpoint p hp).referenceXX) hxxup
  change c3*delta*tau/tau^N ≤ |pulseWeightedMoment a delta tau
    (actualShearedQLeading gStar z q0 a N delta tau)| at hlead
  have htriangle : |pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau)| ≤
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)|+
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
        pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau)| := by
    calc
      _ = |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
        (pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
          pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau))| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  linarith

end SmoothLocal.Pulse

end

end OAI
