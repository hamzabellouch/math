import OAI.Geometry.IsometricImmersion.Pulses.PulseActualDensity

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem exists_test_density_global_bound (B : ℝ) {d : ℝ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
      ∀ tau : ℝ, T ≤ tau → ∀ (gStar : MetricField) (q0 : ℝ) (U : Set Coord),
        SmoothPositiveOn gStar U → SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
        IsOpen U → ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
          ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B →
          d ≤ (metricInShearCoordinates gStar q0 p).det →
          |(curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
              curvatureDensity gStar (inverseShearCoordinates q0 p))-
            pulsePrincipalLeading a N delta tau p| ≤
            testDensityErrorCoefficient C a ha delta*tau/tau^N := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_actual_pulse_lower_bound B hd ha N hN
  refine ⟨C,hC,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hsmall⟩ := hbound delta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar q0 U hg htest hU p hpU hjet hdet
  have ht1 : 1 ≤ tau := hT.trans ht
  have hL := hsmall tau ht (metricInShearCoordinates gStar q0) p hjet hdet
  have hR := pulse_principal_remainder_le ha N delta ht1 p
  have heq := actual_pulse_curvature_density q0 a N delta tau hg htest hU hpU
  rw [pulse_principal_exact] at heq
  have hdensity :
      (curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-pulsePrincipalLeading a N delta tau p =
        pulsePrincipalRemainder a N delta tau p+
          thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p := by
    dsimp only [curvatureDensity]
    linarith only [heq]
  rw [hdensity]
  calc
    _ ≤ |pulsePrincipalRemainder a N delta tau p|+
        |thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p| :=
      abs_add_le _ _
    _ ≤ pulsePrincipalRemainderBound a ha*tau/tau^N+
        C*scalarPulseFirstJetBudget a ha N delta tau := add_le_add hR hL
    _ = _ := by unfold testDensityErrorCoefficient scalarPulseFirstJetBudget; ring

theorem exists_actual_density_global_bound (B Bcompare : ℝ) {d dcompare : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ Ctest Ccompare : ℝ, 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
            ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B →
            d ≤ (metricInShearCoordinates gStar q0 p).det →
            ∀ epsilon : ℝ,
              ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                (inverseShearCoordinates q0 p)‖ ≤ Bcompare →
              dcompare ≤ (testMetric gStar q0 a N delta tau
                (inverseShearCoordinates q0 p)).det →
              ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
                actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                  (inverseShearCoordinates q0 p)‖ ≤ epsilon →
              epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
              (∀ i j k l : Fin 2,
                |coordPartial i (coordPartial j (fun q => gTau q k l))
                    (inverseShearCoordinates q0 p)-
                  coordPartial i (coordPartial j
                    (fun q => testMetric gStar q0 a N delta tau q k l))
                    (inverseShearCoordinates q0 p)| ≤ epsilon) →
              |(curvatureDensity gTau (inverseShearCoordinates q0 p)-
                  curvatureDensity gStar (inverseShearCoordinates q0 p))-
                pulsePrincipalLeading a N delta tau p| ≤
                testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+
                  Ccompare*epsilon := by
  obtain ⟨Ct,hCt,htest⟩ := exists_test_density_global_bound B hd ha N hN
  obtain ⟨Cc,hCc,hcompare⟩ := exists_uniform_curvature_density_comparison Bcompare hdcompare
  refine ⟨Ct,Cc,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hglobal⟩ := htest delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU hjet hdet
    epsilon hjetTest hdetTest hdistance he1 hesmall hsecond
  have hpulse := hglobal tau ht gStar q0 U hgStar hgTest hU p hpU hjet hdet
  have hmetric := hcompare gTau (testMetric gStar q0 a N delta tau) U
    hgTau hgTest hU (inverseShearCoordinates q0 p) hpU epsilon
    hjetTest hdetTest hdistance he1 hesmall hsecond
  have heq :
      (curvatureDensity gTau (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-
          pulsePrincipalLeading a N delta tau p =
      ((curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-
          pulsePrincipalLeading a N delta tau p)+
      (curvatureDensity gTau (inverseShearCoordinates q0 p)-
        curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hpulse hmetric)

end SmoothLocal.Pulse

end

end OAI
