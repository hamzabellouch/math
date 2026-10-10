import OAI.Geometry.IsometricImmersion.Pulses.ActualQPulseForcingGlobal
import OAI.Geometry.IsometricImmersion.Pulses.PulseMomentError

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

structure QPulsePointBounds (gStar gTau : MetricField) (z : Coord → ℝ)
    (U : Set Coord) (q0 a delta tau : ℝ) (N : ℕ)
    (B Bcompare BQ D A d dcompare c epsilon epsilonQ : ℝ) (p : Coord) : Prop where
  point_mem : inverseShearCoordinates q0 p ∈ U
  referenceFirst : ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B
  referenceDet : d ≤ (metricInShearCoordinates gStar q0 p).det
  testFirst : ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
    (inverseShearCoordinates q0 p)‖ ≤ Bcompare
  testDet : dcompare ≤ (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det
  approximationFirst : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
    actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
      (inverseShearCoordinates q0 p)‖ ≤ epsilon
  approximationSecond : ∀ i j k l : Fin 2,
    |coordPartial i (coordPartial j (fun q => gTau q k l)) (inverseShearCoordinates q0 p)-
      coordPartial i (coordPartial j (fun q => testMetric gStar q0 a N delta tau q k l))
        (inverseShearCoordinates q0 p)| ≤ epsilon
  referenceState : ‖qFirstBundle (metricInShearCoordinates gStar q0)
    (qSolutionJet (heightInShearCoordinates z q0) p)‖ ≤ BQ
  referenceXX : c ≤ |covHessian (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) p 0 0|
  baseFirstDistance : ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
    actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ epsilonQ
  actualDensity : |curvatureDensity gTau (inverseShearCoordinates q0 p)| ≤ D
  referenceCoefficient : |forcingCoefficient (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) p| ≤ A

def actualShearedQForcing (gStar gTau : MetricField) (z : Coord → ℝ) (q0 : ℝ) (p : Coord) : ℝ :=
  sixVariableQ (metricInShearCoordinates gTau q0) (qSolutionJet (heightInShearCoordinates z q0) p)-
    sixVariableQ (metricInShearCoordinates gStar q0) (qSolutionJet (heightInShearCoordinates z q0) p)

def actualShearedQLeading (gStar : MetricField) (z : Coord → ℝ)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  2*forcingCoefficient (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p*
    pulsePrincipalLeading a N delta tau p

def qForcingRemainderBudget (A Cfirst Ctest Ccompare a : ℝ) (ha : 0 < a)
    (N : ℕ) (delta tau epsilon epsilonQ : ℝ) : ℝ :=
  2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*epsilon)+Cfirst*epsilonQ

theorem qForcingRemainderBudget_nonneg {A Cfirst Ctest Ccompare a : ℝ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare)
    (N : ℕ) (delta : ℝ) {tau epsilon epsilonQ : ℝ}
    (ht : 0 ≤ tau) (he : 0 ≤ epsilon) (heQ : 0 ≤ epsilonQ) :
    0 ≤ qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ := by
  have hCd : 0 ≤ testDensityErrorCoefficient Ctest a ha delta :=
    add_nonneg (pulsePrincipalRemainderBound_nonneg a ha)
      (mul_nonneg hCt (scalarPulseFirstJetBound_nonneg ha delta))
  unfold qForcingRemainderBudget
  positivity

theorem exists_actual_Q_weighted_remainder_bound (B Bcompare BQ D A : ℝ)
    {d dcompare c : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ H Cfirst Ctest Ccompare : ℝ,
      0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
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
            |pulseWeightedMoment a delta tau (fun p => actualShearedQForcing gStar gTau z q0 p-
              actualShearedQLeading gStar z q0 a N delta tau p)| ≤
              qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
                (2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  obtain ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,hglobal⟩ :=
    exists_actual_Q_pulse_forcing_bound_global B Bcompare BQ D A hd hdcompare hc hD hA ha N hN
  refine ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hglobalT⟩ := hglobal delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ he heQ
    he1 hesmall heQ1 heQsmall hxxsmall hpoint
  have htpos : 0 < tau := zero_lt_one.trans_le (hT.trans ht)
  apply pulseWeightedMoment_bound ha hdelta.le htpos
    (qForcingRemainderBudget_nonneg ha hA hCf hCt hCc N delta htpos.le he heQ)
  intro p hp
  have h := hpoint p hp
  exact hglobalT tau ht gStar gTau q0 U hgStar hgTest hgTau hU p h.point_mem z hz epsilon epsilonQ
    h.referenceFirst h.referenceDet h.testFirst h.testDet h.approximationFirst he1 hesmall
    h.approximationSecond h.referenceState h.referenceXX h.baseFirstDistance heQ1 heQsmall hxxsmall
    h.actualDensity h.referenceCoefficient

end SmoothLocal.Pulse

end

end OAI
