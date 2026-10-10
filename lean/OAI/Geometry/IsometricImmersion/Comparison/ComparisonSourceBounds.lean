import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonSource
import OAI.Geometry.IsometricImmersion.Estimates.MovingSourceBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor SmoothLocal.Hyperbolic

def pulseLeadingBound (a : ℝ) (ha : 0 < a) : ℝ :=
  axisBumpDerivativeBound a ha 0*axisBumpDerivativeBound (1/2) (by norm_num) 0/2

theorem pulseLeadingBound_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ pulseLeadingBound a ha := by
  exact div_nonneg (mul_nonneg (axisBumpDerivativeBound_pos ha 0).le
    (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ)<1/2) 0).le) (by norm_num)

theorem pulsePrincipalLeading_abs_bound {a tau : ℝ} (ha : 0 < a) (ht : 0 < tau)
    (N : ℕ) (delta : ℝ) (p : Coord) :
    |pulsePrincipalLeading a N delta tau p| ≤ pulseLeadingBound a ha*tau^2/tau^N := by
  let A0 := axisBumpDerivativeBound a ha 0
  let P0 := axisBumpDerivativeBound (1/2) (by norm_num) 0
  have hA0 : 0 ≤ A0 := (axisBumpDerivativeBound_pos ha 0).le
  have hP0 : 0 ≤ P0 := (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ)<1/2) 0).le
  have haxis : |axisBump a (p 0)| ≤ A0 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using axisBump_derivative_le ha 0 (p 0)
  have htemp : |temporalCutoff (tau*p 1/delta)| ≤ P0 := by
    simpa only [temporalCutoff,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
      axisBump_derivative_le (by norm_num : (0 : ℝ)<1/2) 0 (tau*p 1/delta)
  have hq : 0 ≤ tau^2/(2*tau^N) := by positivity
  calc
    _ = (tau^2/(2*tau^N))*|axisBump a (p 0)| *
        |temporalCutoff (tau*p 1/delta)| *|Real.cos (tau*p 0)| := by
      rw [pulsePrincipalLeading,abs_mul,abs_mul,abs_mul,abs_of_nonneg hq]
    _ ≤ (tau^2/(2*tau^N))*A0*P0*1 :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left haxis hq) htemp (abs_nonneg _)
        (mul_nonneg hq hA0)) (Real.abs_cos_le_one _) (abs_nonneg _)
        (mul_nonneg (mul_nonneg hq hA0) hP0)
    _ = _ := by dsimp [pulseLeadingBound,A0,P0]; field_simp [ht.ne']

def comparisonSourceBudget (A Cfirst Ctest Ccompare Cres a : ℝ) (ha : 0 < a)
    (N : ℕ) (delta tau epsilon epsilonQ : ℝ) : ℝ :=
  2*A*(pulseLeadingBound a ha*tau^2/tau^N)+
    qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ+Cres/tau^N

theorem comparisonSourceBudget_nonneg {A Cfirst Ctest Ccompare Cres a : ℝ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare)
    (hCr : 0 ≤ Cres) (N : ℕ) (delta : ℝ) {tau epsilon epsilonQ : ℝ}
    (ht : 0 ≤ tau) (he : 0 ≤ epsilon) (heQ : 0 ≤ epsilonQ) :
    0 ≤ comparisonSourceBudget A Cfirst Ctest Ccompare Cres a ha N delta tau epsilon epsilonQ := by
  have hrem := qForcingRemainderBudget_nonneg ha hA hCf hCt hCc N delta ht he heQ
  have hlead := pulseLeadingBound_nonneg ha
  unfold comparisonSourceBudget
  positivity

theorem exists_actual_comparison_source_pointwise_bound
    (B Bcompare BQ D A Cres : ℝ)
    {d dcompare c : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ H Cfirst Ctest Ccompare : ℝ,
      0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U → SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ (z P : Coord → ℝ), ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            ∀ p : Coord,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p →
              |qResidual (metricInShearCoordinates gStar q0) P p| ≤ Cres/tau^N →
              |actualComparisonSource gStar gTau z q0 P p| ≤
                comparisonSourceBudget A Cfirst Ctest Ccompare Cres a ha N delta tau epsilon epsilonQ := by
  obtain ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,hglobal⟩ :=
    exists_actual_Q_pulse_forcing_bound_global B Bcompare BQ D A hd hdcompare hc hD hA ha N hN
  refine ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelt
  obtain ⟨T,hT,hglobalT⟩ := hglobal delta hdelt
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z P hz epsilon epsilonQ
    he1 hesmall heQ1 heQsmall hxxsmall p hpoint hres
  have htpos : 0 < tau := zero_lt_one.trans_le (hT.trans ht)
  have herr := hglobalT tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpoint.point_mem z hz
    epsilon epsilonQ hpoint.referenceFirst hpoint.referenceDet hpoint.testFirst hpoint.testDet
    hpoint.approximationFirst he1 hesmall hpoint.approximationSecond hpoint.referenceState
    hpoint.referenceXX hpoint.baseFirstDistance heQ1 heQsmall hxxsmall
    hpoint.actualDensity hpoint.referenceCoefficient
  have hlead : |actualShearedQLeading gStar z q0 a N delta tau p| ≤
      2*A*(pulseLeadingBound a ha*tau^2/tau^N) := by
    rw [actualShearedQLeading,abs_mul,abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpoint.referenceCoefficient (by norm_num))
      (pulsePrincipalLeading_abs_bound ha htpos N delta p) (abs_nonneg _) (by positivity)
  have hforce : |actualShearedQForcing gStar gTau z q0 p| ≤
      2*A*(pulseLeadingBound a ha*tau^2/tau^N)+
        qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ := by
    have htri : |actualShearedQForcing gStar gTau z q0 p| ≤
        |actualShearedQLeading gStar z q0 a N delta tau p|+
          |actualShearedQForcing gStar gTau z q0 p-actualShearedQLeading gStar z q0 a N delta tau p| := by
      have he : actualShearedQLeading gStar z q0 a N delta tau p+
          (actualShearedQForcing gStar gTau z q0 p-actualShearedQLeading gStar z q0 a N delta tau p) =
          actualShearedQForcing gStar gTau z q0 p := by ring
      simpa only [he] using abs_add_le (actualShearedQLeading gStar z q0 a N delta tau p)
        (actualShearedQForcing gStar gTau z q0 p-actualShearedQLeading gStar z q0 a N delta tau p)
    exact htri.trans (add_le_add hlead herr)
  exact (abs_sub _ _).trans (add_le_add hforce hres)

end SmoothLocal.Pulse

end

end OAI
