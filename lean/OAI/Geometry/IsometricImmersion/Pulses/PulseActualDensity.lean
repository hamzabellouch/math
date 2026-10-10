import OAI.Geometry.IsometricImmersion.Comparison.CurvatureComparisonControl

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem exists_actual_density_slab_bound (B Bcompare : ℝ) {d dcompare : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ Ctest Ccompare : ℝ, 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ p ∈ pulseLocalBox a delta tau,
            inverseShearCoordinates q0 p ∈ U →
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
  obtain ⟨Ct,hCt,htest⟩ := exists_test_density_slab_bound B hd ha N hN
  obtain ⟨Cc,hCc,hcompare⟩ := exists_uniform_curvature_density_comparison Bcompare hdcompare
  refine ⟨Ct,Cc,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hslab⟩ := htest delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hp hpU hjet hdet
    epsilon hjetTest hdetTest hdistance he1 hesmall hsecond
  have hpulse := hslab tau ht gStar q0 U hgStar hgTest hU p hp hpU hjet hdet
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

theorem approximation_budget_le_pulse_error {N n : ℕ}
    (hN : 0 < N) (hn : 1 ≤ n) (hlarge : N-1 ≤ n) :
    1/(n : ℝ)^n ≤ (n : ℝ)/(n : ℝ)^N := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  calc
    _ ≤ 1/(n : ℝ)^(N-1) :=
      one_div_le_one_div_of_le (pow_pos hn0 _) (pow_le_pow_right₀ hn1 hlarge)
    _ = (n : ℝ)/(n : ℝ)^N := by
      have hN' : N = (N-1)+1 := by omega
      conv_rhs => rw [hN',pow_add,pow_one]
      field_simp [hn0.ne']

end SmoothLocal.Pulse

end

end OAI
