import OAI.Geometry.IsometricImmersion.Pulses.ActualQPulseForcing
import OAI.Geometry.IsometricImmersion.Pulses.PulseDensityGlobal

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise
namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_pulse_forcing_bound_global (B Bcompare BQ D A : ℝ)
    {d dcompare c : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ H Cfirst Ctest Ccompare : ℝ,
      0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          let gs := metricInShearCoordinates gStar q0
          let gt := metricInShearCoordinates gTau q0
          let zs := heightInShearCoordinates z q0
          ∀ epsilon epsilonQ : ℝ,
            ‖actualCurvatureFirstInput gs p‖ ≤ B → d ≤ (gs p).det →
            ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
              (inverseShearCoordinates q0 p)‖ ≤ Bcompare →
            dcompare ≤ (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det →
            ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
              actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                (inverseShearCoordinates q0 p)‖ ≤ epsilon →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            (∀ i j k l : Fin 2,
              |coordPartial i (coordPartial j (fun q => gTau q k l)) (inverseShearCoordinates q0 p)-
                coordPartial i (coordPartial j (fun q => testMetric gStar q0 a N delta tau q k l))
                  (inverseShearCoordinates q0 p)| ≤ epsilon) →
            ‖qFirstBundle gs (qSolutionJet zs p)‖ ≤ BQ →
            c ≤ |covHessian gs zs p 0 0| →
            ‖actualCurvatureFirstInput gt p-actualCurvatureFirstInput gs p‖ ≤ epsilonQ →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            |curvatureDensity gTau (inverseShearCoordinates q0 p)| ≤ D →
            |forcingCoefficient gs zs p| ≤ A →
            |(sixVariableQ gt (qSolutionJet zs p)-sixVariableQ gs (qSolutionJet zs p))-
                2*forcingCoefficient gs zs p*pulsePrincipalLeading a N delta tau p| ≤
              2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*epsilon)+
                Cfirst*epsilonQ := by
  obtain ⟨H,Cfirst,hH,hCfirst,hQ⟩ := exists_actual_Q_forcing_error_bound BQ D A hD hA hd hc
  obtain ⟨Ctest,Ccompare,hCt,hCc,hDensity⟩ :=
    exists_actual_density_global_bound B Bcompare hd hdcompare ha N hN
  refine ⟨H,Cfirst,Ctest,Ccompare,hH,hCfirst,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hDensityT⟩ := hDensity delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU z hz
  dsimp only
  intro epsilon epsilonQ hB hdet hBcompare hdetcompare hdist he1 hsmall hsecond
    hBQ hxx hdistQ heQ1 hsmallQ hxxsmall hdensity hforce
  have hactualDensity := hDensityT tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU
    hB hdet epsilon hBcompare hdetcompare hdist he1 hsmall hsecond
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hpV : p ∈ V := hpU
  have hgSV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hgTV : SmoothPositiveOn (metricInShearCoordinates gTau q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgTau 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hdensityQ : |curvatureDensity (metricInShearCoordinates gTau q0) p| ≤ D := by
    rw [curvatureDensity_in_shear_coordinates hgTau hU q0 hpU]
    exact hdensity
  have hQactual := hQ (metricInShearCoordinates gTau q0) (metricInShearCoordinates gStar q0)
    V hgTV hgSV hV (heightInShearCoordinates z q0) p hpV epsilonQ
    (pulsePrincipalLeading a N delta tau p) hBQ hdet hxx hdistQ heQ1 hsmallQ hxxsmall
    hdensityQ hforce
  rw [curvatureDensity_in_shear_coordinates hgTau hU q0 hpU,
    curvatureDensity_in_shear_coordinates hgStar hU q0 hpU] at hQactual
  exact hQactual.trans (add_le_add
    (mul_le_mul_of_nonneg_left hactualDensity (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)) le_rfl)

end SmoothLocal.Pulse

end

end OAI
