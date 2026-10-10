import OAI.Geometry.IsometricImmersion.Pulses.PulseFirstJetControl
import OAI.Geometry.IsometricImmersion.Pulses.PulseSecondXi

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def curvatureDensity (g : MetricField) (p : Coord) : ℝ :=
  gaussianCurvature g p*(g p).det

def curvatureDensityJetError (g h : MetricField) (p : Coord) : ℝ :=
  (coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
    coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p) -
  ((coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
      coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p) +
    (coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
      coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p))/2 +
  curvatureLowerTerm g p-curvatureLowerTerm h p

theorem curvatureDensityJetError_eq {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    curvatureDensityJetError g h p = curvatureDensity g p-curvatureDensity h p := by
  unfold curvatureDensity curvatureDensityJetError
  rw [gaussianCurvature_density_principal_part hg hU hp,
    gaussianCurvature_density_principal_part hh hU hp]
  ring

theorem curvatureDensityJetError_le (g h : MetricField) (p : Coord) {e : ℝ}
    (hxy : |coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
      coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p| ≤ e)
    (hxx : |coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
      coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p| ≤ e)
    (hyy : |coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
      coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p| ≤ e) :
    |curvatureDensityJetError g h p| ≤ 2*e+|curvatureLowerTerm g p-curvatureLowerTerm h p| := by
  let x := coordPartial 0 (coordPartial 1 (fun q => g q 0 1)) p-
    coordPartial 0 (coordPartial 1 (fun q => h q 0 1)) p
  let y := coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p-
    coordPartial 0 (coordPartial 0 (fun q => h q 1 1)) p
  let z := coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p-
    coordPartial 1 (coordPartial 1 (fun q => h q 0 0)) p
  have hmain : |x-(y+z)/2| ≤ 2*e := by
    calc
      _ ≤ |x|+|(y+z)/2| := abs_sub _ _
      _ = |x|+|y+z|/2 := by rw [abs_div]; norm_num
      _ ≤ e+(e+e)/2 := add_le_add hxy
        (div_le_div_of_nonneg_right ((abs_add_le y z).trans (add_le_add hxx hyy)) (by norm_num))
      _ = 2*e := by ring
  have heq : curvatureDensityJetError g h p =
      (x-(y+z)/2)+(curvatureLowerTerm g p-curvatureLowerTerm h p) := by
    dsimp only [curvatureDensityJetError,x,y,z]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmain le_rfl)

def testDensityErrorCoefficient (C a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  pulsePrincipalRemainderBound a ha+C*scalarPulseFirstJetBound a ha delta

theorem exists_test_density_slab_bound (B : ℝ) {d : ℝ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
      ∀ tau : ℝ, T ≤ tau → ∀ (gStar : MetricField) (q0 : ℝ) (U : Set Coord),
        SmoothPositiveOn gStar U → SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
        IsOpen U → ∀ p ∈ pulseLocalBox a delta tau,
          inverseShearCoordinates q0 p ∈ U →
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
  intro tau ht gStar q0 U hg htest hU p hp hpU hjet hdet
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

theorem perturbed_density_slab_with_comparison
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta tau A : ℝ} {N : ℕ} {p : Coord}
    (hgTau : SmoothPositiveOn gTau U)
    (htest : SmoothPositiveOn (testMetric gStar q0 a N delta tau) U)
    (hU : IsOpen U) (hp : inverseShearCoordinates q0 p ∈ U)
    (htestBound :
      |(curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-pulsePrincipalLeading a N delta tau p| ≤ A) :
    |(curvatureDensity gTau (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-pulsePrincipalLeading a N delta tau p| ≤
      |curvatureDensityJetError gTau (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)|+A := by
  rw [curvatureDensityJetError_eq hgTau htest hU hp]
  have heq : (curvatureDensity gTau (inverseShearCoordinates q0 p)-
      curvatureDensity gStar (inverseShearCoordinates q0 p))-pulsePrincipalLeading a N delta tau p =
      (curvatureDensity gTau (inverseShearCoordinates q0 p)-
        curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p))+
      ((curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-pulsePrincipalLeading a N delta tau p) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add le_rfl htestBound)

end SmoothLocal.Pulse

end

end OAI
