import OAI.Geometry.IsometricImmersion.Pulses.PulseOperatorMoment
import OAI.Geometry.IsometricImmersion.Comparison.ComparisonCoefficientSmooth
import OAI.Geometry.IsometricImmersion.Darboux.QContainingRectangle

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem actual_comparison_tested_source {g gRef : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det=gaussianCurvature g p*heightEnergy g z p)
    (hxx : covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef U) :
    sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p =
      testedOperatorSource (comparisonCoefficient gRef P z 4) (comparisonCoefficient gRef P z 5)
        (comparisonCoefficient gRef P z 3) (comparisonCoefficient gRef P z 2) (comparisonDifference P z) p := by
  have hh := comparison_equation_from_darboux hg hgRef hU hz hP hp hD hxx hseg
  unfold testedOperatorSource
  linarith

theorem actual_comparison_source_test_cost {a delta tau K K1 M B : ℝ} {N : ℕ}
    {g gRef : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hK : 0 ≤ K) (hK1 : 0 ≤ K1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hg : SmoothPositiveOn g U) (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) (hSU : pulseStrip a delta tau ⊆ U)
    (hD : ∀ p ∈ pulseStrip a delta tau,
      (covHessian g z p).det=gaussianCurvature g p*heightEnergy g z p)
    (hxx : ∀ p ∈ pulseStrip a delta tau, covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ p ∈ pulseStrip a delta tau, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef U)
    (hcoeff : ∀ i : Fin 6, ∀ p ∈ pulseStrip a delta tau, |comparisonCoefficient gRef P z i p| ≤ K)
    (hderiv : ∀ i : Fin 6, ∀ p ∈ pulseStrip a delta tau,
      |coordPartial 0 (comparisonCoefficient gRef P z i) p| ≤ K1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau), ∀ i : Fin 2,
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i (comparisonDifference P z) (boxPoint x theta))^2) ≤
        M*delta*tau/tau^N)
    (hinitial : ∀ x ∈ Icc (-a) a,
      coordPartial 1 (comparisonDifference P z) (boxPoint x (-(delta/tau)))=0)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity (comparisonDifference P z) (delta/tau)) x‖ ≤ B) :
    |pulseWeightedMoment a delta tau
      (fun p => sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N+
      (4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
      (4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hab : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  obtain ⟨W,hW,hSW,hWU,_,hcoeffSmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRef hU hP hz (closedRectangle_compact _ _ _ _) hSU hseg
  obtain ⟨radius,lo,hi,hRad,hlo,hhi,hRect⟩ := exists_containing_coordinateRectangle hW ha hab hSW
  have hI : IsOpen (Ioo (-radius) radius) := isOpen_Ioo
  have hsub : Icc (-a) a ⊆ Ioo (-radius) radius := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hupper (x : ℝ) (hx : x ∈ Ioo (-radius) radius) : (![x,delta/tau] : Coord) ∈ W := by
    apply hRect
    exact ⟨hx,⟨hlo.trans_le hab,hhi⟩⟩
  have hv : ContDiffOn ℝ ∞ (comparisonDifference P z) W := (hz.sub hP).mono hWU
  have hcost := testedOperatorSource_moment_cost ha hd ht hK hK1 hM hB
    (hcoeffSmooth 4) (hcoeffSmooth 5) (hcoeffSmooth 3) (hcoeffSmooth 2) hv hW hSW
    (fun p hp => ⟨hcoeff 4 p hp,hcoeff 5 p hp,hcoeff 3 p hp,hcoeff 2 p hp⟩)
    (fun p hp => ⟨hderiv 4 p hp,hderiv 5 p hp⟩) hL2 hI hsub hupper hinitial hjet
  have heq : pulseWeightedMoment a delta tau
      (fun p => sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p) =
      pulseWeightedMoment a delta tau
        (testedOperatorSource (comparisonCoefficient gRef P z 4) (comparisonCoefficient gRef P z 5)
          (comparisonCoefficient gRef P z 3) (comparisonCoefficient gRef P z 2) (comparisonDifference P z)) := by
    apply setIntegral_congr_fun (pulsePairRectangle_isCompact a delta tau).measurableSet
    intro q hq
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    rw [actual_comparison_tested_source hg hgRef hU hz hP (hSU (pulsePairPoint_mem hq))
      (hD _ (pulsePairPoint_mem hq)) (hxx _ (pulsePairPoint_mem hq)) (hseg _ (pulsePairPoint_mem hq))]
  rw [heq]
  exact hcost

end SmoothLocal.HighEquation

end

end OAI
