import OAI.Geometry.IsometricImmersion.Darboux.QSegmentMargins
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.BigOperators.Pi

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def averagedQCoefficient (g : MetricField) (w0 w1 : DarbouxState) (i : Fin 6) : ℝ :=
  ∫ sigma in (0 : ℝ)..1, qFirstCoefficient g i (stateSegment w0 w1 sigma)

theorem sixVariableQ_fderiv_apply (g : MetricField) (w v : DarbouxState) :
    fderiv ℝ (sixVariableQ g) w v = ∑ i, qFirstCoefficient g i w * v i := by
  calc
    _ = fderiv ℝ (sixVariableQ g) w (∑ i, v i • Pi.single i 1) :=
      congrArg (fderiv ℝ (sixVariableQ g) w) (pi_eq_sum_univ' v)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, qFirstCoefficient, mul_comm]

theorem qCoefficient_segment_continuousOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContinuousOn (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) (Icc (0 : ℝ) 1) :=
  (qFirstCoefficient_contDiffOn hg hU i).continuousOn.comp
    (stateSegment_continuous w0 w1).continuousOn (fun t ht => hsegment t ht)

theorem sixVariableQ_segment_FTC {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) :
    sixVariableQ g w1 - sixVariableQ g w0 =
      ∑ i, averagedQCoefficient g w0 w1 i * (w1 i - w0 i) := by
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun sigma => sixVariableQ g (stateSegment w0 w1 sigma))
        (∑ i, qFirstCoefficient g i (stateSegment w0 w1 t) * (w1 i - w0 i)) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hQ := ((sixVariableQ_contDiffOn hg hU).contDiffAt
      ((darbouxQStateDomain_isOpen hg hU).mem_nhds (hsegment t ht'))).differentiableAt (by simp)
    have hh := hQ.hasFDerivAt.comp_hasDerivAt t (stateSegment_hasDerivAt w0 w1 t)
    change HasDerivAt (fun sigma => sixVariableQ g (stateSegment w0 w1 sigma))
      (fderiv ℝ (sixVariableQ g) (stateSegment w0 w1 t) (w1 - w0)) t at hh
    rw [sixVariableQ_fderiv_apply] at hh
    exact hh
  have hi (i : Fin 6) : IntervalIntegrable
      (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
        volume (0 : ℝ) 1 :=
    ((qCoefficient_segment_continuousOn hg hU hsegment i).mul_const _).intervalIntegrable_of_Icc zero_le_one
  have hint : IntervalIntegrable
      (fun sigma => ∑ i, qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
        volume (0 : ℝ) 1 := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
    change IntervalIntegrable
      (fun sigma => ∑ i, qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
      volume (0 : ℝ) 1 at hh
    exact hh
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [stateSegment_zero, stateSegment_one] at hFTC
  calc
    _ = ∫ sigma in (0 : ℝ)..1, ∑ i,
        qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i) := hFTC.symm
    _ = ∑ i, ∫ sigma in (0 : ℝ)..1,
        qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i) :=
      intervalIntegral.integral_finsetSum (fun i _ => hi i)
    _ = _ := by simp only [intervalIntegral.integral_mul_const, averagedQCoefficient]

theorem sixVariableQ_segment_FTC_of_jet_error {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) (hpU : statePoint w0 ∈ U)
    {B epsilon nu : ℝ} (hB : 0 ≤ B) (heps : 0 ≤ epsilon) (hnu : 0 < nu)
    (hGamma : ∀ r : Fin 2, |christoffel g r 0 0 (statePoint w0)| ≤ B)
    (hjet : ∀ i : Fin 6, |w1 i - w0 i| ≤ epsilon)
    (hbase : nu ≤ |stateQDenominator g w0|)
    (hsmall : (1 + 2 * B) * epsilon ≤ nu / 2) :
    sixVariableQ g w1 - sixVariableQ g w0 =
      ∑ i, averagedQCoefficient g w0 w1 i * (w1 i - w0 i) := by
  apply sixVariableQ_segment_FTC hg hU
  intro sigma hs
  refine ⟨by simpa only [statePoint_segment hp] using hpU, ?_⟩
  have hlower := stateQDenominator_segment_lower g hp hs hB heps hGamma hjet hbase hsmall
  intro hz
  rw [hz, abs_zero] at hlower
  linarith

theorem qHeightJetSegment_mean_linearization {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (z0 z : Coord → ℝ)
    {p : Coord} (hp : p ∈ U) {B epsilon nu : ℝ}
    (hB : 0 ≤ B) (heps : 0 ≤ epsilon) (hnu : 0 < nu)
    (hGamma : ∀ r : Fin 2, |christoffel g r 0 0 p| ≤ B)
    (hgrad : ∀ i : Fin 2, |coordPartial i z p - coordPartial i z0 p| ≤ epsilon)
    (hmixed : |coordPartial 0 (coordPartial 1 z) p -
      coordPartial 0 (coordPartial 1 z0) p| ≤ epsilon)
    (hxx : |coordPartial 0 (coordPartial 0 z) p -
      coordPartial 0 (coordPartial 0 z0) p| ≤ epsilon)
    (hbase : nu ≤ |covHessian g z0 p 0 0|)
    (hsmall : (1 + 2 * B) * epsilon ≤ nu / 2) :
    sixVariableQ g (qSolutionJet z p) - sixVariableQ g (qSolutionJet z0 p) =
      averagedQCoefficient g (qSolutionJet z0 p) (qSolutionJet z p) 2 *
        (coordPartial 0 z p - coordPartial 0 z0 p) +
      averagedQCoefficient g (qSolutionJet z0 p) (qSolutionJet z p) 3 *
        (coordPartial 1 z p - coordPartial 1 z0 p) +
      averagedQCoefficient g (qSolutionJet z0 p) (qSolutionJet z p) 4 *
        (coordPartial 0 (coordPartial 1 z) p - coordPartial 0 (coordPartial 1 z0) p) +
      averagedQCoefficient g (qSolutionJet z0 p) (qSolutionJet z p) 5 *
        (coordPartial 0 (coordPartial 0 z) p - coordPartial 0 (coordPartial 0 z0) p) := by
  have h := sixVariableQ_segment_FTC_of_jet_error hg hU
    (w0 := qSolutionJet z0 p) (w1 := qSolutionJet z p)
    (by simp only [statePoint_qSolutionJet]) (by simpa only [statePoint_qSolutionJet] using hp)
    hB heps hnu (by simpa only [statePoint_qSolutionJet] using hGamma)
    (qSolutionJet_coordinate_error z0 z p heps hgrad hmixed hxx)
    (by simpa only [stateQDenominator_qSolutionJet] using hbase) hsmall
  convert h using 1
  simp [Fin.sum_univ_succ, qSolutionJet]
  ring

theorem averagedQCoefficient_lower {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U)
    (i : Fin 6) {gamma : ℝ}
    (hgamma : ∀ sigma ∈ Icc (0 : ℝ) 1, gamma ≤ qFirstCoefficient g i (stateSegment w0 w1 sigma)) :
    gamma ≤ averagedQCoefficient g w0 w1 i := by
  have hi : IntervalIntegrable
      (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) volume (0 : ℝ) 1 :=
    (qCoefficient_segment_continuousOn hg hU hsegment i).intervalIntegrable_of_Icc zero_le_one
  have hc : IntervalIntegrable (fun _ : ℝ => gamma) volume (0 : ℝ) 1 := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on zero_le_one hc hi hgamma
  simpa [averagedQCoefficient] using h

theorem averagedQPrincipal_margin {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) {gamma : ℝ}
    (hgamma : ∀ sigma ∈ Icc (0 : ℝ) 1,
      gamma ≤ qFirstCoefficient g 5 (stateSegment w0 w1 sigma)) :
    gamma ≤ averagedQCoefficient g w0 w1 5 ∧
      gamma ≤ (averagedQCoefficient g w0 w1 4 / 2) ^ 2 + averagedQCoefficient g w0 w1 5 := by
  have h := averagedQCoefficient_lower hg hU hsegment 5 hgamma
  exact ⟨h, by nlinarith [sq_nonneg (averagedQCoefficient g w0 w1 4 / 2)]⟩

end SmoothLocal.HighEquation

end

end OAI
