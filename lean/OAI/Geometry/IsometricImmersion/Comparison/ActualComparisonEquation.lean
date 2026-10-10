import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonSource
import OAI.Geometry.IsometricImmersion.Darboux.QSegmentAveraging
import OAI.Geometry.IsometricImmersion.Darboux.QStripJetControl
import OAI.Geometry.IsometricImmersion.Energy.MovingSlabEnergy
import OAI.Geometry.IsometricImmersion.Coordinates.ActualShearHyperbolicity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Taylor
open SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def comparisonCoefficient (g : MetricField) (P z : Coord → ℝ) (i : Fin 6) (p : Coord) : ℝ :=
  averagedQCoefficient g (qSolutionJet P p) (qSolutionJet z p) i

def comparisonDifference (P z : Coord → ℝ) (p : Coord) : ℝ := z p-P p

theorem actual_comparison_mean_identity
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (P z : Coord → ℝ) (p : Coord)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) :
    sixVariableQ g (qSolutionJet z p)-sixVariableQ g (qSolutionJet P p) =
      comparisonCoefficient g P z 2 p*(coordPartial 0 z p-coordPartial 0 P p)+
      comparisonCoefficient g P z 3 p*(coordPartial 1 z p-coordPartial 1 P p)+
      comparisonCoefficient g P z 4 p*(coordPartial 0 (coordPartial 1 z) p-
        coordPartial 0 (coordPartial 1 P) p)+
      comparisonCoefficient g P z 5 p*(coordPartial 0 (coordPartial 0 z) p-
        coordPartial 0 (coordPartial 0 P) p) := by
  have hh := sixVariableQ_segment_FTC hg hU hseg
  convert hh using 1
  simp [comparisonCoefficient,Fin.sum_univ_succ,qSolutionJet]
  ring

theorem comparison_equation_from_darboux
    {g g0 : MetricField} {U : Set Coord} {P z : Coord → ℝ}
    (hg : SmoothPositiveOn g U) (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p)
    (hxx : covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g0 U) :
    hyperbolicOperator (comparisonCoefficient g0 P z 4) (comparisonCoefficient g0 P z 5)
      (comparisonDifference P z) p =
        comparisonCoefficient g0 P z 3 p*coordPartial 1 (comparisonDifference P z) p+
        comparisonCoefficient g0 P z 2 p*coordPartial 0 (comparisonDifference P z) p+
        (sixVariableQ g (qSolutionJet z p)-sixVariableQ g0 (qSolutionJet z p)-qResidual g0 P p) := by
  have hQ := (darbouxDet_iff_sixVariableQ hg hU hz hp hxx).mp hD
  have hmean := actual_comparison_mean_identity hg0 hU P z p hseg
  have hsub (ds : List (Fin 2)) := CoordinateBound.iterated_sub hz hP hU ds hp
  have h0 : coordPartial 0 (comparisonDifference P z) p = coordPartial 0 z p-coordPartial 0 P p := hsub [0]
  have h1 : coordPartial 1 (comparisonDifference P z) p = coordPartial 1 z p-coordPartial 1 P p := hsub [1]
  have h00 : coordPartial 0 (coordPartial 0 (comparisonDifference P z)) p =
      coordPartial 0 (coordPartial 0 z) p-coordPartial 0 (coordPartial 0 P) p := hsub [0,0]
  have h01 : coordPartial 0 (coordPartial 1 (comparisonDifference P z)) p =
      coordPartial 0 (coordPartial 1 z) p-coordPartial 0 (coordPartial 1 P) p := hsub [0,1]
  have h11 : coordPartial 1 (coordPartial 1 (comparisonDifference P z)) p =
      coordPartial 1 (coordPartial 1 z) p-coordPartial 1 (coordPartial 1 P) p := hsub [1,1]
  unfold hyperbolicOperator qResidual
  rw [h0,h1,h00,h01,h11,hQ]
  linarith

theorem actual_sheared_comparison_equation
    {gStar gTau : MetricField} {z P : Coord → ℝ} {U : Set Coord}
    (hgStar : SmoothPositiveOn gStar U) (hgTau : SmoothPositiveOn gTau U)
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (q0 : ℝ)
    (hP : ContDiffOn ℝ ∞ P (inverseShearCoordinates q0 ⁻¹' U))
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hD : (covHessian gTau z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature gTau (inverseShearCoordinates q0 p)*heightEnergy gTau z (inverseShearCoordinates q0 p))
    (hxx : covHessian (metricInShearCoordinates gTau q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P (heightInShearCoordinates z q0) sigma p ∈
        darbouxQStateDomain (metricInShearCoordinates gStar q0) (inverseShearCoordinates q0 ⁻¹' U)) :
    let zs := heightInShearCoordinates z q0
    let gs := metricInShearCoordinates gStar q0
    hyperbolicOperator (comparisonCoefficient gs P zs 4) (comparisonCoefficient gs P zs 5)
      (comparisonDifference P zs) p =
        comparisonCoefficient gs P zs 3 p*coordPartial 1 (comparisonDifference P zs) p+
        comparisonCoefficient gs P zs 2 p*coordPartial 0 (comparisonDifference P zs) p+
        actualComparisonSource gStar gTau z q0 P p := by
  exact comparison_equation_from_darboux
    (metricInShearCoordinates_smoothPositive hgTau q0) (metricInShearCoordinates_smoothPositive hgStar q0)
    (hU.preimage (inverseShearCoordinates_contDiff q0).continuous)
    (heightInShearCoordinates_contDiffOn hz q0) hP hp
    (darboux_in_shear_coordinates hgTau hz hU q0 hp hD) hxx hseg

theorem comparison_initial_partials_zero
    {U : Set Coord} {P z : Coord → ℝ} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U)
    {left right a : ℝ} (hcut : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, P (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right, coordPartial 1 P (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    coordPartial 0 (comparisonDifference P z) (boxPoint x a) = 0 ∧
    coordPartial 1 (comparisonDifference P z) (boxPoint x a) = 0 := by
  have hj := qSolutionJet_eq_of_cauchy_data hz hP hU hcut hvalue hvelocity hx
  have hxEq : coordPartial 0 P (boxPoint x a) = coordPartial 0 z (boxPoint x a) :=
    congrArg (fun w : DarbouxState => w 2) hj
  have h0 := CoordinateBound.iterated_sub hz hP hU [0] (hcut x hx)
  have h1 := CoordinateBound.iterated_sub hz hP hU [1] (hcut x hx)
  change coordPartial 0 (comparisonDifference P z) (boxPoint x a) =
    coordPartial 0 z (boxPoint x a)-coordPartial 0 P (boxPoint x a) at h0
  change coordPartial 1 (comparisonDifference P z) (boxPoint x a) =
    coordPartial 1 z (boxPoint x a)-coordPartial 1 P (boxPoint x a) at h1
  exact ⟨by rw [h0,hxEq,sub_self],by rw [h1,hvelocity x hx,sub_self]⟩

theorem comparison_initial_energy_zero
    {U : Set Coord} {P z S : Coord → ℝ} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U)
    {left right xl xr a : ℝ} (hlr : xl ≤ xr)
    (hcut : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (hvalue : ∀ x ∈ Ioo left right, P (boxPoint x a) = z (boxPoint x a))
    (hvelocity : ∀ x ∈ Ioo left right, coordPartial 1 P (boxPoint x a) = coordPartial 1 z (boxPoint x a))
    (hxl : left < xl) (hxr : xr < right) :
    (∫ x in xl..xr, energyDensity S (comparisonDifference P z) (coordinatePoint x a)) = 0 := by
  have hpoint (x : ℝ) (hx : x ∈ uIcc xl xr) :
      energyDensity S (comparisonDifference P z) (coordinatePoint x a) = 0 := by
    have hx' : x ∈ Icc xl xr := by simpa only [uIcc_of_le hlr] using hx
    have hi : x ∈ Ioo left right := ⟨hxl.trans_le hx'.1,hx'.2.trans_lt hxr⟩
    obtain ⟨h0,h1⟩ := comparison_initial_partials_zero hU hz hP hcut hvalue hvelocity hi
    have he : coordinatePoint x a = boxPoint x a := by ext i; fin_cases i <;> simp [coordinatePoint,boxPoint]
    rw [he]
    simp only [energyDensity,h0,h1,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,add_zero,zero_div]
  calc
    _ = ∫ x in xl..xr, (0 : ℝ) := intervalIntegral.integral_congr hpoint
    _ = 0 := intervalIntegral.integral_zero

end SmoothLocal.HighEquation

end

end OAI
