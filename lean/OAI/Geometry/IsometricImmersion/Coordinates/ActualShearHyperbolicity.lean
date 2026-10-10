import OAI.Geometry.IsometricImmersion.Immersions.ActualShearHeight
import OAI.Geometry.IsometricImmersion.Coordinates.ShearSpeedBounds

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem metricInShearCoordinates_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (q0 : ℝ) :
    SmoothPositiveOn (metricInShearCoordinates g q0) (inverseShearCoordinates q0 ⁻¹' U) := by
  simpa only [metricInShearCoordinates, inverseShearCoordinates_eq_affine] using
    affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
      (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))

theorem gaussianCurvature_in_shear_coordinates {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (q0 : ℝ) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) :
    gaussianCurvature (metricInShearCoordinates g q0) p =
      gaussianCurvature g (inverseShearCoordinates q0 p) := by
  simpa only [metricInShearCoordinates, ← inverseShearCoordinates_eq_affine] using
    gaussianCurvature_affinePullback hg hU 0 (inverseShearMatrix q0)
      (inverseShearMatrix_isUnit q0) p
      (by simpa only [← inverseShearCoordinates_eq_affine] using hp)

theorem darboux_in_shear_coordinates {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    (covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p).det =
      gaussianCurvature (metricInShearCoordinates g q0) p *
        heightEnergy (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p := by
  rw [covHessian_in_shear_coordinates hg hz hU q0 hp,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, inverseShearMatrix_det,
    one_mul, mul_one, hD, gaussianCurvature_in_shear_coordinates hg hU q0 hp,
    heightEnergy_in_shear_coordinates hz hU q0 hp]

def shearTimeFactor (g : MetricField) (z : Coord → ℝ) (q0 : ℝ) (p : Coord) : ℝ :=
  (hessianQuotient g z (inverseShearCoordinates q0 p) - q0) ^ 2 +
    gaussianCurvature g (inverseShearCoordinates q0 p) *
      darbouxG g z (inverseShearCoordinates q0 p)

theorem sheared_principal_coefficients {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p))
    (hd : shearTimeFactor g z q0 p ≠ 0) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 ∧
    qFirstCoefficient (metricInShearCoordinates g q0) 4
        (qSolutionJet (heightInShearCoordinates z q0) p) =
      2 * (hessianQuotient g z (inverseShearCoordinates q0 p) - q0) /
        shearTimeFactor g z q0 p ∧
    qFirstCoefficient (metricInShearCoordinates g q0) 5
        (qSolutionJet (heightInShearCoordinates z q0) p) = -1 / shearTimeFactor g z q0 p := by
  have hgS := metricInShearCoordinates_smoothPositive hg q0
  have hzS := heightInShearCoordinates_contDiffOn hz q0
  have hUS := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hfac : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      shearTimeFactor g z q0 p * covHessian g z (inverseShearCoordinates q0 p) 1 1 :=
    sheared_Hxx_factor hg hz hU q0 hp hyy hD
  have hxx : covHessian (metricInShearCoordinates g q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero hd hyy
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  refine ⟨hxx, ?_, ?_⟩
  · rw [q_mixed_coefficient_at_height hgS hUS hp hxx, h01, hfac]
    unfold hessianQuotient
    field_simp [hd, hyy]
  · rw [q_xx_coefficient_at_height hgS hUS hzS hp hxx
      (darboux_in_shear_coordinates hg hz hU q0 hp hD), h11, hfac]
    field_simp [hd, hyy]

theorem actual_shear_hyperbolicity {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) {q0 kappa e M v : ℝ} {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (hkappa : 0 < kappa) (he : 0 < e)
    (hv : 0 < v) (hvBound : v ^ 2 ≤ kappa * e / (2 * M ^ 2))
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hH : |covHessian g z (inverseShearCoordinates q0 p) 1 1| ≤ M)
    (hE : e ≤ heightEnergy g z (inverseShearCoordinates q0 p))
    (hK : gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * (100 * (1 + v⁻¹))))
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    v ^ 2 / 2 ≤ -shearTimeFactor g z q0 p ∧
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 ∧
    0 < qFirstCoefficient (metricInShearCoordinates g q0) 5
      (qSolutionJet (heightInShearCoordinates z q0) p) ∧
    |qFirstCoefficient (metricInShearCoordinates g q0) 4
      (qSolutionJet (heightInShearCoordinates z q0) p)| +
        Real.sqrt (qFirstCoefficient (metricInShearCoordinates g q0) 5
          (qSolutionJet (heightInShearCoordinates z q0) p)) < (100 * (1 + v⁻¹)) / 4 := by
  have ha : gaussianCurvature g (inverseShearCoordinates q0 p) *
      darbouxG g z (inverseShearCoordinates q0 p) ≤ -(v ^ 2) :=
    negative_curvature_factor hkappa he hyy hK hE hH hvBound
  obtain ⟨hb, hspeed⟩ := shear_width_smallness hv hq
  have hfactor := shear_time_factor_bound hv hb ha
  have hdneg : shearTimeFactor g z q0 p < 0 := by
    have hv2 : 0 < v ^ 2 / 2 := half_pos (sq_pos_of_pos hv)
    change v ^ 2 / 2 ≤ -shearTimeFactor g z q0 p at hfactor
    linarith
  obtain ⟨hxx, hP, hS⟩ := sheared_principal_coefficients hg hz hU q0 hp hyy hD hdneg.ne
  obtain ⟨hSpos, hchar⟩ := shear_principal_speed hv hb ha
  refine ⟨hfactor, hxx, ?_, ?_⟩
  · rw [hS]
    exact hSpos
  · rw [hP, hS]
    exact hchar.trans_lt hspeed

end SmoothLocal.Pulse

end

end OAI
