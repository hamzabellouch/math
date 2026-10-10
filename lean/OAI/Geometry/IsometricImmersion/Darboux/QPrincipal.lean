import OAI.Geometry.IsometricImmersion.Darboux.SixVariableQ

namespace OAI

noncomputable section
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qFirstCoefficient (g : MetricField) (i : Fin 6) (w : DarbouxState) : ℝ :=
  fderiv ℝ (sixVariableQ g) w (Pi.single i 1)

theorem qFirstCoefficient_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (qFirstCoefficient g i) (darbouxQStateDomain g U) :=
  ((sixVariableQ_contDiffOn hg hU).fderiv_of_isOpen
    (darbouxQStateDomain_isOpen hg hU) (by simp)).clm_apply contDiffOn_const

theorem q_principal_discriminant {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    (qFirstCoefficient g 4 w / 2) ^ 2 + qFirstCoefficient g 5 w =
      -(gaussianCurvature g (statePoint w) * stateEnergy g w) / (stateQDenominator g w) ^ 2 := by
  unfold qFirstCoefficient
  rw [sixVariableQ_mixed_axis hg hU hw, sixVariableQ_xx_axis hg hU hw]
  ring

theorem q_principal_discriminant_pos {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U)
    (hK : gaussianCurvature g (statePoint w) < 0) (hE : 0 < stateEnergy g w) :
    0 < (qFirstCoefficient g 4 w / 2) ^ 2 + qFirstCoefficient g 5 w := by
  rw [q_principal_discriminant hg hU hw]
  exact div_pos (neg_pos.mpr (mul_neg_of_neg_of_pos hK hE)) (sq_pos_of_ne_zero hw.2)

theorem q_xx_coefficient_pos_of_numerator_neg {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) (hN : stateNumerator g w < 0) :
    0 < qFirstCoefficient g 5 w := by
  have heq : qFirstCoefficient g 5 w =
      -(stateNumerator g w) / (stateQDenominator g w) ^ 2 := by
    unfold qFirstCoefficient
    rw [sixVariableQ_xx_axis hg hU hw]
    simp only [stateNumerator, jetNumerator, stateMixed, stateEnergy, div_pow]
    ring
  rw [heq]
  exact div_pos (neg_pos.mpr hN) (sq_pos_of_ne_zero hw.2)

theorem q_mixed_coefficient_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    qFirstCoefficient g 4 (qSolutionJet z p) =
      2 * (covHessian g z p 0 1 / covHessian g z p 0 0) := by
  unfold qFirstCoefficient
  rw [sixVariableQ_mixed_axis hg hU (qSolutionJet_mem_domain hp hxx),
    stateQDenominator_qSolutionJet]
  unfold stateMixed
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  rfl

theorem q_xx_coefficient_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    qFirstCoefficient g 5 (qSolutionJet z p) =
      -(covHessian g z p 1 1 / covHessian g z p 0 0) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold qFirstCoefficient
  rw [sixVariableQ_xx_axis hg hU (qSolutionJet_mem_domain hp hxx),
    stateQDenominator_qSolutionJet]
  simp only [stateMixed, stateEnergy, statePoint_qSolutionJet, stateGradient_qSolutionJet]
  change -((jetMixed g p (coordPartial 0 (coordPartial 1 z) p)
    (fun i => coordPartial i z p) / covHessian g z p 0 0) ^ 2 +
      gaussianCurvature g p * jetEnergy g p (fun i => coordPartial i z p) /
        (covHessian g z p 0 0) ^ 2) = _
  rw [jetMixed_at_height, jetEnergy_at_height hg hp z]
  field_simp [hxx]
  nlinarith [hdet]

theorem hessian_time_ratio {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    (hessianQuotient g z p) ^ 2 + gaussianCurvature g p * darbouxG g z p =
      covHessian g z p 0 0 / covHessian g z p 1 1 := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold hessianQuotient darbouxG
  field_simp [hyy]
  nlinarith [hdet]

theorem q_xx_coefficient_eq_neg_inv_time_ratio {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    qFirstCoefficient g 5 (qSolutionJet z p) =
      -1 / ((hessianQuotient g z p) ^ 2 + gaussianCurvature g p * darbouxG g z p) := by
  rw [q_xx_coefficient_at_height hg hU hz hp hxx hD,
    hessian_time_ratio hg hU hz hp hyy hD]
  field_simp [hxx, hyy]

theorem q_xx_coefficient_at_height_pos {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hd : (hessianQuotient g z p) ^ 2 + gaussianCurvature g p * darbouxG g z p < 0) :
    0 < qFirstCoefficient g 5 (qSolutionJet z p) := by
  rw [q_xx_coefficient_eq_neg_inv_time_ratio hg hU hz hp hxx hyy hD]
  exact div_pos_of_neg_of_neg (by norm_num) hd

end SmoothLocal.HighEquation

end

end OAI
