import OAI.Geometry.IsometricImmersion.Curvature.GaussFormula
import OAI.Geometry.IsometricImmersion.Metrics.MetricSmoothness
import Mathlib.Tactic.LinearCombination

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

theorem coordPartial_vector_sub {A B : Coord → Ambient} {p : Coord}
    (hA : DifferentiableAt ℝ A p) (hB : DifferentiableAt ℝ B p) (i : Fin 2) :
    coordPartial i (fun q => A q - B q) p = coordPartial i A p - coordPartial i B p := by
  simp only [coordPartial, fderiv_fun_sub hA hB, sub_apply]

theorem coordPartial_vector_sum (A : Fin 2 → Coord → Ambient) {p : Coord}
    (hA : ∀ r, DifferentiableAt ℝ (A r) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ r, A r q) p = ∑ r, coordPartial i (A r) p := by
  simp only [Fin.sum_univ_two, coordPartial, fderiv_fun_add (hA 0) (hA 1),
    add_apply]

theorem coordPartial_scalar_vector {c : Coord → ℝ} {A : Coord → Ambient} {p : Coord}
    (hc : DifferentiableAt ℝ c p) (hA : DifferentiableAt ℝ A p) (i : Fin 2) :
    coordPartial i (fun q => c q • A q) p =
      coordPartial i c p • A p + c p • coordPartial i A p := by
  simp only [coordPartial, fderiv_fun_smul hc hA, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

theorem normalResidual_contDiffOn {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) (a b : Fin 2) :
    ContDiffOn ℝ ∞ (fun q => normalResidual g F q a b) U := by
  have ht (r : Fin 2) := partial_contDiffOn hF hU r
  have hsecond := partial_contDiffOn (ht b) hU a
  exact hsecond.sub (ContDiffOn.sum fun r _ =>
    (christoffel_contDiffOn hg hU r a b).smul (ht r))

theorem coordPartial_normalResidual {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : ContDiffOn ℝ ∞ F U)
    (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (d a b : Fin 2) :
    coordPartial d (fun q => normalResidual g F q a b) p =
      coordPartial d (coordPartial a (coordPartial b F)) p -
        ∑ r, (coordPartial d (christoffel g r a b) p • coordPartial r F p +
          christoffel g r a b p • coordPartial d (coordPartial r F) p) := by
  have ht (r : Fin 2) : ContDiffOn ℝ ∞ (coordPartial r F) U :=
    partial_contDiffOn hF hU r
  have hdT (r : Fin 2) : DifferentiableAt ℝ (coordPartial r F) p :=
    (((ht r) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdΓ (r : Fin 2) : DifferentiableAt ℝ (christoffel g r a b) p :=
    (((christoffel_contDiffOn hg hU r a b) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdSecond : DifferentiableAt ℝ (coordPartial a (coordPartial b F)) p :=
    (((partial_contDiffOn (ht b) hU a) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdTerm (r : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g r a b q • coordPartial r F q) p :=
    (hdΓ r).smul (hdT r)
  change coordPartial d (fun q => coordPartial a (coordPartial b F) q -
    ∑ r, christoffel g r a b q • coordPartial r F q) p = _
  rw [coordPartial_vector_sub hdSecond (DifferentiableAt.fun_sum fun r _ => hdTerm r),
    coordPartial_vector_sum _ hdTerm]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact coordPartial_scalar_vector (hdΓ r) (hdT r) d

theorem residual_inner_second_eq_residual_inner_residual
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (a b c d : Fin 2) :
    inner ℝ (normalResidual g F p a b) (coordPartial c (coordPartial d F) p) =
      inner ℝ (normalResidual g F p a b) (normalResidual g F p c d) := by
  change inner ℝ (normalResidual g F p a b) (coordPartial c (coordPartial d F) p) =
    inner ℝ (normalResidual g F p a b)
      (coordPartial c (coordPartial d F) p -
        ∑ r, christoffel g r c d p • coordPartial r F p)
  simp only [inner_sub_right, inner_sum, real_inner_smul_right,
    normalResidual_orthogonal_tangent hg hF hU hp, mul_zero,
    Finset.sum_const_zero, sub_zero]

theorem residual_derivative_inner_tangent
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (d a b l : Fin 2) :
    inner ℝ (coordPartial d (fun q => normalResidual g F q a b) p)
        (coordPartial l F p) =
      -inner ℝ (normalResidual g F p a b) (normalResidual g F p d l) := by
  have hdS : DifferentiableAt ℝ (fun q => normalResidual g F q a b) p :=
    (((normalResidual_contDiffOn hg hF.1 hU a b) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdT : DifferentiableAt ℝ (coordPartial l F) p :=
    (((partial_contDiffOn hF.1 hU l) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hzero : (fun q => inner ℝ (normalResidual g F q a b) (coordPartial l F q))
      =ᶠ[𝓝 p] (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact normalResidual_orthogonal_tangent hg hF hU hq a b l
  have hderiv := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single d 1)) hzero.fderiv_eq
  rw [fderiv_inner_apply ℝ hdS hdT] at hderiv
  simp only [fderiv_const_apply, zero_apply] at hderiv
  change inner ℝ (normalResidual g F p a b) (coordPartial d (coordPartial l F) p) +
    inner ℝ (coordPartial d (fun q => normalResidual g F q a b) p)
      (coordPartial l F p) = 0 at hderiv
  rw [residual_inner_second_eq_residual_inner_residual hg hF hU hp] at hderiv
  linarith

theorem second_partial_inner_tangent_eq_christoffel_sum
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (a b l : Fin 2) :
    inner ℝ (coordPartial a (coordPartial b F) p) (coordPartial l F p) =
      ∑ r, christoffel g r a b p * g p l r := by
  have ht (r : Fin 2) : inner ℝ (coordPartial r F p) (coordPartial l F p) = g p l r := by
    rw [real_inner_comm]
    exact congrFun (congrFun (inducedMetric_eq_of_isometric hF hp) l) r
  have h := normalResidual_orthogonal_tangent hg hF hU hp a b l
  simp only [normalResidual, inner_sub_left, sum_inner, real_inner_smul_left, ht] at h
  exact sub_eq_zero.mp h

theorem riemann_contraction_eq_residual_products
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j k l : Fin 2) :
    (∑ r, g p l r * riemann g r k i j p) =
      inner ℝ (normalResidual g F p j k) (normalResidual g F p i l) -
        inner ℝ (normalResidual g F p i k) (normalResidual g F p j l) := by
  have hi := residual_derivative_inner_tangent hg hF hU hp i j k l
  have hj := residual_derivative_inner_tangent hg hF hU hp j i k l
  rw [coordPartial_normalResidual hg hF.1 hU hp] at hi hj
  have ht (r : Fin 2) : inner ℝ (coordPartial r F p) (coordPartial l F p) = g p l r := by
    rw [real_inner_comm]
    exact congrFun (congrFun (inducedMetric_eq_of_isometric hF hp) l) r
  simp only [inner_sub_left, sum_inner, inner_add_left, real_inner_smul_left, ht,
    second_partial_inner_tangent_eq_christoffel_sum hg hF hU hp] at hi hj
  have hcomm := coordPartial_comm (partial_contDiffOn hF.1 hU k) hU hp i j
  rw [hcomm] at hi
  simp only [riemann, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two] at hi hj
  linear_combination hj - hi

theorem det_secondFundamental_eq_gaussianCurvature_mul_det
    {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {n : Ambient} (hn : IsUnitNormalAt F n p) :
    (secondFundamental F n p).det = gaussianCurvature g p * (g p).det := by
  have hR := riemann_contraction_eq_residual_products hg hF hU hp 0 1 1 0
  simp only [normalResidual_eq_secondFundamental_smul hg hF hU hp hn,
    real_inner_smul_left, real_inner_smul_right, hn.1, mul_one] at hR
  calc
    (secondFundamental F n p).det = ∑ r, g p 0 r * riemann g r 1 0 1 p := by
      rw [hR, Matrix.det_fin_two]
      ring
    _ = gaussianCurvature g p * (g p).det := by
      unfold gaussianCurvature
      rw [div_mul_cancel₀ _ (metricDet_ne_zero hg hp)]

end SmoothLocal.Geometry

end

end OAI
