import Mathlib
import OAI.Analysis.Crouzeix.LaurentSplit
import OAI.Analysis.Crouzeix.PhysicalFourier

namespace OAI

/-! Physical Projection. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace Matrix.Norms.L2Operator

namespace CrouzeixHilbert

namespace Boundary

def boundaryFieldCLM (k : ℕ) : C(CircleSpace, Coeff k) →L[ℂ] BoundaryL2 k :=
  (ContinuousMap.toLp 2 circleMeasure ℂ).comp
    (ContinuousLinearMap.compLeftContinuous ℂ CircleSpace (toHSCLM k))

@[simp] lemma boundaryFieldCLM_apply {k : ℕ} (F : C(CircleSpace, Coeff k)) :
    boundaryFieldCLM k F = boundaryField F := rfl

lemma boundaryField_sum {k : ℕ} {ι : Type*} (s : Finset ι) (F : ι → C(CircleSpace, Coeff k)) :
    boundaryField (∑ i ∈ s, F i) = ∑ i ∈ s, boundaryField (F i) :=
  map_sum (boundaryFieldCLM k) F s

end Boundary

namespace Conformal.ExteriorCollar

open Boundary

variable {U : Set ℂ} (C : ExteriorCollar U)

def physicalPolynomial (p : Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j * C.physicalCoefficient (j : ℤ) z

lemma differentiableOn_physicalPolynomial (p : Polynomial ℂ) :
    DifferentiableOn ℂ (C.physicalPolynomial p) C.outerDomain := by
  exact DifferentiableOn.fun_sum (fun j _ =>
    (C.differentiableOn_physicalCoefficient (j : ℤ)).const_mul (p.coeff j))

def polynomialCircle (p : Polynomial ℂ) : C(CircleSpace, ℂ) :=
  ⟨fun t => p.eval (circleCoordinate t), p.continuous.comp circleCoordinate.continuous⟩

def physicalPolynomialTrace (p : Polynomial ℂ) : C(CircleSpace, ℂ) :=
  ⟨fun t => C.physicalPolynomial p (C.boundaryMap t),
    (C.differentiableOn_physicalPolynomial p).continuousOn.comp_continuous
      C.boundaryMap.continuous (fun t => C.closure_subset_outerDomain (C.boundaryMap_mem_frontier t).1)⟩

lemma boundaryCauchy_polynomialCircle (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (p : Polynomial ℂ) (i l : Fin k) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (scalarChannel i l (polynomialCircle p))) =
      boundaryField (scalarChannel i l (C.physicalPolynomialTrace p)) := by
  have hp : scalarChannel i l (polynomialCircle p) =
      ∑ j ∈ Finset.range (p.natDegree+1), matrixLaurentMonomial ((j : ℤ),i,l) (p.coeff j) := by
    ext t a b
    simp only [ContinuousMap.sum_apply, Matrix.sum_apply, scalarChannel, polynomialCircle,
      ContinuousMap.coe_mk, Matrix.smul_apply, smul_eq_mul, matrixLaurentMonomial,
      Polynomial.eval_eq_sum_range, Finset.sum_mul, circleCoordinate_pow]
  have hv : scalarChannel i l (C.physicalPolynomialTrace p) =
      ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j • C.physicalChannel ((j : ℤ),i,l) := by
    ext t a b
    simp only [ContinuousMap.sum_apply, Matrix.sum_apply, scalarChannel, physicalPolynomialTrace,
      physicalPolynomial, physicalChannel, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [hp, hv, boundaryField_sum, map_sum, boundaryField_sum]
  exact Finset.sum_congr rfl (fun j _ => C.boundaryCauchy_matrixLaurentMonomial hU hc _ _)

lemma physicalPolynomial_inside (hU : IsOpen U) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ U) :
    C.physicalPolynomial p z = ∫ t, p.eval (circleCoordinate t) *
      (C.boundaryNormal t / (C.boundaryMap t - z)) ∂circleMeasure := by
  have hd (t : CircleSpace) : C.boundaryMap t - z ≠ 0 := by
    intro he
    exact (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ (sub_eq_zero.mp he ▸ hz))
  have hk : Continuous (fun t => C.boundaryNormal t / (C.boundaryMap t-z)) :=
    C.boundaryNormal.continuous.div (C.boundaryMap.continuous.sub continuous_const) hd
  simp only [physicalPolynomial, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ =>
    (show Continuous (fun t : CircleSpace => p.coeff j * circleCoordinate t ^ j *
      (C.boundaryNormal t / (C.boundaryMap t-z))) from
      (continuous_const.mul (circleCoordinate.continuous.pow j)).mul hk).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [C.physicalCoefficient_inside hU _ hz]
  simp only [zpow_natCast, mul_assoc, integral_const_mul]

lemma cauchy_inverse_q_zero (hU : IsOpen U) {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (closedBall 0 1)) (hq0 : q 0 = 0)
    {z : ℂ} (hz : z ∈ U) :
    (∫ t, q (circleCoordinate t)⁻¹ * (C.boundaryNormal t / (C.boundaryMap t-z))
      ∂circleMeasure) = 0 := by
  simp_rw [← C.reciprocalCauchy_boundary hU hz]
  have he := integral_holomorphic_inverse_circleCoordinate
    (hq.mul (C.differentiableOn_reciprocalCauchy hU hz))
  simpa only [Pi.mul_apply, hq0, zero_mul] using he

lemma physicalPolynomial_of_power_split (hU : IsOpen U) (p : Polynomial ℂ) (q : ℂ → ℂ)
    (hq : DifferentiableOn ℂ q C.reciprocalDisk) (hq0 : q 0 = 0) (n : ℕ)
    (hsplit : ∀ t, C.radius < ‖t‖ → (C.G t)^n = p.eval t + q t⁻¹) :
    EqOn (C.physicalPolynomial p) (fun z => z^n) (closure U) := by
  have he : EqOn (C.physicalPolynomial p) (fun z => z^n) U := by
    intro z hz
    have hcp := C.physical_cauchy_formula hU isOpen_univ (convex_univ : Convex ℝ (univ : Set ℂ))
      (subset_univ _) (differentiableOn_id.pow n) hz
    have hd (t : CircleSpace) : C.boundaryMap t - z ≠ 0 := by
      intro he
      exact (C.boundaryMap_mem_frontier t).2 (hU.interior_eq.symm ▸ (sub_eq_zero.mp he ▸ hz))
    have hk : Continuous (fun t => C.boundaryNormal t / (C.boundaryMap t-z)) :=
      C.boundaryNormal.continuous.div (C.boundaryMap.continuous.sub continuous_const) hd
    have hqc : Continuous (fun t : CircleSpace => q (circleCoordinate t)⁻¹) :=
      hq.continuousOn.comp_continuous
        (circleCoordinate.continuous.inv₀ circleCoordinate_ne_zero) C.circle_inverse_mem
    have hi1 : Integrable (fun t => p.eval (circleCoordinate t) *
        (C.boundaryNormal t / (C.boundaryMap t-z))) circleMeasure := ((polynomialCircle p).continuous.fun_mul hk).integrable_of_hasCompactSupport
      (μ := circleMeasure)
      (HasCompactSupport.of_compactSpace _)
    have hi2 := (hqc.fun_mul hk).integrable_of_hasCompactSupport (μ := circleMeasure)
      (HasCompactSupport.of_compactSpace _)
    have halg (t : CircleSpace) : C.boundaryNormal t / (C.boundaryMap t - z) * (C.boundaryMap t)^n =
        p.eval (circleCoordinate t) * (C.boundaryNormal t / (C.boundaryMap t - z)) +
        q (circleCoordinate t)⁻¹ * (C.boundaryNormal t / (C.boundaryMap t - z)) := by
      change _ * (C.G (circleCoordinate t))^n = _
      rw [hsplit _ (by rw [norm_circleCoordinate]; exact C.radius_lt_one)]
      ring
    change (∫ t, (C.boundaryNormal t / (C.boundaryMap t-z)) * (C.boundaryMap t)^n
      ∂circleMeasure) = z^n at hcp
    simp_rw [halg] at hcp
    rw [integral_add hi1 hi2, C.cauchy_inverse_q_zero hU
      (hq.mono C.closed_unit_subset_reciprocalDisk) hq0 hz, add_zero] at hcp
    exact (C.physicalPolynomial_inside hU p hz).trans hcp
  exact Set.EqOn.of_subset_closure he
    ((C.differentiableOn_physicalPolynomial p).continuousOn.mono C.closure_subset_outerDomain)
    (continuous_id.pow n).continuousOn subset_closure (Subset.refl _)

lemma boundaryCauchy_physical_power (hU : IsOpen U) (hc : Convex ℝ U) {k : ℕ}
    (n : ℕ) (i l : Fin k) :
    boundaryCauchy (C.boundaryOperator hc k)
      (boundaryField (scalarChannel i l (C.boundaryMap^n))) =
      boundaryField (scalarChannel i l (C.boundaryMap^n)) := by
  obtain ⟨p,q,hq,hq0,hsplit⟩ := C.power_finite_principal_part n
  let Q : C(CircleSpace, ℂ) := ⟨fun t => q (circleCoordinate t)⁻¹,
    hq.continuousOn.comp_continuous
      (circleCoordinate.continuous.inv₀ circleCoordinate_ne_zero) C.circle_inverse_mem⟩
  have hqz : boundaryCauchy (C.boundaryOperator hc k) (boundaryField (scalarChannel i l Q)) = 0 := by
    apply boundaryCauchy_inverse_zero (f := fun z => q z • Matrix.single i l (1 : ℂ))
    · intro a b
      exact (hq.mono C.closed_unit_subset_reciprocalDisk).mul_const _
    · simp [hq0]
    · exact fun _ => rfl
  have he : scalarChannel i l (C.boundaryMap^n) =
      scalarChannel i l (polynomialCircle p) + scalarChannel i l Q := by
    ext t a b
    change (C.G (circleCoordinate t))^n * _ = _
    rw [hsplit _ (by rw [norm_circleCoordinate]; exact C.radius_lt_one)]
    simp only [ContinuousMap.add_apply, scalarChannel, ContinuousMap.coe_mk,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, polynomialCircle, Q]
  have hpe : C.physicalPolynomialTrace p = C.boundaryMap^n := by
    ext t
    exact C.physicalPolynomial_of_power_split hU p q hq hq0 n hsplit
      (C.boundaryMap_mem_frontier t).1
  conv_lhs => rw [he]
  rw [boundaryField_add, map_add, hqz, add_zero, C.boundaryCauchy_polynomialCircle hU hc, hpe]

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
