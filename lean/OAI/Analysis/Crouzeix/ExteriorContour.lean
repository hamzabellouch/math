import Mathlib
import OAI.Analysis.Crouzeix.BoundaryKernel
import OAI.Analysis.Crouzeix.CircleAnalytic
import OAI.Analysis.Crouzeix.PolynomialApproximation

namespace OAI

/-! Exterior Contour. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

def boundaryMap : C(CircleSpace, ℂ) where
  toFun t := C.G (circleCoordinate t)
  continuous_toFun := C.analytic.continuousOn.comp_continuous circleCoordinate.continuous
    (fun t => by change C.radius < ‖circleCoordinate t‖; rw [norm_circleCoordinate]; exact C.radius_lt_one)

def boundaryNormal : C(CircleSpace, ℂ) where
  toFun t := circleCoordinate t * deriv C.G (circleCoordinate t)
  continuous_toFun := circleCoordinate.continuous.mul
    (C.analytic.deriv.continuousOn.comp_continuous circleCoordinate.continuous
      (fun t => by change C.radius < ‖circleCoordinate t‖; rw [norm_circleCoordinate]; exact C.radius_lt_one))

lemma boundaryMap_mem_frontier (t : CircleSpace) : C.boundaryMap t ∈ frontier U :=
  C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr (norm_circleCoordinate t))

def boundaryContour : SmoothContour where
  path t := C.G (unitCirclePath t)
  smooth := (C.analytic.contDiffOn C.parameter_open.uniqueDiffOn |>.restrict_scalars ℝ).comp_contDiff
    unitCirclePath_smooth (fun t => by change C.radius < ‖unitCirclePath t‖; rw [unitCirclePath_norm]; exact C.radius_lt_one)
  closed := by rw [unitCirclePath_closed]

lemma boundaryContour_deriv (t : ℝ) :
    deriv C.boundaryContour.path t =
      (2 * (Real.pi : ℂ) * I) * C.boundaryNormal (t : CircleSpace) := by
  have hc : C.radius < ‖unitCirclePath t‖ := by rw [unitCirclePath_norm]; exact C.radius_lt_one
  have hd := ((C.analytic _ hc).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
    t (hasDerivAt_unitCirclePath t)
  change HasDerivAt C.boundaryContour.path _ t at hd
  rw [hd.deriv]
  change (unitCirclePath t * (2 * (Real.pi : ℂ) * I)) * deriv C.G (unitCirclePath t) = _
  change _ = (2 * (Real.pi : ℂ) * I) * (circleCoordinate (t : CircleSpace) * _)
  rw [circleCoordinate_coe]
  change (circleMap 0 1 (2 * Real.pi * t) * (2 * (Real.pi : ℂ) * I)) * _ = _
  unfold unitCirclePath
  ring

lemma boundaryContour_trace_subset : C.boundaryContour.trace ⊆ frontier U := by
  rintro z ⟨t,ht,rfl⟩
  exact C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr (unitCirclePath_norm t))

lemma boundaryContour_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t • f (C.boundaryContour.path t)) =
    ∫ t, C.boundaryNormal t • f (C.boundaryMap t) ∂circleMeasure := by
  rw [integral_circleMeasure_eq_interval, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [C.boundaryContour_deriv, smul_smul, inv_mul_cancel_left₀]
  · congr 1
    change f (C.G (unitCirclePath t)) = f (C.G (circleCoordinate (t : CircleSpace)))
    rw [circleCoordinate_coe]
    rfl
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero

lemma exterior_value_not_mem (hU : IsOpen U) {t : ℂ} (ht : 1 ≤ ‖t‖) : C.G t ∉ U := by
  rcases ht.eq_or_lt with he|he
  · have hb := C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr he.symm)
    exact fun hz => hb.2 (hU.interior_eq.symm ▸ hz)
  · exact fun h => C.outside.mapsTo he (subset_closure h)

def reciprocalDenominator (z u : ℂ) : ℂ := C.leading + u * (C.regular u - z)

lemma reciprocalDenominator_inverse {z t : ℂ} (ht : C.radius < ‖t‖) :
    C.reciprocalDenominator z t⁻¹ = t⁻¹ * (C.G t - z) := by
  rw [C.laurent t ht, reciprocalDenominator]
  have hn : t ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  field_simp
  ring

lemma reciprocalDenominator_ne_zero (hU : IsOpen U) {z u : ℂ} (hz : z ∈ U)
    (hu : u ∈ closedBall 0 1) : C.reciprocalDenominator z u ≠ 0 := by
  by_cases hu0 : u = 0
  · simpa only [hu0, reciprocalDenominator, zero_mul, add_zero] using C.leading_ne_zero
  have ht : 1 ≤ ‖u⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hu0)).mpr (mem_closedBall_zero_iff.mp hu)
  have he := C.reciprocalDenominator_inverse (z := z) (C.radius_lt_one.trans_le ht)
  rw [inv_inv] at he
  rw [he]
  exact mul_ne_zero hu0 (sub_ne_zero.mpr (fun h => C.exterior_value_not_mem hU ht (h ▸ hz)))

def reciprocalCauchy (z u : ℂ) : ℂ :=
  (C.leading - u^2 * deriv C.regular u) / C.reciprocalDenominator z u

lemma differentiableOn_reciprocalCauchy (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableOn ℂ (C.reciprocalCauchy z) (closedBall 0 1) := by
  apply DifferentiableOn.div
  · exact (differentiableOn_const _).sub ((differentiableOn_id.pow 2).mul
      (C.regular_analytic.deriv.differentiableOn.mono C.closed_unit_subset_reciprocalDisk))
  · exact (differentiableOn_const _).add (differentiableOn_id.mul
      ((C.regular_analytic.differentiableOn.mono C.closed_unit_subset_reciprocalDisk).sub_const z))
  · exact fun u hu => C.reciprocalDenominator_ne_zero hU hz hu

lemma reciprocalCauchy_boundary (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) (t : CircleSpace) :
    C.reciprocalCauchy z (circleCoordinate t)⁻¹ =
      C.boundaryNormal t / (C.boundaryMap t - z) := by
  have ht : C.radius < ‖circleCoordinate t‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  rw [reciprocalCauchy, C.reciprocalDenominator_inverse ht, ← C.deriv_laurent ht]
  change deriv C.G (circleCoordinate t) / ((circleCoordinate t)⁻¹ * (C.G (circleCoordinate t) - z)) = _
  simp only [boundaryNormal, boundaryMap, ContinuousMap.coe_mk]
  have hden : C.G (circleCoordinate t) - z ≠ 0 :=
    sub_ne_zero.mpr fun he =>
      C.exterior_value_not_mem hU (norm_circleCoordinate t).ge (he ▸ hz)
  field_simp [hden]

lemma boundaryContour_index_inside (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    C.boundaryContour.index z = 1 := by
  change (2 * (Real.pi : ℂ) * I)⁻¹ •
    (∫ t in (0 : ℝ)..1, deriv C.boundaryContour.path t * (C.boundaryContour.path t - z)⁻¹) = 1
  rw [show (fun t : ℝ => deriv C.boundaryContour.path t * (C.boundaryContour.path t - z)⁻¹) =
      fun t => deriv C.boundaryContour.path t • (C.boundaryContour.path t - z)⁻¹ from rfl,
    C.boundaryContour_integral (fun w => (w - z)⁻¹)]
  change (∫ t, C.boundaryNormal t / (C.boundaryMap t - z) ∂circleMeasure) = 1
  simp_rw [← C.reciprocalCauchy_boundary hU hz]
  rw [integral_holomorphic_inverse_circleCoordinate (C.differentiableOn_reciprocalCauchy hU hz)]
  simp [reciprocalCauchy, reciprocalDenominator, C.leading_ne_zero]

lemma boundaryContour_index_outside (hc : Convex ℝ U) {z : ℂ} (hz : z ∉ closure U) :
    C.boundaryContour.index z = 0 :=
  C.boundaryContour.index_eq_zero_of_convex hc.closure isClosed_closure
    (C.boundaryContour_trace_subset.trans frontier_subset_closure) hz

lemma physical_cauchy_formula (hU : IsOpen U) {V : Set ℂ} (hV : IsOpen V)
    (hcV : Convex ℝ V) (hUV : closure U ⊆ V) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f V) {z : ℂ} (hz : z ∈ U) :
    (∫ t, (C.boundaryNormal t / (C.boundaryMap t - z)) * f (C.boundaryMap t)
      ∂circleMeasure) = f z := by
  have hztrace : z ∉ C.boundaryContour.trace := by
    intro he
    exact (C.boundaryContour_trace_subset he).2 (hU.interior_eq.symm ▸ hz)
  have he := C.boundaryContour.cauchy_formula_convex hV hcV
    (C.boundaryContour_trace_subset.trans (frontier_subset_closure.trans hUV)) hf
    (hUV (subset_closure hz)) hztrace
  rw [C.boundaryContour_index_inside hU hz, one_mul] at he
  have hi := C.boundaryContour_integral (fun w => f w / (w - z))
  simp only [smul_eq_mul] at hi
  have hmul (a b c : ℂ) : a * (b / c) = a * b / c := by ring
  have hmul' (a b c : ℂ) : a * (b / c) = (a / c) * b := by ring
  simp_rw [hmul] at hi
  rw [hi] at he
  convert he using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by ring

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
