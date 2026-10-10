import Mathlib
import OAI.Analysis.Crouzeix.InteriorCollar
import OAI.Analysis.Crouzeix.PhysicalModule

namespace OAI

/-! Angular Transport. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped InnerProductSpace

namespace CrouzeixHilbert.Conformal

open Boundary

lemma angular_derivative_real_nonneg {g : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ = 1)
    (hga : DifferentiableAt ℂ g z) (hnt : ∀ w, ‖w‖ = 1 → ‖g w‖ = 1)
    (hmax : IsLocalMaxOn (fun w => ‖g w‖^2) (closedBall 0 1) z) :
    (z * deriv g z / g z).im = 0 ∧ 0 ≤ (z * deriv g z / g z).re := by
  have hgz : ‖g z‖ = 1 := hnt z hz
  have hinv : (g z)⁻¹ = conj (g z) := Complex.inv_eq_conj hgz
  have hc : HasDerivAt (fun t : ℝ => g (z * circleMap 0 1 t)) ((z * I) * deriv g z) 0 := by
    have hp : HasDerivAt (fun t : ℝ => z * circleMap 0 1 t) (z * I) 0 := by
      simpa [circleMap_zero] using (hasDerivAt_circleMap 0 1 0).const_mul z
    have hg' : HasDerivAt g (deriv g z) (z * circleMap 0 1 (0 : ℝ)) := by
      simpa [circleMap_zero] using hga.hasDerivAt
    simpa [Function.comp_def, mul_comm] using (hg'.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hp
  have hc0 : ∀ t : ℝ, ‖g (z * circleMap 0 1 t)‖ ^ 2 = 1 := by
    intro t
    rw [hnt _ (by rw [norm_mul, hz]; simp), one_pow]
  have hd0 := (hc.norm_sq.congr_of_eventuallyEq (Eventually.of_forall (fun t => (hc0 t).symm))).unique
    (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply] at hd0
  simp only [circleMap_zero, ofReal_one, ofReal_zero, zero_mul, exp_zero, mul_one] at hd0
  have he0 : (z * deriv g z * conj (g z)).im = 0 := by
    have halg : (((z * I) * deriv g z) * conj (g z)).re =
        -(z * deriv g z * conj (g z)).im := by
      simp only [Complex.mul_re, Complex.mul_im, I_re, I_im, mul_zero, mul_one]
      ring
    change 2 * (((z * I) * deriv g z) * conj (g z)).re = 0 at hd0
    rw [halg] at hd0
    linarith
  have hdir := hmax.hasFDerivWithinAt_nonpos
    (hga.hasDerivAt.hasFDerivAt.restrictScalars ℝ).norm_sq.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset
      ((convex_closedBall (0 : ℂ) (1 : ℝ)).segment_subset
        (mem_closedBall_zero_iff.mpr hz.le) (mem_closedBall_self zero_le_one)))
  simp only [ContinuousLinearMap.comp_apply, smul_apply] at hdir
  simp only [innerSL_apply_apply] at hdir
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply] at hdir
  simp only [two_smul, zero_sub] at hdir
  change (((-z) * deriv g z) * conj (g z)).re +
    (((-z) * deriv g z) * conj (g z)).re ≤ 0 at hdir
  simp only [neg_mul, neg_re] at hdir
  rw [div_eq_mul_inv, hinv]
  exact ⟨he0, by linarith⟩

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

def interiorBoundary : C(CircleSpace, ℂ) :=
  C.analyticTrace R.closure_subset_domain R.f R.analytic_f.continuousOn

lemma norm_interiorBoundary (t : CircleSpace) : ‖C.interiorBoundary R t‖ = 1 :=
  R.boundary_norm _ (C.boundaryMap_mem_frontier t)

def angularJacobian : C(CircleSpace, ℂ) :=
  ⟨fun t => C.boundaryNormal t * deriv R.f (C.boundaryMap t) / C.interiorBoundary R t,
    (C.boundaryNormal.continuous.mul (R.analytic_f.deriv.continuousOn.comp_continuous
      C.boundaryMap.continuous (fun t => R.closure_subset_domain (C.boundaryMap_mem_frontier t).1))).div
      (C.interiorBoundary R).continuous
      (fun t => norm_ne_zero_iff.mp (by rw [C.norm_interiorBoundary]; exact one_ne_zero))⟩

lemma angularJacobian_real_nonneg (t : CircleSpace) :
    (C.angularJacobian R t).im = 0 ∧ 0 ≤ (C.angularJacobian R t).re := by
  let g := R.f ∘ C.G
  have ht : C.radius < ‖circleCoordinate t‖ := by rw [norm_circleCoordinate]; exact C.radius_lt_one
  have hfg : DifferentiableAt ℂ R.f (C.G (circleCoordinate t)) :=
    (R.analytic_f _ (R.closure_subset_domain (C.boundaryMap_mem_frontier t).1)).differentiableAt
  have hg : DifferentiableAt ℂ g (circleCoordinate t) :=
    hfg.comp (circleCoordinate t) (C.analytic _ ht).differentiableAt
  have hn : ∀ w, ‖w‖ = 1 → ‖g w‖ = 1 := fun w hw => R.boundary_norm _
    (C.boundary.mapsTo (mem_sphere_zero_iff_norm.mpr hw))
  have hmax : IsLocalMaxOn (fun w => ‖g w‖^2) (closedBall 0 1) (circleCoordinate t) := by
    filter_upwards [nhdsWithin_le_nhds (C.parameter_open.mem_nhds ht), self_mem_nhdsWithin] with w hw hw1
    rw [hn _ (norm_circleCoordinate t), one_pow]
    have hwle : ‖g w‖ ≤ 1 := by
      rcases (mem_closedBall_zero_iff.mp hw1).eq_or_lt with h|h
      · exact (hn w h).le
      · exact (mem_ball_zero_iff.mp (R.bijective_f.mapsTo (C.inside ⟨hw,h⟩))).le
    nlinarith [norm_nonneg (g w)]
  have hp := angular_derivative_real_nonneg (norm_circleCoordinate t) hg hn hmax
  have hd : deriv g (circleCoordinate t) = deriv R.f (C.G (circleCoordinate t)) *
      deriv C.G (circleCoordinate t) :=
    deriv_comp _ (R.analytic_f _ (R.closure_subset_domain (C.boundaryMap_mem_frontier t).1)).differentiableAt
      (C.analytic _ ht).differentiableAt
  rw [hd] at hp
  have he : C.angularJacobian R t = circleCoordinate t *
      (deriv R.f (C.G (circleCoordinate t)) * deriv C.G (circleCoordinate t)) / g (circleCoordinate t) := by
    change circleCoordinate t * deriv C.G (circleCoordinate t) *
      deriv R.f (C.G (circleCoordinate t)) / R.f (C.G (circleCoordinate t)) = _
    dsimp only [g, Function.comp_def]
    ring
  rw [he]
  exact hp

lemma physical_integral_zero (hc : Convex ℝ U) {V : Set ℂ}
    (hV : IsOpen V) (hUV : closure U ⊆ V) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g V) :
    (∫ t, C.boundaryNormal t * g (C.boundaryMap t) ∂circleMeasure) = 0 := by
  have hs := sum_integral_eq_zero_of_null_homology (fun _ : Fin 1 => C.boundaryContour)
    (fun _ => (1 : ℂ)) hV (fun _ => C.boundaryContour_trace_subset.trans
      (frontier_subset_closure.trans hUV))
    (U := V) (fun (w : ℂ) (hw : w ∉ V) => by
      simpa using C.boundaryContour_index_outside hc (z := w)
        (fun hwc => hw (hUV hwc))) hg
  simp only [Fin.sum_univ_one, one_smul] at hs
  change (∫ t, C.boundaryNormal t • g (C.boundaryMap t) ∂circleMeasure) = 0
  rw [← C.boundaryContour_integral g]
  exact hs

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
