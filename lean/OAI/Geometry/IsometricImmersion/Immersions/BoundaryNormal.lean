import OAI.Geometry.IsometricImmersion.Calculus.NormalDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def coordinateCircle (center : Coord) (radius : ℝ) (t : ℝ) : Coord :=
  center + radius • ![Real.cos t, Real.sin t]

def coordinateCircleVelocity (radius : ℝ) (t : ℝ) : Coord :=
  radius • ![-Real.sin t, Real.cos t]

theorem coordinateCircle_contDiff (center : Coord) (radius : ℝ) :
    ContDiff ℝ ∞ (coordinateCircle center radius) := by
  have hpair : ContDiff ℝ ∞ (fun t : ℝ => (![Real.cos t, Real.sin t] : Coord)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ Real.cos
      exact Real.contDiff_cos
    · change ContDiff ℝ ∞ Real.sin
      exact Real.contDiff_sin
  exact contDiff_const.add (ContDiff.const_smul radius hpair)

theorem coordinateCircle_hasDerivAt (center : Coord) (radius t : ℝ) :
    HasDerivAt (coordinateCircle center radius) (coordinateCircleVelocity radius t) t := by
  have hpair : HasDerivAt (fun s : ℝ => (![Real.cos s, Real.sin s] : Coord))
      (![-Real.sin t, Real.cos t] : Coord) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasDerivAt Real.cos (-Real.sin t) t
      exact Real.hasDerivAt_cos t
    · change HasDerivAt Real.sin (Real.cos t) t
      exact Real.hasDerivAt_sin t
  change HasDerivAt (fun s : ℝ => center + radius • (![Real.cos s, Real.sin s] : Coord))
    (radius • (![-Real.sin t, Real.cos t] : Coord)) t
  simpa only [Pi.add_def, Pi.smul_def, zero_add] using
    (hasDerivAt_const t center).add (HasDerivAt.const_smul radius hpair)

theorem coordinateCircle_equation (center : Coord) (radius t : ℝ) :
    (coordinateCircle center radius t 0 - center 0) ^ 2 +
      (coordinateCircle center radius t 1 - center 1) ^ 2 = radius ^ 2 := by
  calc
    _ = radius ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by
      simp only [coordinateCircle, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    _ = radius ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

variable {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
variable {center : Coord} {radius : ℝ}

theorem unitNormalField_circle_hasDerivAt_zero
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U)
    (hII : ∀ t, secondFundamental F
      (unitNormalField F (coordinateCircle center radius t))
      (coordinateCircle center radius t) = 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => unitNormalField F (coordinateCircle center radius s)) 0 t := by
  have hn := unitNormalField_contDiffOn hg hF hU
  have hd : DifferentiableAt ℝ (unitNormalField F) (coordinateCircle center radius t) :=
    (((hn _ (hcircle t)).contDiffAt (hU.mem_nhds (hcircle t))).differentiableAt (by simp))
  have hzero := unitNormalField_fderiv_eq_zero_of_secondFundamental_eq_zero
    hg hF hU (hcircle t) (hII t)
  simpa only [Function.comp_def, hzero, zero_apply] using
    hd.hasFDerivAt.comp_hasDerivAt t (coordinateCircle_hasDerivAt center radius t)

theorem unitNormalField_circle_constant
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U)
    (hII : ∀ t, secondFundamental F
      (unitNormalField F (coordinateCircle center radius t))
      (coordinateCircle center radius t) = 0) (s t : ℝ) :
    unitNormalField F (coordinateCircle center radius s) =
      unitNormalField F (coordinateCircle center radius t) := by
  have hd := unitNormalField_circle_hasDerivAt_zero hg hF hU hcircle hII
  exact is_const_of_deriv_eq_zero (fun a => (hd a).differentiableAt)
    (fun a => (hd a).deriv) s t

theorem height_circle_hasDerivAt_zero
    (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U) (e : Ambient)
    (he : ∀ t, IsUnitNormalAt F e (coordinateCircle center radius t)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => height F e (coordinateCircle center radius s)) 0 t := by
  have hh := height_smooth hF.1 e
  have hd : DifferentiableAt ℝ (height F e) (coordinateCircle center radius t) :=
    (((hh _ (hcircle t)).contDiffAt (hU.mem_nhds (hcircle t))).differentiableAt (by simp))
  have hzero := height_derivative_at_normal hF.1 hU (hcircle t) (he t)
  simpa only [Function.comp_def, hzero, zero_apply] using
    hd.hasFDerivAt.comp_hasDerivAt t (coordinateCircle_hasDerivAt center radius t)

theorem height_circle_constant
    (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U) (e : Ambient)
    (he : ∀ t, IsUnitNormalAt F e (coordinateCircle center radius t)) (s t : ℝ) :
    height F e (coordinateCircle center radius s) =
      height F e (coordinateCircle center radius t) := by
  have hd := height_circle_hasDerivAt_zero hF hU hcircle e he
  exact is_const_of_deriv_eq_zero (fun a => (hd a).differentiableAt)
    (fun a => (hd a).deriv) s t

theorem exists_circle_constant_normal_and_height
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U) (hU : IsOpen U)
    (hcircle : ∀ t, coordinateCircle center radius t ∈ U)
    (hII : ∀ t, secondFundamental F
      (unitNormalField F (coordinateCircle center radius t))
      (coordinateCircle center radius t) = 0) :
    ∃ e : Ambient, ∃ c : ℝ, inner ℝ e e = 1 ∧
      (∀ t, unitNormalField F (coordinateCircle center radius t) = e) ∧
      (∀ t, IsUnitNormalAt F e (coordinateCircle center radius t)) ∧
      (∀ t, height F e (coordinateCircle center radius t) = c) := by
  let e := unitNormalField F (coordinateCircle center radius 0)
  have hconst (t : ℝ) : unitNormalField F (coordinateCircle center radius t) = e :=
    unitNormalField_circle_constant hg hF hU hcircle hII t 0
  have he (t : ℝ) : IsUnitNormalAt F e (coordinateCircle center radius t) := by
    rw [← hconst t]
    exact unitNormalField_isUnitNormalAt hg hF (hcircle t)
  refine ⟨e, height F e (coordinateCircle center radius 0), (he 0).1, hconst, he, ?_⟩
  intro t
  exact height_circle_constant hF hU hcircle e he t 0

end SmoothLocal.Geometry

end

end OAI
