import OAI.Geometry.EinsteinFour.Defect
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-!
# Removal of the energy defects

The right side of equation (19) is kept as an actual function of its two
energies. Its derivative estimate uses the scalar discriminant; continuity supplies
the zero-energy endpoints.
-/

namespace PositiveEinsteinFour.Energy

open Defect

noncomputable section

def scalarWeight (v b : ℝ) : ℝ := 1 - 3 * (v - b) / 8

def gradientSum (e0 f0 : ℝ) : ℝ :=
  Real.sqrt (3 / 5) * (Real.sqrt e0 + Real.sqrt f0)

/-- The actual right side of equation (19), with the two fixed radial energies
`e0`, `f0` and variable total energies `e`, `f`. -/
def quarticEnergy (v b e0 f0 g gb H Hb e f : ℝ) : ℝ :=
  (1 / 2) * Real.sqrt (3 / 5) * gradientSum e0 f0 *
      (scalarWeight v b * (e * Real.sqrt e) + scalarWeight b v * (f * Real.sqrt f)) +
    (9 / 64) * (gradientSum e0 f0) ^ 2 *
      (g * e0 + gb * f0 + H * (e - e0) + Hb * (f - f0)) -
    (17 / 10) * (e + f) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b)

/-- The homogeneous form of the strict scalar discriminant estimate. -/
theorem homogeneous_derivative_nonpos
    {v : ℝ} (hv : 0 < v) (hv2 : v < 2) (r s : ℝ) :
    A0 v * (r + s) ^ 2 + L0 v * r * (r + s) -
      (17 / 10) * ((7 / 5) * r ^ 2 + (1 + 2 * v / (5 * (2 - v))) * s ^ 2) ≤ 0 := by
  by_cases hr : r = 0
  · subst r
    have hv_sq : v ^ 2 ≤ 4 := by nlinarith
    have hA : A0 v ≤ 477 / 320 := by
      unfold A0
      nlinarith
    have hsub : 0 < 2 - v := by linarith
    have hden : 0 < 5 * (2 - v) := by positivity
    have hfrac : 0 ≤ 2 * v / (5 * (2 - v)) := by positivity
    have hcoef : A0 v - (17 / 10) * (1 + 2 * v / (5 * (2 - v))) ≤ 0 := by
      linarith
    have h := mul_nonpos_of_nonpos_of_nonneg hcoef (sq_nonneg s)
    nlinarith
  · have h := energy_defect_derivative_neg hv hv2 (s / r)
    have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) (le_of_lt h)
    have hid : r ^ 2 * (A0 v * (1 + s / r) ^ 2 + L0 v * (1 + s / r) -
        (17 / 10) * (7 / 5 + (1 + 2 * v / (5 * (2 - v))) * (s / r) ^ 2)) =
        A0 v * (r + s) ^ 2 + L0 v * r * (r + s) -
          (17 / 10) * ((7 / 5) * r ^ 2 +
            (1 + 2 * v / (5 * (2 - v))) * s ^ 2) := by
      field_simp [hr, ne_of_gt (sub_pos.mpr hv2)]
    rwa [hid] at hm

private theorem hasDerivAt_mul_sqrt {e : ℝ} (he : 0 < e) :
    HasDerivAt (fun x : ℝ => x * Real.sqrt x) ((3 / 2) * Real.sqrt e) e := by
  have h := (hasDerivAt_id e).mul (Real.hasDerivAt_sqrt (ne_of_gt he))
  simp only [id_eq, one_mul] at h
  convert h using 1
  · ext x
    rfl
  · have hs : Real.sqrt e ≠ 0 := ne_of_gt (Real.sqrt_pos.2 he)
    field_simp [hs]
    nlinarith [Real.sq_sqrt he.le]

/-- The derivative with respect to the first energy, for positive first energy. -/
theorem quarticEnergy_hasDerivAt_left
    (v b e0 f0 g gb H Hb f : ℝ) {e : ℝ} (he : 0 < e) :
    HasDerivAt (fun x => quarticEnergy v b e0 f0 g gb H Hb x f)
      ((3 / 4) * Real.sqrt (3 / 5) * gradientSum e0 f0 * scalarWeight v b * Real.sqrt e +
        (9 / 64) * (gradientSum e0 f0) ^ 2 * H -
        (17 / 10) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v)) e := by
  have hfirst := ((hasDerivAt_mul_sqrt he).const_mul (scalarWeight v b)).add_const
    (scalarWeight b v * (f * Real.sqrt f))
  have hsecond := (((hasDerivAt_id e).sub_const e0).const_mul H).add_const
    (g * e0 + gb * f0 + Hb * (f - f0))
  have hthird := ((hasDerivAt_id e).add_const f).mul
    ((((hasDerivAt_id e).sub_const ((3 / 5) * e0)).div_const v).add_const
      ((f - (3 / 5) * f0) / b))
  convert ((hfirst.const_mul ((1 / 2) * Real.sqrt (3 / 5) * gradientSum e0 f0)).add
    (hsecond.const_mul ((9 / 64) * (gradientSum e0 f0) ^ 2))).sub
    (hthird.const_mul (17 / 10)) using 1
  · ext x
    unfold quarticEnergy
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  · simp only [id_eq]
    ring

/-- The actual first-energy derivative in (19) is nonpositive. The elementary
bounds on `H` are exactly the displayed bounds for the defect coefficient. -/
theorem quarticEnergy_left_derivative_nonpos
    {v b e0 f0 H e f : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2)
    (he0 : 0 ≤ e0) (hf0 : 0 ≤ f0) (he : e0 ≤ e) (hf : f0 ≤ f)
    (hH0 : 0 ≤ H) (hH : H ≤ 15 / 2 + 2 * v / 3) :
    (3 / 4) * Real.sqrt (3 / 5) * gradientSum e0 f0 * scalarWeight v b * Real.sqrt e +
      (9 / 64) * (gradientSum e0 f0) ^ 2 * H -
      (17 / 10) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v) ≤ 0 := by
  have hv2 : v < 2 := by linarith
  have he_nonneg : 0 ≤ e := le_trans he0 he
  have hf_nonneg : 0 ≤ f := le_trans hf0 hf
  let r := Real.sqrt e
  let s := Real.sqrt f
  let k := Real.sqrt (3 / 5 : ℝ)
  let z := gradientSum e0 f0
  have hr : 0 ≤ r := Real.sqrt_nonneg e
  have hs : 0 ≤ s := Real.sqrt_nonneg f
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hk_sq : k ^ 2 = (3 / 5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hz : 0 ≤ z := by dsimp [z, gradientSum]; positivity
  have hz_bound : z ≤ k * (r + s) := by
    exact mul_le_mul_of_nonneg_left
      (add_le_add (Real.sqrt_le_sqrt he) (Real.sqrt_le_sqrt hf)) hk
  have hM0 : 0 ≤ scalarWeight v b := by unfold scalarWeight; linarith
  have hM : scalarWeight v b ≤ 7 / 4 - 3 * v / 4 := by
    unfold scalarWeight
    linarith
  have hU : 0 ≤ 7 / 4 - 3 * v / 4 := by linarith
  have hHmax : 0 ≤ 15 / 2 + 2 * v / 3 := by positivity
  have hfirst : (3 / 4) * k * z * scalarWeight v b * r * v ≤
      L0 v * r * (r + s) := by
    calc
      _ ≤ (3 / 4) * k * (k * (r + s)) * (7 / 4 - 3 * v / 4) * r * v := by
        gcongr
      _ = ((3 / 4) * k ^ 2 * (7 / 4 - 3 * v / 4) * v) * r * (r + s) := by ring
      _ = _ := by rw [hk_sq]; unfold L0; ring
  have hsecond : (9 / 64) * z ^ 2 * H * v ≤ A0 v * (r + s) ^ 2 := by
    calc
      _ ≤ (9 / 64) * (k * (r + s)) ^ 2 * (15 / 2 + 2 * v / 3) * v := by
        gcongr
      _ = (9 / 64) * k ^ 2 * (r + s) ^ 2 * (15 / 2 + 2 * v / 3) * v := by ring
      _ = _ := by rw [hk_sq]; unfold A0; ring
  have hratio : v / (2 - v) ≤ v / b := by
    apply div_le_div_of_nonneg_left hv.le hb
    linarith
  have hradial : (7 / 5) * e + (1 + 2 * v / (5 * (2 - v))) * f ≤
      v * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v) := by
    calc
      _ = (7 / 5) * e + f + (v / (2 - v)) * ((2 / 5) * f) := by
        field_simp [ne_of_gt (sub_pos.mpr hv2)]
        ring
      _ ≤ (7 / 5) * e + f + (v / b) * ((2 / 5) * f) := by gcongr
      _ ≤ 2 * e + f - (3 / 5) * e0 + (v / b) * (f - (3 / 5) * f0) := by
        gcongr <;> linarith
      _ = _ := by field_simp [ne_of_gt hv, ne_of_gt hb]; ring
  have hhom := homogeneous_derivative_nonpos hv hv2 r s
  have hre : r ^ 2 = e := Real.sq_sqrt he_nonneg
  have hsf : s ^ 2 = f := Real.sq_sqrt hf_nonneg
  have hscaled : v *
      ((3 / 4) * k * z * scalarWeight v b * r + (9 / 64) * z ^ 2 * H -
        (17 / 10) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v)) ≤ 0 := by
    have hcomparison : v *
        ((3 / 4) * k * z * scalarWeight v b * r + (9 / 64) * z ^ 2 * H -
          (17 / 10) * ((e - (3 / 5) * e0) / v + (f - (3 / 5) * f0) / b + (e + f) / v)) ≤
        A0 v * (r + s) ^ 2 + L0 v * r * (r + s) -
          (17 / 10) * ((7 / 5) * r ^ 2 + (1 + 2 * v / (5 * (2 - v))) * s ^ 2) := by
      rw [hre, hsf]
      nlinarith only [hfirst, hsecond, hradial]
    exact le_trans hcomparison hhom
  exact nonpos_of_mul_nonpos_right hscaled hv

/-- Monotonicity in the first defect, including a zero radial-energy endpoint. -/
theorem quarticEnergy_left_antitone
    {v b e0 f0 H e f : ℝ} (g gb Hb : ℝ)
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2)
    (he0 : 0 ≤ e0) (hf0 : 0 ≤ f0) (he : e0 ≤ e) (hf : f0 ≤ f)
    (hH0 : 0 ≤ H) (hH : H ≤ 15 / 2 + 2 * v / 3) :
    quarticEnergy v b e0 f0 g gb H Hb e f ≤
      quarticEnergy v b e0 f0 g gb H Hb e0 f := by
  have hc : Continuous (fun x => quarticEnergy v b e0 f0 g gb H Hb x f) := by
    unfold quarticEnergy
    fun_prop
  have hantitone : AntitoneOn (fun x => quarticEnergy v b e0 f0 g gb H Hb x f)
      (Set.Ici e0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici e0) hc.continuousOn
    · intro x hx
      rw [interior_Ici] at hx
      exact (quarticEnergy_hasDerivAt_left v b e0 f0 g gb H Hb f
        (lt_of_le_of_lt he0 hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(quarticEnergy_hasDerivAt_left v b e0 f0 g gb H Hb f
        (lt_of_le_of_lt he0 hx)).deriv]
      exact quarticEnergy_left_derivative_nonpos hv hb hsum he0 hf0 hx.le hf hH0 hH
  exact hantitone (by simp) he he

/-- Exchanging the two Weyl blocks preserves the energy expression. -/
theorem quarticEnergy_swap (v b e0 f0 g gb H Hb e f : ℝ) :
    quarticEnergy v b e0 f0 g gb H Hb e f =
      quarticEnergy b v f0 e0 gb g Hb H f e := by
  unfold quarticEnergy gradientSum
  ring

/-- The full removal of both nonnegative energy defects in equation (19).
The coefficient bounds are the elementary pointwise bounds displayed before
the manuscript's scalar discriminant calculation; all zero-energy cases are
included by continuity. -/
theorem remove_energy_defects
    {v b e0 f0 H Hb e f : ℝ} (g gb : ℝ)
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2)
    (he0 : 0 ≤ e0) (hf0 : 0 ≤ f0) (he : e0 ≤ e) (hf : f0 ≤ f)
    (hH0 : 0 ≤ H) (hH : H ≤ 15 / 2 + 2 * v / 3)
    (hHb0 : 0 ≤ Hb) (hHb : Hb ≤ 15 / 2 + 2 * b / 3) :
    quarticEnergy v b e0 f0 g gb H Hb e f ≤
      quarticEnergy v b e0 f0 g gb H Hb e0 f0 := by
  calc
    _ ≤ quarticEnergy v b e0 f0 g gb H Hb e0 f :=
      quarticEnergy_left_antitone g gb Hb hv hb hsum he0 hf0 he hf hH0 hH
    _ = quarticEnergy b v f0 e0 gb g Hb H f e0 := quarticEnergy_swap _ _ _ _ _ _ _ _ _ _
    _ ≤ quarticEnergy b v f0 e0 gb g Hb H f0 e0 :=
      quarticEnergy_left_antitone gb g H hb hv (by linarith) hf0 he0 hf le_rfl hHb0 hHb
    _ = _ := (quarticEnergy_swap _ _ _ _ _ _ _ _ _ _).symm

/-- The defect coefficient `H_d` in equation (19). -/
def defectCoefficient (v y : ℝ) : ℝ := (7 / 12) * (4 + y) + (5 / 4) * v + 4

/-- The elementary sectional-domain bounds for the coefficient `H_d`. -/
theorem defectCoefficient_bounds {v y : ℝ}
    (hv : 0 ≤ v) (hy : 0 ≤ y) (hsum : v + y ≤ 2) :
    0 ≤ defectCoefficient v y ∧ defectCoefficient v y ≤ 15 / 2 + 2 * v / 3 := by
  unfold defectCoefficient
  constructor <;> linarith

/-- Removal of defects with the actual curvature coefficient `H_d` on the
sectional-positivity domain. -/
theorem remove_energy_defects_from_spectral_bounds
    {v b x y e0 f0 e f : ℝ} (g gb : ℝ)
    (hv : 0 < v) (hb : 0 < b) (hvx : v ≤ x) (hby : b ≤ y) (hxy : x + y ≤ 2)
    (he0 : 0 ≤ e0) (hf0 : 0 ≤ f0) (he : e0 ≤ e) (hf : f0 ≤ f) :
    quarticEnergy v b e0 f0 g gb (defectCoefficient v y) (defectCoefficient b x) e f ≤
      quarticEnergy v b e0 f0 g gb (defectCoefficient v y) (defectCoefficient b x) e0 f0 := by
  have hH := defectCoefficient_bounds (v := v) (y := y) hv.le (by linarith) (by linarith)
  have hHb := defectCoefficient_bounds (v := b) (y := x) hb.le (by linarith) (by linarith)
  exact remove_energy_defects g gb hv hb (by linarith) he0 hf0 he hf hH.1 hH.2 hHb.1 hHb.2

end
end PositiveEinsteinFour.Energy

end OAI
