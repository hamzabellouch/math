import OAI.Geometry.IsometricImmersion.Metric
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model
open SmoothLocal.Geometry

def squareTransition (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1)

theorem squareTransition_contDiff : ContDiff ℝ ∞ squareTransition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem squareTransition_range (t : ℝ) :
    0 ≤ squareTransition t ∧ squareTransition t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem squareTransition_zero {t : ℝ} (ht : t ≤ 1 / 4) : squareTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem squareTransition_one {t : ℝ} (ht : 1 / 2 ≤ t) : squareTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem squareTransition_monotone : Monotone squareTransition := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem squareTransition_deriv_nonneg (t : ℝ) : 0 ≤ deriv squareTransition t :=
  squareTransition_monotone.deriv_nonneg

def modelProfile (y : ℝ) : ℝ := 1 - y ^ 2 * squareTransition (y ^ 2)

theorem modelProfile_contDiff : ContDiff ℝ ∞ modelProfile :=
  contDiff_const.sub ((contDiff_id.pow 2).mul
    (squareTransition_contDiff.comp (contDiff_id.pow 2)))

theorem modelProfile_even : Function.Even modelProfile := by
  intro y
  simp [modelProfile]

theorem modelProfile_plateau {y : ℝ} (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    modelProfile y = 1 := by
  have hs : y ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := sq_le_sq' hy.1 hy.2
  have hz := squareTransition_zero (t := y ^ 2) (by nlinarith)
  simp [modelProfile, hz]

theorem modelProfile_bounds (y : ℝ) : 1 - y ^ 2 ≤ modelProfile y ∧ modelProfile y ≤ 1 := by
  have hh := squareTransition_range (y ^ 2)
  have hprod := mul_le_mul_of_nonneg_left hh.2 (sq_nonneg y)
  have hprod0 := mul_nonneg (sq_nonneg y) hh.1
  unfold modelProfile
  constructor <;> nlinarith

theorem modelProfile_pos_inside {y : ℝ} (hy : |y| < 1) : 0 < modelProfile y := by
  have hs : y ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one y).mpr hy
  linarith [(modelProfile_bounds y).1]

theorem modelProfile_eq_one_sub_sq {y : ℝ} (hy : 1 / 2 ≤ y ^ 2) :
    modelProfile y = 1 - y ^ 2 := by
  simp [modelProfile, squareTransition_one hy]

theorem modelProfile_neg_outside {y : ℝ} (hy : 1 < |y|) : modelProfile y < 0 := by
  have hs : 1 < y ^ 2 := (one_lt_sq_iff_one_lt_abs y).mpr hy
  rw [modelProfile_eq_one_sub_sq (by linarith : 1 / 2 ≤ y ^ 2)]
  linarith

theorem modelProfile_one : modelProfile 1 = 0 := by
  rw [modelProfile_eq_one_sub_sq (by norm_num : (1 / 2 : ℝ) ≤ (1 : ℝ) ^ 2)]
  norm_num

theorem modelProfile_hasDerivAt (y : ℝ) :
    HasDerivAt modelProfile
      (-2 * y * squareTransition (y ^ 2) - 2 * y ^ 3 * deriv squareTransition (y ^ 2)) y := by
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    convert (hasDerivAt_id y).pow 2 using 1 <;> first | rfl | simp
  have hcut := ((squareTransition_contDiff.differentiable (by simp)) (y ^ 2)).hasDerivAt.comp y hsq
  have hp := (hsq.mul hcut).const_sub 1
  convert hp using 1 <;> first | rfl | (dsimp only [Function.comp_def]; ring)

theorem modelProfile_deriv (y : ℝ) :
    deriv modelProfile y =
      -2 * y * squareTransition (y ^ 2) - 2 * y ^ 3 * deriv squareTransition (y ^ 2) :=
  (modelProfile_hasDerivAt y).deriv

theorem modelProfile_deriv_nonpos {y : ℝ} (hy : 0 ≤ y) : deriv modelProfile y ≤ 0 := by
  rw [modelProfile_deriv]
  have hfirst : 0 ≤ 2 * y * squareTransition (y ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hy) (squareTransition_range _).1
  have hsecond : 0 ≤ 2 * y ^ 3 * deriv squareTransition (y ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hy _)) (squareTransition_deriv_nonneg _)
  linarith

theorem modelProfile_deriv_one_neg : deriv modelProfile 1 < 0 := by
  rw [modelProfile_deriv]
  have hc := squareTransition_one (t := 1) (by norm_num)
  have hd := squareTransition_deriv_nonneg 1
  norm_num only [one_pow]
  rw [hc]
  nlinarith only [hd]

theorem modelProfile_spec :
    ContDiff ℝ ∞ modelProfile ∧ Function.Even modelProfile ∧
    (∀ y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), modelProfile y = 1) ∧
    (∀ y ∈ Ici (0 : ℝ), deriv modelProfile y ≤ 0) ∧
    (∀ y ∈ Ioo (-1 : ℝ) 1, 0 < modelProfile y) ∧
    (∀ y : ℝ, 1 < |y| → modelProfile y < 0) ∧
    modelProfile 1 = 0 ∧ deriv modelProfile 1 < 0 :=
  ⟨modelProfile_contDiff, modelProfile_even, fun _ hy => modelProfile_plateau hy,
    fun _ hy => modelProfile_deriv_nonpos hy,
    fun _ hy => modelProfile_pos_inside (abs_lt.mpr hy),
    fun _ hy => modelProfile_neg_outside hy, modelProfile_one, modelProfile_deriv_one_neg⟩

def modelCurvature (kappa : ℝ) (p : Coord) : ℝ :=
  kappa * ((p 0) ^ 2 - modelProfile (p 1))

theorem modelCurvature_contDiff (kappa : ℝ) : ContDiff ℝ ∞ (modelCurvature kappa) :=
  contDiff_const.mul (((contDiff_apply ℝ ℝ 0).pow 2).sub
    (modelProfile_contDiff.comp (contDiff_apply ℝ ℝ 1)))

theorem modelCurvature_central_square {kappa : ℝ} (hkappa : 0 < kappa) {p : Coord}
    (hp : ∀ i : Fin 2, p i ∈ Icc (-(1 / 5 : ℝ)) (1 / 5)) :
    modelCurvature kappa p < -kappa / 2 := by
  have hplateau : modelProfile (p 1) = 1 := modelProfile_plateau
    ⟨by linarith [(hp 1).1], by linarith [(hp 1).2]⟩
  have hx : (p 0) ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := sq_le_sq' (hp 0).1 (hp 0).2
  have hmul := mul_le_mul_of_nonneg_left hx hkappa.le
  unfold modelCurvature
  rw [hplateau]
  nlinarith

theorem modelCurvature_pos_lateral {kappa : ℝ} (hkappa : 0 < kappa) {p : Coord}
    (hp : 1 < |p 0|) : 0 < modelCurvature kappa p := by
  have hx : 1 < (p 0) ^ 2 := (one_lt_sq_iff_one_lt_abs _).mpr hp
  apply mul_pos hkappa
  linarith [(modelProfile_bounds (p 1)).2]

theorem modelCurvature_lateral_band_lower {kappa : ℝ} (hkappa : 0 < kappa) {p : Coord}
    (hp : 3 / 2 < |p 0|) : 5 / 4 * kappa < modelCurvature kappa p := by
  have hx : (3 / 2 : ℝ) ^ 2 < (p 0) ^ 2 := sq_lt_sq.mpr (by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    exact hp)
  have hmul := mul_lt_mul_of_pos_left hx hkappa
  have hh := mul_le_mul_of_nonneg_left (modelProfile_bounds (p 1)).2 hkappa.le
  unfold modelCurvature
  nlinarith

theorem modelCurvature_pos_transverse {kappa : ℝ} (hkappa : 0 < kappa) {p : Coord}
    (hp : 1 < |p 1|) : 0 < modelCurvature kappa p := by
  have hh := modelProfile_neg_outside hp
  apply mul_pos hkappa
  linarith [sq_nonneg (p 0)]

theorem modelCurvature_pos_lower_flow_band {kappa y s t : ℝ} (hkappa : 0 < kappa)
    (hys : |y - s| ≤ 1 / 50) (hs : s < -3 / 2) :
    0 < modelCurvature kappa ![t, y] := by
  have hy : y < -1 := by linarith [(abs_le.mp hys).2]
  apply modelCurvature_pos_transverse hkappa
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [abs_of_neg (by linarith : y < 0)]
  linarith

theorem modelCurvature_abs_le_model_square {kappa : ℝ} (hkappa : 0 ≤ kappa) {p : Coord}
    (hp : ∀ i : Fin 2, p i ∈ Icc (-3 : ℝ) 3) :
    |modelCurvature kappa p| ≤ 17 * kappa := by
  have hx : (p 0) ^ 2 ≤ (3 : ℝ) ^ 2 := sq_le_sq' (hp 0).1 (hp 0).2
  have hy : (p 1) ^ 2 ≤ (3 : ℝ) ^ 2 := sq_le_sq' (hp 1).1 (hp 1).2
  have hh := modelProfile_bounds (p 1)
  have habs : |(p 0) ^ 2 - modelProfile (p 1)| ≤ 17 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (p 0)]
  unfold modelCurvature
  rw [abs_mul, abs_of_nonneg hkappa]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left habs hkappa

end SmoothLocal.Model

end

end OAI
