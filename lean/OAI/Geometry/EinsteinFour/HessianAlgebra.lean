import OAI.Geometry.EinsteinFour.Matrix
import OAI.Geometry.EinsteinFour.QuarticEnergy
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI

/-!
# Finite algebra in the weighted Hessian inequality

These are the energy metric, compressed curvature action, matrix (12), and
sharp scalar optimization in (13). The manifold Hessian and its integration
by parts are separate from these finite-dimensional identities.
-/

namespace PositiveEinsteinFour.HessianAlgebra

noncomputable section

/-- The energy metric of the three Bianchi parameters. -/
def energy (p k l : ℝ) : ℝ := (5 / 3) * p ^ 2 + 5 * k ^ 2 + l ^ 2

/-- The quadratic form of the compressed matrix-slot action, normalized by
`|Z|² / 6`. -/
def curvatureForm (v σ ρ p k l : ℝ) : ℝ :=
  v * ((4 / 3) * σ * p ^ 2 - 8 * ρ / Real.sqrt 3 * p * k -
    4 * σ * k ^ 2 - 2 * k * l)

/-- The analogous form of the trace-free square of the Weyl block. -/
def squareCurvatureForm (v σ ρ p k l : ℝ) : ℝ :=
  v ^ 2 * ((4 / 3) * p ^ 2 - 2 * ρ / Real.sqrt 3 * p * l -
    4 * k ^ 2 - 2 * σ * k * l)

/-- First component of `H⁻¹ B`, for `H = diag(5/3,5,1)`. -/
def actionP (v σ ρ p k : ℝ) : ℝ :=
  v * ((4 / 5) * σ * p - (12 / 5) * ρ / Real.sqrt 3 * k)

/-- Second component of `H⁻¹ B`. -/
def actionK (v σ ρ p k l : ℝ) : ℝ :=
  v * (-(4 / 5) * ρ / Real.sqrt 3 * p - (4 / 5) * σ * k - l / 5)

/-- Last component of `H⁻¹ B`. -/
def actionL (v k : ℝ) : ℝ := -v * k

/-- The compressed operator is represented by the curvature bilinear form
in the energy metric. -/
theorem energy_pair_action (v σ ρ p k l p' k' l' : ℝ) :
    (5 / 3) * actionP v σ ρ p k * p' +
        5 * actionK v σ ρ p k l * k' + actionL v k * l' =
      v * ((4 / 3) * σ * p * p' - 4 * ρ / Real.sqrt 3 * (p * k' + k * p') -
        4 * σ * k * k' - k * l' - l * k') := by
  unfold actionP actionK actionL
  ring

/-- The matrix of the squared operator is `B H⁻¹ B`, not the ordinary
matrix square. This is the displayed formula for `E_B` before (12). -/
theorem squared_action_energy (v σ ρ p k l : ℝ)
    (hcircle : ρ ^ 2 = 1 - σ ^ 2) :
    energy (actionP v σ ρ p k) (actionK v σ ρ p k l) (actionL v k) =
      v ^ 2 * ((16 / 15) * p ^ 2 + (21 / 5) * k ^ 2 + l ^ 2 / 5 +
        8 * ρ / (5 * Real.sqrt 3) * p * l + (8 / 5) * σ * k * l) := by
  have hsqrt : ((Real.sqrt 3)⁻¹) ^ 2 = (1 / 3 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  unfold energy actionP actionK actionL
  simp only [div_eq_mul_inv]
  linear_combination
    v ^ 2 * ((16 / 15) * p ^ 2 + (16 / 5) * k ^ 2) * hcircle +
    v ^ 2 * ((48 / 5) * ρ ^ 2 * k ^ 2 + (16 / 5) * ρ ^ 2 * p ^ 2) * hsqrt

/-- The invariant scalar expression obtained after the Hessian integration
by parts. -/
def hessianForm (v b σ ρ p k l : ℝ) : ℝ :=
  (-42 - 3 * b ^ 2 - (10 / 3) * v ^ 2) * energy p k l +
    75 * curvatureForm v σ ρ p k l + (25 / 3) * squareCurvatureForm v σ ρ p k l -
    (100 / 3) * energy (actionP v σ ρ p k) (actionK v σ ρ p k l) (actionL v k) +
    5 * v ^ 2 * p ^ 2

/-- Exact matrix (12), with all off-diagonal entries counted twice. -/
theorem hessian_matrix (v b σ ρ p k l : ℝ) (hcircle : ρ ^ 2 = 1 - σ ^ 2) :
    hessianForm v b σ ρ p k l =
      (-70 - 5 * b ^ 2 + 100 * σ * v - 25 * v ^ 2) * p ^ 2 +
      (-210 - 15 * b ^ 2 - 300 * σ * v - 190 * v ^ 2) * k ^ 2 +
      (-42 - 3 * b ^ 2 - 10 * v ^ 2) * l ^ 2 -
      200 * Real.sqrt 3 * ρ * v * p * k -
      70 * ρ * v ^ 2 / Real.sqrt 3 * p * l -
      2 * (75 * v + 35 * σ * v ^ 2) * k * l := by
  unfold hessianForm
  rw [squared_action_energy v σ ρ p k l hcircle]
  unfold energy curvatureForm squareCurvatureForm
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hne]
  ring_nf
  rw [hsqrt]
  ring

/-- The last scalar maximization in the sharp cubic contraction estimate.
Its hypotheses are precisely the energy spent by the distinguished tangent
component, `e₁ = 5ν²/3 ≤ e`. -/
theorem cubic_energy_optimization {ν e : ℝ}
    (_hν : 0 ≤ ν) (he : (5 / 3) * ν ^ 2 ≤ e) :
    ν * (e - ν ^ 2 / 3) ≤
      (4 / 5) * Real.sqrt (3 / 5) * e * Real.sqrt e := by
  have he0 : 0 ≤ e := le_trans (by positivity) he
  let L := Real.sqrt (3 / 5) * Real.sqrt e
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hL2 : L ^ 2 = (3 / 5) * e := by
    dsimp [L]
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt he0]
  have hνL : ν ≤ L := by nlinarith only [_hν, he, hL2, hL]
  have hνLprod : ν * L ≤ L ^ 2 := by nlinarith
  have hgap : 0 ≤ e - (L ^ 2 + L * ν + ν ^ 2) / 3 := by nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hνL) hgap
  have hL3 : L ^ 3 = (3 / 5) * e * L := by rw [pow_succ, hL2]
  calc
    _ ≤ (4 / 5) * L * e := by nlinarith
    _ = _ := by dsimp [L]; ring

/-- Positive operator square underlying (11), before integration. -/
theorem weighted_operator_square
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E)
    (hsymm : ∀ x y, inner ℝ (P x) y = inner ℝ (P y) x)
    (hpos : ∀ x, 0 ≤ inner ℝ (P x) x)
    {m : ℝ} (hm : 0 < m) (Y L : E) :
    0 ≤ m / 6 * inner ℝ (P Y) Y + inner ℝ (P Y) L / 6 +
      inner ℝ (P L) L / (24 * m) := by
  have h := mul_nonneg (show 0 ≤ m / 6 by positivity)
    (hpos (Y + (1 / (2 * m)) • L))
  convert h using 1
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hsymm L Y]
  field_simp [ne_of_gt hm]
  ring

/-- The mixed radial/defect cost is controlled by an explicit square. The
statement retains the actual tangent inner products. -/
theorem projection_bracket_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v y σ ρ : ℝ} (hv : 0 ≤ v) (hσ : σ ≤ 1) (p k l : E) :
    (7 / 12) * (4 + y) * ((5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) -
      (5 / 4) * v * ((4 / 3) * σ * ‖p‖ ^ 2 -
        8 * ρ / Real.sqrt 3 * inner ℝ p k - 4 * σ * ‖k‖ ^ 2 - 2 * inner ℝ k l) ≤
    QuarticEnergy.projectionCoefficient v y σ ρ * ((5 / 3) * ‖p‖ ^ 2) +
      Energy.defectCoefficient v y * (5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) := by
  have hpure : 0 ≤ v * ((5 / 4) * ‖l - k‖ ^ 2 + 5 * (1 - σ) * ‖k‖ ^ 2) := by
    positivity
  have hmix : 0 ≤ 5 * ‖(ρ * v / (2 * Real.sqrt 3)) • p - (2 : ℝ) • k‖ ^ 2 := by
    positivity
  have hl : 0 ≤ 4 * ‖l‖ ^ 2 := by positivity
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right] at hpure hmix
  rw [show inner ℝ l k = inner ℝ k l from real_inner_comm k l] at hpure
  unfold QuarticEnergy.projectionCoefficient Energy.defectCoefficient
  have hidentity :
      QuarticEnergy.projectionCoefficient v y σ ρ * ((5 / 3) * ‖p‖ ^ 2) +
        Energy.defectCoefficient v y * (5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) -
      ((7 / 12) * (4 + y) * ((5 / 3) * ‖p‖ ^ 2 + 5 * ‖k‖ ^ 2 + ‖l‖ ^ 2) -
        (5 / 4) * v * ((4 / 3) * σ * ‖p‖ ^ 2 -
          8 * ρ / Real.sqrt 3 * inner ℝ p k - 4 * σ * ‖k‖ ^ 2 - 2 * inner ℝ k l)) =
      v * ((5 / 4) * (‖l‖ ^ 2 - 2 * inner ℝ k l + ‖k‖ ^ 2) +
        5 * (1 - σ) * ‖k‖ ^ 2) +
      5 * ((ρ * v / (2 * Real.sqrt 3)) ^ 2 * ‖p‖ ^ 2 -
        2 * (ρ * v / (2 * Real.sqrt 3)) * 2 * inner ℝ p k + 4 * ‖k‖ ^ 2) +
      4 * ‖l‖ ^ 2 := by
    unfold QuarticEnergy.projectionCoefficient Energy.defectCoefficient
    field_simp [hne]
    ring_nf
    rw [hsqrt]
    ring
  unfold QuarticEnergy.projectionCoefficient Energy.defectCoefficient at hidentity
  linarith

end
end PositiveEinsteinFour.HessianAlgebra

end OAI
