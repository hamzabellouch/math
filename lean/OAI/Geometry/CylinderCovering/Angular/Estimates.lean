import Mathlib

namespace OAI

namespace AngularEstimates

theorem squared_secant_identity (l r : ℝ) :
    2 * ((1 + l * r) / 2) - ((l + r) / 2) ^ 2 =
      1 - (r - l) ^ 2 / 4 := by
  ring

theorem ordinary_secant_identity (l r : ℝ) :
    ((l + r) / 4) ^ 2 - (1 + l * r) / 4 + 1 / 4 =
      (r - l) ^ 2 / 16 := by
  ring

theorem sector_midpoint_error {l r S Y : ℝ}
    (hleft : l * S ≤ Y) (hright : Y ≤ r * S) :
    |2 * ((l + r) / 4) * S - Y| ≤ (r - l) * S / 2 := by
  rw [abs_le]
  constructor <;> nlinarith only [hleft, hright]

theorem cartesian_discriminant_identity
    {α β Δ T Y δ S Y₀ : ℝ}
    (hsecant : β ^ 2 - α + 1 / 4 = Δ ^ 2 / 16)
    (hS : S = T - δ * β) (hY : Y₀ = Y - δ * α) :
    T ^ 2 - δ * Y + δ ^ 2 / 4 =
      S ^ 2 + δ * (2 * β * S - Y₀) + δ ^ 2 * Δ ^ 2 / 16 := by
  rw [hS, hY]
  nlinarith only [congrArg (fun x : ℝ => δ ^ 2 * x) hsecant]

theorem cartesian_discriminant_lower
    {α β Δ T Y δ S Y₀ : ℝ}
    (_hΔ : 0 ≤ Δ) (_hS0 : 0 ≤ S)
    (hsecant : β ^ 2 - α + 1 / 4 = Δ ^ 2 / 16)
    (hS : S = T - δ * β) (hY : Y₀ = Y - δ * α)
    (herror : |2 * β * S - Y₀| ≤ Δ * S / 2) :
    (S - |δ| * Δ / 4) ^ 2 ≤ T ^ 2 - δ * Y + δ ^ 2 / 4 := by
  have hprod : |δ * (2 * β * S - Y₀)| ≤ |δ| * (Δ * S / 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left herror (abs_nonneg δ)
  have hid := cartesian_discriminant_identity hsecant hS hY
  have hsq : |δ| ^ 2 = δ ^ 2 := sq_abs δ
  nlinarith only [(abs_le.mp hprod).1, hid, hsq]

theorem cartesian_discriminant_sqrt
    {α β Δ T Y δ S Y₀ : ℝ}
    (hΔ : 0 ≤ Δ) (hS0 : 0 ≤ S)
    (hsecant : β ^ 2 - α + 1 / 4 = Δ ^ 2 / 16)
    (hS : S = T - δ * β) (hY : Y₀ = Y - δ * α)
    (herror : |2 * β * S - Y₀| ≤ Δ * S / 2) :
    S - |δ| * Δ / 4 ≤ Real.sqrt (T ^ 2 - δ * Y + δ ^ 2 / 4) := by
  have h := cartesian_discriminant_lower hΔ hS0 hsecant hS hY herror
  have hQ : 0 ≤ T ^ 2 - δ * Y + δ ^ 2 / 4 :=
    (sq_nonneg _).trans h
  by_cases hsign : 0 ≤ S - |δ| * Δ / 4
  · exact (Real.le_sqrt hsign hQ).2 h
  · exact (le_of_not_ge hsign).trans (Real.sqrt_nonneg _)

theorem selected_sector_sqrt {l r T Y δ S : ℝ}
    (hlr : l ≤ r) (hS0 : 0 ≤ S)
    (hS : S = T - δ * ((l + r) / 4))
    (hleft : l * S ≤ Y - δ * ((1 + l * r) / 4))
    (hright : Y - δ * ((1 + l * r) / 4) ≤ r * S) :
    S - |δ| * (r - l) / 4 ≤ Real.sqrt (T ^ 2 - δ * Y + δ ^ 2 / 4) := by
  exact cartesian_discriminant_sqrt (sub_nonneg.mpr hlr) hS0
    (ordinary_secant_identity l r) hS rfl (sector_midpoint_error hleft hright)

theorem cartesian_radial_identity (q : ℝ) :
    (q / 2) ^ 2 / 4 + (q / 2) ^ 4 = (q ^ 2 + q ^ 4) / 16 := by
  ring

theorem cartesian_obstruction_identity (x y η : ℝ) :
    (x ^ 2 / 4 + x ^ 4) + (y ^ 2 / 4 + y ^ 4) + η -
      (x ^ 2 + y ^ 2) / 4 - 2 * x ^ 2 * y ^ 2 =
      (x ^ 2 - y ^ 2) ^ 2 + η := by
  ring

theorem cartesian_obstruction_positive (x y : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < (x ^ 2 / 4 + x ^ 4) + (y ^ 2 / 4 + y ^ 4) + η -
      (x ^ 2 + y ^ 2) / 4 - 2 * x ^ 2 * y ^ 2 := by
  rw [cartesian_obstruction_identity]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) hη

theorem squared_radius_obstruction (x y : ℝ) :
    x ^ 2 + y ^ 2 + 8 * x ^ 2 * y ^ 2 ≤
      x ^ 2 + y ^ 2 + 4 * (x ^ 4 + y ^ 4) := by
  nlinarith only [sq_nonneg (x ^ 2 - y ^ 2)]

theorem cartesian_polynomial_bound {Y : ℝ} (hY : |Y| ≤ 3 / 2) :
    0 ≤ Y ^ 2 / 4 + Y ^ 4 ∧ Y ^ 2 / 4 + Y ^ 4 ≤ 45 / 8 := by
  have hsq : Y ^ 2 ≤ 9 / 4 := by
    nlinarith only [(abs_le.mp hY).1, (abs_le.mp hY).2]
  have hfour : Y ^ 4 ≤ 81 / 16 := by
    nlinarith only [sq_nonneg (Y ^ 2 - 9 / 4), sq_nonneg Y, hsq,
      mul_nonneg (sq_nonneg Y) (sub_nonneg.mpr hsq)]
  constructor
  · positivity
  · linarith

theorem displaced_intercept_bound {Y δ α τ : ℝ}
    (hY : |Y| ≤ 1) (hδ : |δ| ≤ τ) (hτ : τ ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    |Y - δ * α| ≤ 3 / 2 := by
  calc
    |Y - δ * α| ≤ |Y| + |δ * α| := abs_sub _ _
    _ = |Y| + |δ| * α := by rw [abs_mul, abs_of_nonneg hα0]
    _ ≤ 1 + 1 * (1 / 2) := by
      gcongr
      exact hδ.trans hτ
    _ = 3 / 2 := by norm_num

theorem strict_half_of_expansion {ε C : ℝ}
    (hε : 0 < ε) (hsmall : ε ≤ 1 / 2000)
    (hexp : |C - (1 / 2 - (13 / 6000 : ℝ) * ε ^ 2)| ≤ 2 * ε ^ 4) :
    C < 1 / 2 := by
  have hsq : ε ^ 2 ≤ (1 / 2000 : ℝ) ^ 2 :=
    (sq_le_sq₀ hε.le (by norm_num)).2 hsmall
  have hcoef : 2 * ε ^ 2 < (13 / 6000 : ℝ) := by
    norm_num at hsq
    linarith
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos hε) (sub_neg.mpr hcoef)
  nlinarith only [(abs_le.mp hexp).2, hneg]

end AngularEstimates

end OAI
