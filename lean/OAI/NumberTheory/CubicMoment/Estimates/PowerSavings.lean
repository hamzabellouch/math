import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra

namespace OAI

/-!
# Power savings at the first-moment scale

A fixed power saving is smaller than `X^(5/6) / log X`.  This is the
analytic bookkeeping used for the short-range and truncation errors in
the sharp-cutoff argument.
-/

noncomputable section

open Filter Asymptotics

namespace CubicFirstMoment

/-- Any fixed positive power saving is negligible at the asserted scale. -/
theorem powerSaving_isLittleO {δ : ℝ} (hδ : 0 < δ) :
    (fun X : ℝ => X ^ (5 / 6 - δ : ℝ)) =o[atTop] firstMomentScale := by
  let multiplier : ℝ → ℝ := fun X => X ^ (5 / 6 - δ : ℝ) / Real.log X
  have h := (isLittleO_log_rpow_atTop hδ).mul_isBigO
    (isBigO_refl multiplier atTop)
  apply h.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    dsimp [multiplier]
    field_simp [(Real.log_pos hX).ne']
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    dsimp [multiplier, firstMomentScale]
    rw [← mul_div_assoc, ← Real.rpow_add (by linarith : 0 < X)]
    congr 2
    ring

/-- A bound with a fixed power saving implies the required little-oh
bound for any normed target space. -/
theorem isLittleO_of_powerSaving {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {δ : ℝ} (hδ : 0 < δ)
    (hf : f =O[atTop] (fun X : ℝ => X ^ (5 / 6 - δ : ℝ))) :
    f =o[atTop] firstMomentScale :=
  hf.trans_isLittleO (powerSaving_isLittleO hδ)

/-- The Fourier truncation loss is controlled by a fixed power saving.
The harmless `1` term is dominated by the interval-length term. -/
theorem truncationError_le {X ε ρ : ℝ} (hX : 1 ≤ X) (hρ : ρ ≤ 5 / 6) :
    X ^ ε * (1 + X / X ^ (1 / 6 + ρ : ℝ)) ≤
      2 * X ^ (5 / 6 - (ρ - ε) : ℝ) := by
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  have hpow : X / X ^ (1 / 6 + ρ : ℝ) = X ^ (5 / 6 - ρ : ℝ) := by
    calc
      X / X ^ (1 / 6 + ρ : ℝ) =
          X ^ (1 : ℝ) / X ^ (1 / 6 + ρ : ℝ) := by rw [Real.rpow_one]
      _ = X ^ (1 - (1 / 6 + ρ) : ℝ) := (Real.rpow_sub hX₀ _ _).symm
      _ = X ^ (5 / 6 - ρ : ℝ) := by congr 1; ring
  rw [hpow]
  have h₁ : (1 : ℝ) ≤ X ^ (5 / 6 - ρ : ℝ) :=
    Real.one_le_rpow hX (by linarith)
  have hε : 0 ≤ X ^ ε := Real.rpow_nonneg hX₀.le ε
  have hmul : X ^ ε * X ^ (5 / 6 - ρ : ℝ) =
      X ^ (5 / 6 - (ρ - ε) : ℝ) := by
    rw [← Real.rpow_add hX₀]
    congr 1
    ring
  nlinarith [mul_le_mul_of_nonneg_left h₁ hε]

/-- Choosing the norm-counting loss below the extra truncation height
makes the entire Fourier endpoint error negligible. -/
theorem truncationError_isLittleO {ε ρ : ℝ} (hερ : ε < ρ) (hρ : ρ ≤ 5 / 6) :
    (fun X : ℝ => X ^ ε * (1 + X / X ^ (1 / 6 + ρ : ℝ)))
      =o[atTop] firstMomentScale := by
  apply isLittleO_of_powerSaving (sub_pos.mpr hερ)
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact truncationError_le hX hρ

end CubicFirstMoment

end

end OAI
