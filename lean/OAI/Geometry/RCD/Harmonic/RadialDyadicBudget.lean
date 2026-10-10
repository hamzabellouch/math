import OAI.Geometry.RCD.Harmonic.RadialSquaredDistance
import OAI.Geometry.RCD.Metric.VolumeBudget

namespace OAI

/-!
# Dyadic normalization of the radial mass estimate

The coefficient of the inner source mass is a fixed positive dimensional
constant times the inverse power of the radius. This preserves the signed
volume increments when summing; monotonicity of the raw Euclidean volume
profile is not imposed.
-/

open Filter
open scoped Topology

noncomputable section

namespace RegularPointCoordinates

def radialCutoffCoefficient (n : ℝ) : ℝ := (1 - (2 : ℝ) ^ (-n)) / n

theorem radialCutoffCoefficient_pos {n : ℝ} (hn : 0 < n) : 0 < radialCutoffCoefficient n := by
  apply div_pos _ hn
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

theorem radialPower_height_dyadic {n r : ℝ} (hr : 0 < r) :
    (r ^ (-n) - (2 * r) ^ (-n)) / n = r ^ (-n) * radialCutoffCoefficient n := by
  rw [Real.mul_rpow (by norm_num) hr.le]
  unfold radialCutoffCoefficient
  ring

/-- Normalize the actual annular estimate using only the outer volume bound. -/
theorem radial_mass_normalized_le {n r M V W curvature C : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hcurvature : 0 ≤ curvature)
    (hW : W ≤ C * (2 * r) ^ n)
    (hmass : ((r ^ (-n) - (2 * r) ^ (-n)) / n) * M ≤
      r ^ (-n) * V - (2 * r) ^ (-n) * W +
      curvature * ((r ^ (-n) - (2 * r) ^ (-n)) / n) * W) :
    r ^ (-n) * M ≤ (radialCutoffCoefficient n)⁻¹ *
      (r ^ (-n) * V - (2 * r) ^ (-n) * W) + curvature * C * (2 : ℝ) ^ n := by
  let D := radialCutoffCoefficient n
  have hD : 0 < D := radialCutoffCoefficient_pos hn
  have hrp : 0 < r ^ (-n) := Real.rpow_pos_of_pos hr _
  have hcancel : r ^ (-n) * (2 * r) ^ n = (2 : ℝ) ^ n := by
    rw [Real.mul_rpow (by norm_num) hr.le]
    calc
      _ = (2 : ℝ) ^ n * (r ^ (-n) * r ^ n) := by ring
      _ = _ := by rw [← Real.rpow_add hr, neg_add_cancel, Real.rpow_zero, mul_one]
  rw [radialPower_height_dyadic hr] at hmass
  have hcorr : curvature * (r ^ (-n) * D) * W ≤ curvature * D * C * (2 : ℝ) ^ n := by
    calc
      _ ≤ curvature * (r ^ (-n) * D) * (C * (2 * r) ^ n) :=
        mul_le_mul_of_nonneg_left hW (mul_nonneg hcurvature (mul_nonneg hrp.le hD.le))
      _ = curvature * D * C * (r ^ (-n) * (2 * r) ^ n) := by ring
      _ = _ := by rw [hcancel]
  have hm : D * (r ^ (-n) * M) ≤
      r ^ (-n) * V - (2 * r) ^ (-n) * W + curvature * D * C * (2 : ℝ) ^ n := by
    nlinarith
  apply (mul_le_mul_iff_left₀ hD).mp
  calc
    _ = D * (r ^ (-n) * M) := mul_comm _ _
    _ ≤ r ^ (-n) * V - (2 * r) ^ (-n) * W + curvature * D * C * (2 : ℝ) ^ n := hm
    _ = ((radialCutoffCoefficient n)⁻¹ * (r ^ (-n) * V - (2 * r) ^ (-n) * W) +
      curvature * C * (2 : ℝ) ^ n) * D := by
        change _ = (D⁻¹ * (r ^ (-n) * V - (2 * r) ^ (-n) * W) + curvature * C * (2 : ℝ) ^ n) * D
        field_simp [ne_of_gt hD]

/-- Signed dyadic volume increments and curvature control the total normalized
source mass. The density need not be attained monotonically. -/
theorem radial_mass_dyadic_budget {n C kappa omega density : ℝ}
    {A M : ℕ → ℝ} (hn : 0 < n)
    (hA : Tendsto A atTop (𝓝 density)) (hdensity : density ≤ omega)
    (hM : ∀ i, 0 ≤ M i)
    (hmass : ∀ i, M i ≤ (radialCutoffCoefficient n)⁻¹ * (A (i + 1) - A i) +
      kappa * (1 / 4 : ℝ) ^ i * C * (2 : ℝ) ^ n) :
    Summable M ∧ (∑' i, M i) ≤ (radialCutoffCoefficient n)⁻¹ *
      (omega - A 0 + (kappa * C * (2 : ℝ) ^ n * radialCutoffCoefficient n) * (4 / 3)) := by
  have hD := radialCutoffCoefficient_pos hn
  apply volume_defect_budget_of_profile_limit (inv_nonneg.mpr hD.le) hA hdensity hM
  intro i
  calc
    M i ≤ (radialCutoffCoefficient n)⁻¹ * (A (i + 1) - A i) +
        kappa * (1 / 4 : ℝ) ^ i * C * (2 : ℝ) ^ n := hmass i
    _ = _ := by field_simp [ne_of_gt hD]

/-- A uniform outer-volume deficit gives a uniform source budget, even at
centers whose density is less than the Euclidean density. -/
theorem radial_mass_budget_of_outer_deficit {Y : Type*} {n C kappa omega delta : ℝ}
    {density : Y → ℝ} {A M : Y → ℕ → ℝ} (hn : 0 < n)
    (hA : ∀ y, Tendsto (A y) atTop (𝓝 (density y)))
    (hdensity : ∀ y, density y ≤ omega) (houter : ∀ y, omega - delta ≤ A y 0)
    (hM : ∀ y i, 0 ≤ M y i)
    (hmass : ∀ y i, M y i ≤ (radialCutoffCoefficient n)⁻¹ * (A y (i + 1) - A y i) +
      kappa * (1 / 4 : ℝ) ^ i * C * (2 : ℝ) ^ n) :
    ∀ y, Summable (M y) ∧ (∑' i, M y i) ≤
      (radialCutoffCoefficient n)⁻¹ * delta + kappa * C * (2 : ℝ) ^ n * (4 / 3) := by
  intro y
  obtain ⟨hs, hb⟩ := radial_mass_dyadic_budget hn (hA y) (hdensity y) (hM y) (hmass y)
  refine ⟨hs, hb.trans ?_⟩
  have hD := radialCutoffCoefficient_pos hn
  calc
    _ ≤ (radialCutoffCoefficient n)⁻¹ *
        (delta + (kappa * C * (2 : ℝ) ^ n * radialCutoffCoefficient n) * (4 / 3)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hD.le)
      linarith [houter y]
    _ = _ := by field_simp [ne_of_gt hD]

/-- The uniform budget tends to zero along increasingly flat rescalings. -/
theorem radial_mass_budget_uniformly_small {Y : Type*} {n C : ℝ}
    {delta kappa : ℕ → ℝ} {M : ℕ → Y → ℕ → ℝ}
    (hdelta : Tendsto delta atTop (𝓝 0)) (hkappa : Tendsto kappa atTop (𝓝 0))
    (hbudget : ∀ ν y, (∑' i, M ν y i) ≤ (radialCutoffCoefficient n)⁻¹ * delta ν +
      kappa ν * C * (2 : ℝ) ^ n * (4 / 3)) :
    ∀ ε > 0, ∀ᶠ ν in atTop, ∀ y, (∑' i, M ν y i) < ε := by
  have ht : Tendsto (fun ν => (radialCutoffCoefficient n)⁻¹ * delta ν +
      kappa ν * C * (2 : ℝ) ^ n * (4 / 3)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      (hdelta.const_mul _).add (((hkappa.mul_const C).mul_const ((2 : ℝ) ^ n)).mul_const (4 / 3))
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with ν hν y
  exact (hbudget ν y).trans_lt hν

end RegularPointCoordinates

end

end OAI
