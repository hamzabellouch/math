import OAI.GroupTheory.Thompson.UnitBall
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Negative radial normalization, with the field's usual value at zero. -/
def normalizeNeg (z : E) : E := -(‖z‖⁻¹ • z)

theorem norm_normalizeNeg {z : E} (hz : z ≠ 0) : ‖normalizeNeg z‖ = 1 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [normalizeNeg, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)), inv_mul_cancel₀ hn]

/-- A scalar identity used to avoid any estimate depending on the larger norm. -/
private theorem abs_inv_sub_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| * b = |b - a| / a := by
  have hdiff : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp [ha.ne', hb.ne']
  rw [hdiff, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hb]
  field_simp [ha.ne', hb.ne']

/-- Radial normalization is `2 / ε`-Lipschitz where the norm is at least `ε`. -/
theorem normalizeNeg_lipschitz {ε : ℝ} (hε : 0 < ε) {x y : E}
    (hx : ε ≤ ‖x‖) (hy : ε ≤ ‖y‖) :
    ‖normalizeNeg x - normalizeNeg y‖ ≤ (2 / ε) * ‖x - y‖ := by
  have hxp : 0 < ‖x‖ := hε.trans_le hx
  have hyp : 0 < ‖y‖ := hε.trans_le hy
  have hdecomp : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    simp only [smul_sub, sub_smul]
    abel
  have hneg : normalizeNeg x - normalizeNeg y =
      -(‖x‖⁻¹ • x - ‖y‖⁻¹ • y) := by
    simp only [normalizeNeg, neg_sub]
    abel
  calc
    ‖normalizeNeg x - normalizeNeg y‖ =
        ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ := by rw [hneg, norm_neg]
    _ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    _ = ‖x‖⁻¹ * ‖x - y‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hxp), abs_inv_sub_mul hxp hyp]
    _ ≤ ‖x‖⁻¹ * ‖x - y‖ + ‖x - y‖ / ‖x‖ := by
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_right
        (by simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x) (norm_nonneg x)
    _ = (2 / ‖x‖) * ‖x - y‖ := by ring
    _ ≤ (2 / ε) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num) hε hx) (norm_nonneg _)

/-- Normalize the given nonvanishing map and retain the closed-ball carrier. -/
def normalizedMap (G : UnitBall E → E) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖) : UnitBall E → UnitBall E :=
  fun x => ⟨normalizeNeg (G x), le_of_eq (norm_normalizeNeg
    (norm_pos_iff.mp (hε.trans_le (hLower x))))⟩

@[simp] theorem coe_normalizedMap (G : UnitBall E → E) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖) (x : UnitBall E) :
    (normalizedMap G hε hLower x : E) = normalizeNeg (G x) := rfl

theorem norm_normalizedMap (G : UnitBall E → E) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖) (x : UnitBall E) :
    ‖(normalizedMap G hε hLower x : E)‖ = 1 :=
  norm_normalizeNeg (norm_pos_iff.mp (hε.trans_le (hLower x)))

/-- The outer identity and unit normalization give a displacement of at least `1/2`. -/
theorem normalizedMap_displacement (G : UnitBall E → E) {ε : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖)
    (hOuter : ∀ x : UnitBall E, (1 / 2 : ℝ) ≤ ‖(x : E)‖ → G x = (x : E))
    (x : UnitBall E) :
    (1 / 2 : ℝ) ≤ ‖(normalizedMap G hε hLower x : E) - (x : E)‖ := by
  by_cases hx : (1 / 2 : ℝ) ≤ ‖(x : E)‖
  · have hxp : 0 < ‖(x : E)‖ := by linarith
    have hi : 0 ≤ ‖(x : E)‖⁻¹ + 1 := by
      have := inv_nonneg.mpr (norm_nonneg (x : E))
      linarith
    have heq : normalizeNeg (x : E) - (x : E) =
        -((‖(x : E)‖⁻¹ + 1) • (x : E)) := by
      simp only [normalizeNeg, add_smul, one_smul, neg_add_rev]
      abel
    rw [coe_normalizedMap, hOuter x hx, heq, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hi, add_mul, one_mul,
      inv_mul_cancel₀ hxp.ne']
    linarith
  · have hrev := norm_sub_norm_le (normalizedMap G hε hLower x : E) (x : E)
    rw [norm_normalizedMap] at hrev
    linarith

/-- The concrete normalized map inherits the advertised Lipschitz estimate. -/
theorem normalizedMap_lipschitz (G : UnitBall E → E) {ε C : ℝ} (hε : 0 < ε)
    (hLower : ∀ x, ε ≤ ‖G x‖)
    (hLip : ∀ x y : UnitBall E, ‖G x - G y‖ ≤ C * ‖(x : E) - (y : E)‖)
    (x y : UnitBall E) :
    ‖(normalizedMap G hε hLower x : E) - (normalizedMap G hε hLower y : E)‖ ≤
      (2 * C / ε) * ‖(x : E) - (y : E)‖ := by
  calc
    _ ≤ (2 / ε) * ‖G x - G y‖ := normalizeNeg_lipschitz hε (hLower x) (hLower y)
    _ ≤ (2 / ε) * (C * ‖(x : E) - (y : E)‖) :=
      mul_le_mul_of_nonneg_left (hLip x y) (div_nonneg (by norm_num) hε.le)
    _ = _ := by ring

end ThompsonNonamenability.Analytic

end

end OAI
