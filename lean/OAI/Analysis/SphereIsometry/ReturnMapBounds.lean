import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-! Scalar estimates for the return map, before taking finite diameter covers. -/

namespace Tingley

theorem radius_ratio_le_factor {p s M U : ℝ} (hs : 0 < s)
    (hM : 0 ≤ M) (hsU : s ≤ U) (hsp : s = p + M) :
    p / s ≤ 1 - M / U := by
  calc
    p / s = (s - M) / s := congrArg (fun q : ℝ => q / s) (by linarith)
    _ = 1 - M / s := by rw [sub_div, div_self (ne_of_gt hs)]
    _ ≤ 1 - M / U :=
      sub_le_sub_left (div_le_div_of_nonneg_left hM hs hsU) 1

theorem return_coefficient_le {p s u r M U : ℝ}
    (hp : 0 ≤ p) (_hu : 0 ≤ u) (hr : 0 < r) (hs : 0 < s)
    (hM : 0 ≤ M) (hrU : r ≤ U) (hsU : s ≤ U)
    (hrm : r = u + M) (hsm : s = p + M) :
    u * p / (r * s) ≤ (1 - M / U) ^ 2 := by
  have hpq := radius_ratio_le_factor hs hM hsU hsm
  have huq := radius_ratio_le_factor hr hM hrU hrm
  have hp0 : 0 ≤ p / s := div_nonneg hp hs.le
  have hq0 : 0 ≤ 1 - M / U := hp0.trans hpq
  calc
    u * p / (r * s) = (u / r) * (p / s) := by rw [div_mul_div_comm]
    _ ≤ (1 - M / U) * (1 - M / U) := mul_le_mul huq hpq hp0 hq0
    _ = (1 - M / U) ^ 2 := by ring

theorem return_pair_error_le {a r s u du dp : ℝ}
    (ha : 0 < a) (har : a ≤ r) (has : a ≤ s)
    (hur : u ≤ r) (hdu : 0 ≤ du) (hdp : 0 ≤ dp) :
    2 * du / r + 2 * u * dp / (r * s) ≤ (2 / a) * (du + dp) := by
  have hr : 0 < r := ha.trans_le har
  have hs : 0 < s := ha.trans_le has
  have he₁ : 2 * du / r ≤ 2 * du / a :=
    div_le_div_of_nonneg_left (mul_nonneg zero_le_two hdu) ha har
  have he₂ : 2 * u * dp / (r * s) ≤ 2 * dp / a := by
    calc
      2 * u * dp / (r * s) = (u / r) * (2 * dp / s) := by
        field_simp [ne_of_gt hr, ne_of_gt hs]
      _ ≤ 1 * (2 * dp / s) :=
        mul_le_mul_of_nonneg_right ((div_le_one₀ hr).mpr hur)
          (div_nonneg (mul_nonneg zero_le_two hdp) hs.le)
      _ = 2 * dp / s := one_mul _
      _ ≤ 2 * dp / a :=
        div_le_div_of_nonneg_left (mul_nonneg zero_le_two hdp) ha has
  calc
    2 * du / r + 2 * u * dp / (r * s) ≤ 2 * du / a + 2 * dp / a :=
      add_le_add he₁ he₂
    _ = (2 / a) * (du + dp) := by ring

theorem return_pair_uniform_bound {a U M p s u r D Dg du dp : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hp : 0 ≤ p) (hu : 0 ≤ u)
    (har : a ≤ r) (has : a ≤ s) (hrU : r ≤ U) (hsU : s ≤ U)
    (hrm : r = u + M) (hsm : s = p + M)
    (hD : 0 ≤ D) (hdu : 0 ≤ du) (hdp : 0 ≤ dp)
    (hpair : Dg ≤ (u * p / (r * s)) * D +
      2 * du / r + 2 * u * dp / (r * s)) :
    Dg ≤ (1 - M / U) ^ 2 * D + (2 / a) * (du + dp) := by
  have hr : 0 < r := ha.trans_le har
  have hs : 0 < s := ha.trans_le has
  have hur : u ≤ r := by linarith
  have hcoeff := return_coefficient_le hp hu hr hs hM hrU hsU hrm hsm
  have herr := return_pair_error_le ha har has hur hdu hdp
  calc
    Dg ≤ (u * p / (r * s)) * D +
        2 * du / r + 2 * u * dp / (r * s) := hpair
    _ = (u * p / (r * s)) * D +
        (2 * du / r + 2 * u * dp / (r * s)) := by ring
    _ ≤ (1 - M / U) ^ 2 * D + (2 / a) * (du + dp) :=
      add_le_add (mul_le_mul_of_nonneg_right hcoeff hD) herr

/-- The exact square factor, with its strict upper bound. -/
theorem return_factor_mem_Ico {t M : ℝ} (ht0 : 0 < t)
    (hM : 0 < M) (hMU : M < 1 + t) :
    (1 - M / (1 + t)) ^ 2 ∈ Set.Ico (0 : ℝ) 1 := by
  have hU : 0 < 1 + t := by linarith
  have hq0 : 0 < M / (1 + t) := div_pos hM hU
  have hq1 : M / (1 + t) < 1 := by
    apply (div_lt_iff₀ hU).mpr
    simpa using hMU
  have hprod : 0 < (1 - M / (1 + t)) * (M / (1 + t)) :=
    mul_pos (by linarith) hq0
  exact ⟨sq_nonneg _, by nlinarith⟩

/-- Nonemptiness is used only to bound M by one actual positive radius. -/
theorem return_contraction_factor_mem_Ico {X : Type*}
    {C : Set X} {p s : X → ℝ} {t M : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hM : 0 < M) (hCne : C.Nonempty)
    (hp : ∀ v ∈ C, 1 - t ≤ p v)
    (hsU : ∀ v ∈ C, s v ≤ 1 + t)
    (hsm : ∀ v ∈ C, s v = p v + M) :
    (1 - M / (1 + t)) ^ 2 ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨v, hv⟩ := hCne
  have hpv := hp v hv
  have hsv := hsU v hv
  have heq := hsm v hv
  apply return_factor_mem_Ico ht0 hM
  linarith

end Tingley

end OAI
