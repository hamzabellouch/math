import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace SmoothLocal.Weighted

theorem normalized_T_lower_bound {H Is epsilon t B MI Mt MB : ℝ}
    (heps : 0 ≤ epsilon) (hMt : 0 ≤ Mt) (hIs : |Is| ≤ MI)
    (ht : |t| ≤ Mt) (hB : |B| ≤ MB)
    (hbudget : 2 * (MI + epsilon + epsilon * Mt * MB) ≤ H) :
    H / 4 ≤ (H - Is - epsilon + epsilon * t * B) / 2 := by
  have hprod : |epsilon * t * B| ≤ epsilon * Mt * MB := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hB
      (abs_nonneg B) (mul_nonneg heps hMt)
  have hlower := (abs_le.mp hprod).1
  have hupper := (abs_le.mp hIs).2
  linarith

theorem quadratic_cross_absorption {T S J u v : ℝ} (hT : 0 < T) :
    T / 2 * u ^ 2 + (S - J ^ 2 / (2 * T)) * v ^ 2 ≤
      T * u ^ 2 + S * v ^ 2 + J * u * v := by
  have hs : 0 ≤ (T * u + J * v) ^ 2 / (2 * T) :=
    div_nonneg (sq_nonneg _) (by positivity)
  have he : T * u ^ 2 + S * v ^ 2 + J * u * v -
      (T / 2 * u ^ 2 + (S - J ^ 2 / (2 * T)) * v ^ 2) =
      (T * u + J * v) ^ 2 / (2 * T) := by
    field_simp
    ring
  linarith

theorem cross_loss_bound {T J W H A C epsilon : ℝ}
    (hW : 0 < W) (hH : 0 < H) (hC : 0 ≤ C) (heps : 0 ≤ epsilon)
    (hT : W * H / 4 ≤ T)
    (hJ : |J| ≤ W * C * epsilon * (1 + H * |A|)) :
    J ^ 2 / (T * W) ≤
      8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hmajor : 0 ≤ W * C * epsilon * (1 + H * |A|) := by positivity
  have hj2 : J ^ 2 ≤ (W * C * epsilon * (1 + H * |A|)) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg J) hmajor).mpr hJ
  have hshape : (1 + H * |A|) ^ 2 ≤ 2 * (1 + H ^ 2 * A ^ 2) := by
    nlinarith [sq_nonneg (H * |A| - 1), sq_abs A]
  have hnum : J ^ 2 ≤ 2 * W ^ 2 * C ^ 2 * epsilon ^ 2 * (1 + H ^ 2 * A ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hshape (sq_nonneg (W * C * epsilon))
    nlinarith [hj2]
  have hden : W ^ 2 * H / 4 ≤ T * W := by
    have hm := mul_le_mul_of_nonneg_right hT hW.le
    nlinarith [hm]
  have hR : 0 ≤ 8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2) := by positivity
  apply (div_le_iff₀ (mul_pos hTpos hW)).mpr
  have hm := mul_le_mul_of_nonneg_left hden hR
  have he : (8 * C ^ 2 * epsilon ^ 2 * (H⁻¹ + H * A ^ 2)) *
      (W ^ 2 * H / 4) =
      2 * W ^ 2 * C ^ 2 * epsilon ^ 2 * (1 + H ^ 2 * A ^ 2) := by
    field_simp
    ring
  rw [he] at hm
  exact hnum.trans hm

theorem positive_strip_weight_bound {d dmax lambda c1 K G M : ℝ}
    (hd : 0 < d) (hdd : d ≤ dmax) (hlambda : 0 ≤ lambda)
    (hc : 0 ≤ c1) (hK : 0 ≤ K) (hKd : K ≤ c1 * d)
    (hG : 0 ≤ G) (hGM : G ≤ M) :
    (lambda + 8 / d) * (G * K) ≤ M * c1 * (lambda * dmax + 8) := by
  have hH : 0 ≤ lambda + 8 / d := by positivity
  have hGK : G * K ≤ M * (c1 * d) :=
    (mul_le_mul_of_nonneg_right hGM hK).trans
      (mul_le_mul_of_nonneg_left hKd (hG.trans hGM))
  have hm := mul_le_mul_of_nonneg_left hGK hH
  have he : (lambda + 8 / d) * (M * (c1 * d)) =
      M * c1 * (lambda * d + 8) := by
    field_simp
  rw [he] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hdd hlambda) (le_refl 8))
    (mul_nonneg (hG.trans hGM) hc))

theorem exists_positive_strip_scale {M lambda dmax margin : ℝ}
    (hM : 0 ≤ M) (hlambda : 0 ≤ lambda) (hdmax : 0 ≤ dmax)
    (hmargin : 0 < margin) :
    ∃ c1 : ℝ, 0 < c1 ∧ M * c1 * (lambda * dmax + 8) ≤ margin := by
  let D := M * (lambda * dmax + 8) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨margin / D, div_pos hmargin hD, ?_⟩
  have he : M * (margin / D) * (lambda * dmax + 8) =
      margin / D * (D - 1) := by dsimp [D]; ring
  rw [he]
  have hle : D - 1 ≤ D := by linarith
  have hm := mul_le_mul_of_nonneg_left hle (div_pos hmargin hD).le
  simpa only [div_mul_cancel₀ margin hD.ne'] using hm

end SmoothLocal.Weighted

end

end OAI
