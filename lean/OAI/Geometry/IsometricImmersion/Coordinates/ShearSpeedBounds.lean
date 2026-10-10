import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace SmoothLocal.Pulse

theorem shear_time_factor_bound {v b a : ℝ} (hv : 0 < v)
    (hb : |b| ≤ v / 2) (ha : a ≤ -(v ^ 2)) :
    v ^ 2 / 2 ≤ -(b ^ 2 + a) := by
  have hb2 : b ^ 2 ≤ (v / 2) ^ 2 := by
    have ht := (sq_le_sq₀ (abs_nonneg b) (by positivity : 0 ≤ v / 2)).mpr hb
    simpa only [sq_abs] using ht
  nlinarith [sq_nonneg v]

theorem shear_principal_speed {v b a : ℝ} (hv : 0 < v)
    (hb : |b| ≤ v / 2) (ha : a ≤ -(v ^ 2)) :
    0 < -1 / (b ^ 2 + a) ∧
      |2 * b / (b ^ 2 + a)| + Real.sqrt (-1 / (b ^ 2 + a)) ≤ 4 / v := by
  let d := -(b ^ 2 + a)
  have hd0 : v ^ 2 / 2 ≤ d := shear_time_factor_bound hv hb ha
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  have hd : 0 < d := (half_pos hv2).trans_le hd0
  have hS : -1 / (b ^ 2 + a) = 1 / d := by
    dsimp only [d]
    rw [div_neg, neg_div]
  have hP : |2 * b / (b ^ 2 + a)| = 2 * |b| / d := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_neg (show b ^ 2 + a < 0 from neg_pos.mp hd)]
  have hp : 2 * |b| / d ≤ 2 / v := by
    apply (div_le_div_iff₀ hd hv).mpr
    have hh := mul_le_mul_of_nonneg_right hb hv.le
    nlinarith
  have hs : 1 / d ≤ (2 / v) ^ 2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ hd hv2).mpr
    nlinarith
  have hsqrt : Real.sqrt (1 / d) ≤ 2 / v :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hs⟩
  rw [hS, hP]
  refine ⟨one_div_pos.mpr hd, ?_⟩
  calc
    _ ≤ 2 / v + 2 / v := add_le_add hp hsqrt
    _ = 4 / v := by ring

theorem shear_principal_floor {b a D : ℝ} (hd : b ^ 2 + a < 0)
    (hD : -(b ^ 2 + a) ≤ D) :
    0 < D ∧ 1 / D ≤ -1 / (b ^ 2 + a) := by
  have hp : 0 < -(b ^ 2 + a) := neg_pos.mpr hd
  refine ⟨hp.trans_le hD, ?_⟩
  have h := one_div_le_one_div_of_le hp hD
  simpa only [div_neg, neg_div] using h

theorem shear_width_smallness {v b : ℝ} (hv : 0 < v)
    (hb : |b| ≤ 1 / (10 * (100 * (1 + v⁻¹)))) :
    |b| ≤ v / 2 ∧ 4 / v < (100 * (1 + v⁻¹)) / 4 := by
  have hwidth : 0 < 100 * (1 + v⁻¹) := by positivity
  have hsmall : 1 / (10 * (100 * (1 + v⁻¹))) ≤ v / 1000 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hwidth)).mpr
    have he : v / 1000 * (10 * (100 * (1 + v⁻¹))) = v + 1 := by
      field_simp [hv.ne']
      ring
    rw [he]
    linarith
  refine ⟨(hb.trans hsmall).trans (by linarith), ?_⟩
  apply (div_lt_iff₀ hv).mpr
  have he : (100 * (1 + v⁻¹)) / 4 * v = 25 * (v + 1) := by
    field_simp [hv.ne']
    ring
  rw [he]
  linarith

theorem negative_curvature_factor {K E h kappa e M v : ℝ}
    (hkappa : 0 < kappa) (he : 0 < e) (hh : h ≠ 0)
    (hK : K ≤ -kappa / 2) (hE : e ≤ E) (hH : |h| ≤ M)
    (hv : v ^ 2 ≤ kappa * e / (2 * M ^ 2)) :
    K * (E / h ^ 2) ≤ -(v ^ 2) := by
  have hE0 : 0 < E := he.trans_le hE
  have hK0 : 0 < -K := by linarith
  have hM0 : 0 < M := (abs_pos.mpr hh).trans_le hH
  have hden : h ^ 2 ≤ M ^ 2 := by
    have ht := (sq_le_sq₀ (abs_nonneg h) hM0.le).mpr hH
    simpa only [sq_abs] using ht
  have hnum : kappa * e / 2 ≤ -K * E := by
    have ht := mul_le_mul (show kappa / 2 ≤ -K by linarith) hE he.le hK0.le
    nlinarith
  have hdiv : (kappa * e / 2) / M ^ 2 ≤ (-K * E) / h ^ 2 :=
    div_le_div₀ (mul_nonneg hK0.le hE0.le) hnum (sq_pos_of_ne_zero hh) hden
  have heq : kappa * e / (2 * M ^ 2) = (kappa * e / 2) / M ^ 2 := by ring
  rw [heq] at hv
  have ht := hv.trans hdiv
  have heq2 : K * (E / h ^ 2) = -((-K * E) / h ^ 2) := by ring
  rw [heq2]
  linarith

end SmoothLocal.Pulse

end

end OAI
