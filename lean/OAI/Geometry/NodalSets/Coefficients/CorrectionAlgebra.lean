import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau

theorem correction_denominator_pos {s u lam : ℝ} (hs : 0 ≤ s)
    (hlam : 0 < lam) (hjet : s ≠ 0 ∨ u ≠ 0) : 0 < s + lam * u ^ 2 := by
  rcases hjet with h | h
  · have : 0 < s := lt_of_le_of_ne hs (Ne.symm h)
    positivity
  · have : 0 < u ^ 2 := sq_pos_of_ne_zero h
    positivity

theorem exact_correction {u lam s residual d : ℝ} (hlam : lam ≠ 0)
    (hden : s + lam * u ^ 2 ≠ 0) :
    let f := residual / (s + lam * u ^ 2)
    (u * d + f * s) + lam * (f * u - lam⁻¹ * d) * u = residual := by
  dsimp
  have hc (f : ℝ) : (u * d + f * s) +
      lam * (f * u - lam⁻¹ * d) * u = f * (s + lam * u ^ 2) := by
    field_simp [hlam]
    ring
  rw [hc, div_mul_cancel₀ _ hden]

theorem simplicity_preserves {u lam z s d : ℝ} (hlam : lam ≠ 0) :
    (u ^ 2 * d + 2 * z * u * s) +
      lam * (-lam⁻¹ * (u * d + 2 * z * s)) * u = 0 := by
  field_simp
  ring

theorem simplicity_energy_integrand (u v z uu vv uv : ℝ) :
    z * u ^ 2 * vv + 2 * z * v ^ 2 * uu -
      z * (v ^ 2 * uu + 2 * u * v * uv) =
    z * (u ^ 2 * vv - 2 * u * v * uv + v ^ 2 * uu) := by ring

theorem first_jet_coercivity {a b n lam : ℝ} (hn : 0 < n)
    (hlam : n ^ 2 ≤ lam) :
    (n ^ 2 / 2) * (a + b / n) ^ 2 ≤ b ^ 2 + lam * a ^ 2 := by
  have h := sq_nonneg (n * a - b)
  have ha := mul_nonneg (sub_nonneg.mpr hlam) (sq_nonneg a)
  field_simp
  nlinarith

theorem reciprocal_exponent {r ell : ℕ} (h : ell ≤ r) :
    r + 128 + ell * 136 ≤ 137 * r + 128 := by omega

theorem correction_accuracy (j : ℤ) :
    -(137 * j + 269) + 137 * j + 267 = -2 := by ring

end Yau

end OAI
