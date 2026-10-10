import OAI.NumberTheory.Ostmann.Characters.SparseCoverageContradiction

namespace OAI

/-! # The sharp numerical specialization of the sparse contradiction -/
namespace Ostmann

 theorem sparse_sieve_numerical_bound (c U X Q D H L R : ℝ)
    (hc : 0 ≤ c) (hU : 0 < U) (hX : 0 < X) (hD : 0 ≤ D)
    (hQ : X / 4 ≤ Q ^ 2) (hDX : D ≤ 3 * X)
    (hb : c * U * X * (Q / 16 * Real.exp (-R)) ^ 2 ≤
      Real.exp L * (2 * U * Real.exp (-(8 / 5) * H)) * D ^ 2) :
    c ≤ 18432 * Real.exp (L - (8 / 5) * H + 2 * R) := by
  have hα : X / 1024 * Real.exp (-(2 * R)) ≤ (Q / 16 * Real.exp (-R)) ^ 2 := by
    have he : Real.exp (-(2 * R)) = Real.exp (-R) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hQ (sq_nonneg (Real.exp (-R)))
    nlinarith only [hh]
  have hD2 : D ^ 2 ≤ 9 * X ^ 2 := by nlinarith only [hD, hDX, hX]
  have hleft := (mul_le_mul_of_nonneg_left hα (mul_nonneg (mul_nonneg hc hU.le) hX.le)).trans hb
  have hright := mul_le_mul_of_nonneg_left hD2
    (show 0 ≤ Real.exp L * (2 * U * Real.exp (-(8 / 5) * H)) by positivity)
  have hh := hleft.trans hright
  have heq : Real.exp (L - (8 / 5) * H + 2 * R) * Real.exp (-(2 * R)) =
      Real.exp L * Real.exp (-(8 / 5) * H) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  apply (mul_le_mul_iff_left₀ (show 0 < U * X ^ 2 * Real.exp (-(2 * R)) by positivity)).mp
  calc
    _ = 1024 * (c * U * X * (X / 1024 * Real.exp (-(2 * R)))) := by ring
    _ ≤ 1024 * (Real.exp L * (2 * U * Real.exp (-(8 / 5) * H)) * (9 * X ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 18432 * U * X ^ 2 * (Real.exp L * Real.exp (-(8 / 5) * H)) := by ring
    _ = 18432 * U * X ^ 2 *
        (Real.exp (L - (8 / 5) * H + 2 * R) * Real.exp (-(2 * R))) := by rw [heq]
    _ = _ := by ring

 theorem sparse_sieve_numerical_impossible (c U X Q D H L : ℝ)
    (hc : 0 < c) (hU : 0 < U) (hX : 0 < X) (hD : 0 ≤ D)
    (hQ : X / 4 ≤ Q ^ 2) (hDX : D ≤ 3 * X) (hH : (17 / 25) * L ≤ H)
    (hmargin : 18432 * Real.exp (L - (8 / 5) * ((17 / 25) * L) +
      2 * L ^ (3 / 4 : ℝ)) < c)
    (hb : c * U * X * (Q / 16 * Real.exp (-(L ^ (3 / 4 : ℝ)))) ^ 2 ≤
      Real.exp L * (2 * U * Real.exp (-(8 / 5) * H)) * D ^ 2) : False := by
  have hh := sparse_sieve_numerical_bound c U X Q D H L (L ^ (3 / 4 : ℝ))
    hc.le hU hX hD hQ hDX hb
  have he : Real.exp (L - (8 / 5) * H + 2 * L ^ (3 / 4 : ℝ)) ≤
      Real.exp (L - (8 / 5) * ((17 / 25) * L) + 2 * L ^ (3 / 4 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

end Ostmann

end OAI
