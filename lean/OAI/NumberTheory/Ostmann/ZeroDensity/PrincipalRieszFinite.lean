import Mathlib.NumberTheory.Chebyshev
import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalRieszIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszFiniteSum

namespace OAI

/-! # Literal finite Mangoldt sums underlying the principal Riesz mean -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem principalRieszMean_finite (N : ℕ) (X : ℝ) (hX : 0 < X) (hXN : X ≤ N) :
    (X : ℂ) * principalRieszMean X =
      (finiteRieszSum (Finset.range (N + 1)) ArithmeticFunction.vonMangoldt X : ℝ) := by
  have hsupport (n : ℕ) (hn : n ∉ Finset.range (N + 1)) :
      principalMangoldtCoefficient n * rieszPrimeTest (n / X) = 0 := by
    have hNn : N < n := by simpa using hn
    have hxn : X < n := hXN.trans_lt (by exact_mod_cast hNn)
    rw [rieszPrimeTest_scale X n hX, max_eq_right (by linarith : X - (n : ℝ) ≤ 0)]
    simp
  rw [principalRieszMean, tsum_eq_sum hsupport, Finset.mul_sum]
  unfold finiteRieszSum
  push_cast
  apply Finset.sum_congr rfl
  intro n _
  rw [rieszPrimeTest_scale X n hX]
  dsimp [principalMangoldtCoefficient]
  push_cast
  field_simp [show (X : ℂ) ≠ 0 by exact_mod_cast hX.ne']

theorem principalRieszMean_finite_error (N : ℕ) (X : ℝ) (hX : 0 < X) (hXN : X ≤ N) :
    |finiteRieszSum (Finset.range (N + 1)) ArithmeticFunction.vonMangoldt X - X ^ 2 / 2| =
      X * ‖principalRieszMean X - (X / 2 : ℝ)‖ := by
  have hf := principalRieszMean_finite N X hX hXN
  have he : ((finiteRieszSum (Finset.range (N + 1)) ArithmeticFunction.vonMangoldt X -
      X ^ 2 / 2 : ℝ) : ℂ) = (X : ℂ) * (principalRieszMean X - (X / 2 : ℝ)) := by
    rw [mul_sub, hf]
    push_cast
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, he, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hX]

theorem principal_finite_count_eq_psi (N : ℕ) (X : ℝ) (hX : 0 ≤ X) (hXN : X ≤ N) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => (n : ℝ) ≤ X),
      ArithmeticFunction.vonMangoldt n) = Chebyshev.psi X := by
  rw [Chebyshev.psi_eq_sum_Icc]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · intro hn
    exact ⟨Nat.zero_le _, (Nat.le_floor_iff hX).mpr hn.2⟩
  · intro hn
    have hnx := (Nat.le_floor_iff hX).mp hn.2
    have hnN : n ≤ N := by exact_mod_cast (hnx.trans hXN)
    exact ⟨by omega, hnx⟩

end Ostmann

end OAI
