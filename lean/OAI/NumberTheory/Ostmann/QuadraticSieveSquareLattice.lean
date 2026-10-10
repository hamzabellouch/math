import OAI.NumberTheory.Ostmann.QuadraticSieveSmoothed
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareIntegralBase

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem squarePullback_scale (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M)
    (v : ℕ) (hv : 0 < v) (u : ℝ) :
    W (u ^ 2 * v / M) = squarePullback W 1 (by norm_num) (u / Real.sqrt (M / v)) := by
  rw [squarePullback_apply, one_mul, div_pow, Real.sq_sqrt]
  · congr 1
    field_simp
  · positivity

theorem positive_coprime_square_lattice (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M)
    (v : ℕ) (hv : 0 < v) (k : ℕ) (hk : 2 ≤ k) :
    (∑' u : {u : ℕ // 0 < u}, if Nat.Coprime u.val k then
      W (((u.val : ℝ) ^ 2) * v / M) else 0) =
      (1 / 2 : ℂ) * ∑' m : ℤ, if Nat.Coprime m.natAbs k then
        squarePullback W 1 (by norm_num) ((m : ℝ) / Real.sqrt (M / v)) else 0 := by
  let ψ := squarePullback W 1 (by norm_num)
  let X := Real.sqrt (M / v)
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hX : 0 < X := Real.sqrt_pos.mpr (div_pos hM hv')
  let F : ℤ → ℂ := fun m => if Nat.Coprime m.natAbs k then ψ ((m : ℝ) / X) else 0
  have hF : Summable F := by
    exact ((schwartz_summable_scaled ψ X hX.ne').indicator
      {m : ℤ | Nat.Coprime m.natAbs k}).congr (fun m => by simp [F, Set.indicator_apply])
  have heven : Function.Even F := by
    intro m
    simp only [F, Int.natAbs_neg, Int.cast_neg, neg_div, ψ, squarePullback_apply, neg_sq]
  have hz : F 0 = 0 := by
    have hk1 : k ≠ 1 := by omega
    simp [F, hk1]
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hF
  rw [hz, zero_add] at h
  calc
    _ = ∑' u : ℕ+, F (u : ℤ) := by
      apply tsum_congr
      intro u
      simp only [F, Int.natAbs_natCast, Int.cast_natCast]
      rw [squarePullback_scale W M hM v hv]
      rfl
    _ = (1 / 2 : ℂ) * ∑' m : ℤ, F m := by rw [h]; ring
    _ = _ := rfl

end Ostmann.QuadraticSieve

end OAI
