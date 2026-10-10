import OAI.NumberTheory.TwoPoint.Halasz.HalaszIterationScale

namespace OAI

/-! The trivial count absorbs endpoints below the fixed iteration
threshold without changing the exponent of the large-endpoint bound. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_vinogradov_trivial (s k N : ℕ) : halaszVinogradovCount s k N≤N^(2*s) := by
  have hf (x : Fin s → Fin N) : (halaszVinogradovFiber x k).card≤N^s := by
    calc
      _ ≤ (univ : Finset (Fin s → Fin N)).card := card_le_card (subset_univ _)
      _ = _ := by simp
  unfold halaszVinogradovCount
  calc
    _ ≤ ∑ _x : Fin s → Fin N, N^s := sum_le_sum (fun x _ => hf x)
    _ = _ := by simp [← pow_add,two_mul]

theorem halasz_small_moment {s k N H K : ℕ} {e : ℝ}
    (hN : 1≤N) (hNH : N≤H) (he : (2*s:ℕ)≤e+(K:ℝ)) :
    (halaszVinogradovCount s k N:ℝ)≤(H:ℝ)^K*(N:ℝ)^e := by
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0:ℝ)<N := lt_of_lt_of_le zero_lt_one hN1
  have hcount : (halaszVinogradovCount s k N:ℝ)≤(N:ℝ)^(2*s) := by
    exact_mod_cast halasz_vinogradov_trivial s k N
  calc
    _ ≤ (N:ℝ)^(2*s) := hcount
    _ = (N:ℝ)^((2*s:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (N:ℝ)^(e+(K:ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 he
    _ = (N:ℝ)^e*(N:ℝ)^K := by rw [Real.rpow_add hN0,Real.rpow_natCast]
    _ ≤ (N:ℝ)^e*(H:ℝ)^K := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hNH) K)
      (Real.rpow_nonneg hN0.le _)
    _ = _ := mul_comm _ _

end TwoPointCorrelations

end OAI
