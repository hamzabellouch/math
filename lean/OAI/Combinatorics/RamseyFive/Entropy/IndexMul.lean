import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyWeightedCount
open scoped BigOperators

lemma index_mul_le {J j : ℕ} (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hmono : Antitone s) (hj : j < J) :
    (j:ℝ)*s j ≤ ∑ i ∈ Finset.range J, s i := by
  have hsum : ∑ i ∈ Finset.range j, s j ≤ ∑ i ∈ Finset.range j, s i :=
    Finset.sum_le_sum (fun i hi => hmono (Finset.mem_range.mp hi).le)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj.le)
    (fun i _ _ => hs i))

theorem weighted_rich_count (J : ℕ) (s m : ℕ → ℝ) (q M n p N : ℝ)
    (hs : ∀ i, 0 ≤ s i) (hmono : Antitone s)
    (hm : ∀ i < J, 0 ≤ m i ∧ m i ≤ N)
    (hq : 0 ≤ q) (hM : 0 < M) (hp : 0 ≤ p) (hN : 0 ≤ N)
    (hpn : p*q ≤ 1) (hNq : N ≤ 3*q^2)
    (hbudget : ∑ i ∈ Finset.range J, s i ≤ n) (hJq : (J:ℝ)*q ≤ n)
    (hvariance : ∀ i < J, 2*p*s i ≤ M → m i*M^2 ≤ 4*q*s i) :
    (∑ i ∈ Finset.range J, (i:ℝ)*m i)*M^2 ≤ 12*n^2 := by
  have hn : 0 ≤ n := (mul_nonneg (Nat.cast_nonneg _) hq).trans hJq
  have hNp : N*p^2 ≤ 3 := by
    have hpq : (p*q)^2 ≤ 1 := by nlinarith [mul_nonneg hp hq]
    have hh := mul_le_mul_of_nonneg_right hNq (sq_nonneg p)
    nlinarith
  have hrow (i : ℕ) (hi : i ∈ Finset.range J) : (i:ℝ)*m i*M^2 ≤ 12*n*s i := by
    have hiJ := Finset.mem_range.mp hi
    have hiq : (i:ℝ)*q ≤ n :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hiJ.le) hq).trans hJq
    have his : (i:ℝ)*s i ≤ n := (index_mul_le s hs hmono hiJ).trans hbudget
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have hsi := hs i
    rcases hm i hiJ with ⟨hm0,hmN⟩
    by_cases hsmall : 2*p*s i ≤ M
    · have hh := mul_le_mul_of_nonneg_left (hvariance i hiJ hsmall) hi0
      have hq' := mul_le_mul_of_nonneg_right hiq (hs i)
      have hn' := mul_nonneg hn (hs i)
      nlinarith
    · have hsquare : M^2 ≤ 4*p^2*(s i)^2 := by
        have hh : M ≤ 2*p*s i := (lt_of_not_ge hsmall).le
        have hsq := pow_le_pow_left₀ hM.le hh 2
        nlinarith
      calc
        (i:ℝ)*m i*M^2 ≤ (i:ℝ)*N*(4*p^2*(s i)^2) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hmN hi0) hsquare
            (sq_nonneg M) (mul_nonneg hi0 hN)
        _ = 4*(N*p^2)*((i:ℝ)*s i)*s i := by ring
        _ ≤ 4*3*n*s i := by gcongr
        _ = 12*n*s i := by ring
  rw [Finset.sum_mul]
  calc
    ∑ i ∈ Finset.range J, (i:ℝ)*m i*M^2 ≤ ∑ i ∈ Finset.range J, 12*n*s i :=
      Finset.sum_le_sum hrow
    _ = 12*n*(∑ i ∈ Finset.range J, s i) := by rw [Finset.mul_sum]
    _ ≤ 12*n*n := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = 12*n^2 := by ring
end SharpRamseyFive.GreedyWeightedCount

end OAI
