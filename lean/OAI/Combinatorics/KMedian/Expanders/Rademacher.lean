import Mathlib
import OAI.Combinatorics.KMedian.Expanders.WalkMoments

namespace OAI

section Inline_PCPRademacher

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Rademacher
variable {S : Type} [Fintype S] [Nonempty S] (f : S → ℝ)
variable (hf : ∀ x, f x = 1 ∨ f x = -1) (hmean : (𝔼 x, f x)=0)

include hf hmean in
lemma expect_apply (H : ℝ → ℝ) : (𝔼 x, H (f x)) = (H 1 + H (-1))/2 := by
  have he (x : S) : H (f x) = (1+f x)/2*H 1+(1-f x)/2*H (-1) := by
    rcases hf x with h | h <;> rw [h] <;> ring
  simp_rw [he]
  rw [expect_add_distrib, ← expect_mul, ← expect_mul, ← Finset.expect_div,
    ← Finset.expect_div, expect_add_distrib, expect_sub_distrib, hmean]
  simp only [Fintype.expect_const]
  ring

def wordSum (n : ℕ) (c : Fin n → S) : ℝ := ∑ i, f (c i)
noncomputable def moment (n k : ℕ) : ℝ := 𝔼 c : Fin n → S, wordSum f n c ^ k

omit [Fintype S] [Nonempty S] in
lemma wordSum_cons (n : ℕ) (x : S) (c : Fin n → S) :
    wordSum f (n+1) (Fin.cons x c) = f x + wordSum f n c := by
  simp [wordSum, Fin.sum_univ_succ]

include hf hmean

lemma moment_succ (n k : ℕ) : moment f (n+1) k =
    𝔼 c : Fin n → S, ((wordSum f n c+1)^k+(wordSum f n c-1)^k)/2 := by
  unfold moment
  rw [expect_word_succ, expect_comm]
  apply expect_congr rfl
  intro c _
  simp_rw [wordSum_cons, add_comm (f _) (wordSum f n c)]
  simpa only [sub_eq_add_neg] using expect_apply f hf hmean (fun z => (wordSum f n c+z)^k)

lemma moment2_succ (n : ℕ) : moment f (n+1) 2 = moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^2+(s-1)^2)/2=s^2+1 := by ring
  simp_rw [he]
  rw [expect_add_distrib, Fintype.expect_const]
  rfl

lemma moment4_succ (n : ℕ) : moment f (n+1) 4 = moment f n 4 + 6*moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^4+(s-1)^4)/2=s^4+6*s^2+1 := by ring
  simp_rw [he]
  rw [expect_add_distrib, expect_add_distrib, ← mul_expect, Fintype.expect_const]
  rfl

lemma moment6_succ (n : ℕ) : moment f (n+1) 6 =
    moment f n 6 + 15*moment f n 4 + 15*moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^6+(s-1)^6)/2=s^6+15*s^4+15*s^2+1 := by ring
  simp_rw [he]
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const, moment]

lemma moment8_succ (n : ℕ) : moment f (n+1) 8 =
    moment f n 8 + 28*moment f n 6 + 70*moment f n 4 + 28*moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^8+(s-1)^8)/2=s^8+28*s^6+70*s^4+28*s^2+1 := by ring
  simp_rw [he]
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const, moment]

lemma moment10_succ (n : ℕ) : moment f (n+1) 10 =
    moment f n 10 + 45*moment f n 8 + 210*moment f n 6 + 210*moment f n 4 +
      45*moment f n 2 + 1 := by
  rw [moment_succ f hf hmean]
  have he (s : ℝ) : ((s+1)^10+(s-1)^10)/2=
      s^10+45*s^8+210*s^6+210*s^4+45*s^2+1 := by ring
  simp_rw [he]
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const, moment]

theorem moments_bound (n : ℕ) :
    moment f n 2 ≤ n ∧ moment f n 4 ≤ 3*(n:ℝ)^2 ∧
    moment f n 6 ≤ 15*(n:ℝ)^3 ∧ moment f n 8 ≤ 105*(n:ℝ)^4 ∧
    moment f n 10 ≤ 945*(n:ℝ)^5 := by
  induction n with
  | zero => simp [moment,wordSum]
  | succ n ih =>
    rcases ih with ⟨h2,h4,h6,h8,h10⟩
    rw [moment2_succ f hf hmean, moment4_succ f hf hmean,
      moment6_succ f hf hmean, moment8_succ f hf hmean, moment10_succ f hf hmean]
    push_cast
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hn2 : (0:ℝ) ≤ (n:ℝ)^2 := sq_nonneg _
    have hn3 : (0:ℝ) ≤ (n:ℝ)^3 := pow_nonneg hn _
    constructor
    · linarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith

theorem large_sum_rate (n : ℕ) (a : ℝ) (ha : 0 < a) :
    testRate (fun c : Fin n → S => a ≤ |wordSum f n c|) * a^10 ≤ 945*(n:ℝ)^5 := by
  classical
  have hm : testRate (fun c : Fin n → S => a ≤ |wordSum f n c|) * a^10 ≤ moment f n 10 := by
    unfold testRate moment
    rw [expect_mul]
    apply expect_le_expect
    intro c _
    dsimp only
    by_cases hc : a ≤ |wordSum f n c|
    · rw [ite_eq_left hc, one_mul]
      have hpow := pow_le_pow_left₀ (le_of_lt ha) hc 10
      simpa only [Even.pow_abs (by decide : Even 10)] using hpow
    · rw [ite_eq_right hc, zero_mul]
      exact Even.pow_nonneg (by decide : Even 10) _
  exact hm.trans (moments_bound f hf hmean n).2.2.2.2

end Rademacher
end MetricKMedian.PCP

end Inline_PCPRademacher

end OAI
