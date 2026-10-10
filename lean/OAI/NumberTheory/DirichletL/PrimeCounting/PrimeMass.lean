import OAI.NumberTheory.DirichletL.PrimeCounting.Progressions

namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction
open scoped Topology BigOperators

theorem cumsum_div_tendsto_zero_of_summable_div {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hsum : Summable (fun n => f n / n)) :
    Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 0) := by
  let F : ℕ → ℕ → ℝ := fun N n => if n < N then f n / N else 0
  have hlim (n : ℕ) : Tendsto (fun N => F N n) atTop (𝓝 0) := by
    apply (tendsto_const_div_atTop_nhds_zero_nat (f n)).congr'
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [F, hN]
  have hbound : ∀ N n, ‖F N n‖ ≤ f n / n := by
    intro N n
    by_cases hn : n = 0
    · subst n
      simp [F, hzero]
    by_cases hN : n < N
    · simp only [F, ite_eq_left hN, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hf n) (Nat.cast_nonneg N))]
      exact div_le_div_of_nonneg_left (hf n)
        (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn)
        (show (n : ℝ) ≤ N by exact_mod_cast hN.le)
    · simp only [F, ite_eq_right hN, norm_zero]
      exact div_nonneg (hf n) (by positivity)
  have h := tendsto_tsum_of_dominated_convergence hsum hlim
    (Filter.Eventually.of_forall hbound)
  have heq (N : ℕ) : (∑' n, F N n) = cumsum f N / N := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      simp only [Finset.mem_range] at hn
      simp [F, hn])]
    rw [cumsum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    simp [F, Finset.mem_range.mp hn]
  simpa only [heq, tsum_zero] using h

theorem retained_ratio_tendsto {f : ℕ → ℝ} {A : ℝ} (keep : ℕ → Prop)
    [DecidablePred keep] (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (hremainder : Summable (fun n => (if keep n then 0 else f n) / n)) :
    Tendsto (fun N : ℕ => cumsum (fun n => if keep n then f n else 0) N / N)
      atTop (𝓝 A) := by
  have hrem := cumsum_div_tendsto_zero_of_summable_div
    (f := fun n => if keep n then 0 else f n)
    (fun n => by split_ifs <;> first | exact le_rfl | exact hf n)
    (by simp [hzero]) hremainder
  have h := hmass.sub hrem
  have heq (N : ℕ) :
      cumsum f N / N - cumsum (fun n => if keep n then 0 else f n) N / N =
      cumsum (fun n => if keep n then f n else 0) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp
  simpa only [heq, sub_zero] using h

theorem prime_residueClass_ratio_tendsto {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ =>
      cumsum (fun n => if n.Prime then vonMangoldt.residueClass a n else 0) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) :=
  retained_ratio_tendsto Nat.Prime (vonMangoldt.residueClass_nonneg a)
    (vonMangoldt.residueClass_apply_zero a) (residueClass_ratio_tendsto a ha)
    (vonMangoldt.summable_residueClass_non_primes_div a)

end SevenEighths.PNT

end OAI
