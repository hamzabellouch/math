import OAI.NumberTheory.ShortEgyptian.EmpiricalDiscrepancy

namespace OAI

universe uα uβ

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem sum_nat_int_Icc (f : ℤ → ℂ) (p q : ℕ) :
    (∑ n ∈ Icc p q, f n) = ∑ n ∈ Icc (p : ℤ) q, f n := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    simpa only [mem_Icc, Nat.cast_le] using hn
  · intro a _ b _ hab
    exact_mod_cast hab
  · intro n hn
    have hn0 : 0 ≤ n := le_trans (by positivity) (mem_Icc.mp hn).1
    refine ⟨n.toNat, ?_, Int.toNat_of_nonneg hn0⟩
    have hh := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intros
    rfl

theorem dyadic_interval_norm (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C) (p q : ℕ)
    (hp : 1 ≤ p)
    (hlocal : ∀ u v : ℕ, p ≤ u → u ≤ v → v ≤ q → v ≤ 2 * u →
      ‖∑ n ∈ Icc u v, f n‖ ≤ C * u) :
    ‖∑ n ∈ Icc p q, f n‖ ≤ 2 * C * q := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hpq : p ≤ q
    · by_cases hhalf : p ≤ q / 2
      · have hq0 : 0 < q := by omega
        have hleft := ih (q / 2) (Nat.div_lt_self hq0 (by norm_num))
          (fun u v hu huv hv hvu => hlocal u v hu huv (hv.trans (Nat.div_le_self _ _)) hvu)
        have hright := hlocal (q / 2 + 1) q (by omega) (by omega) le_rfl (by omega)
        have heq : Icc p q = Icc p (q / 2) ∪ Icc (q / 2 + 1) q := by
          ext n
          simp only [mem_Icc, mem_union]
          omega
        have hdis : Disjoint (Icc p (q / 2)) (Icc (q / 2 + 1) q) := by
          apply Finset.disjoint_left.mpr
          intro n hn hm
          simp only [mem_Icc] at hn hm
          omega
        rw [heq, Finset.sum_union hdis]
        have hmid : (3 : ℝ) * (q / 2 : ℕ) + 1 ≤ 2 * q := by
          exact_mod_cast (show 3 * (q / 2) + 1 ≤ 2 * q by omega)
        have hh := mul_le_mul_of_nonneg_left hmid hC
        calc
          _ ≤ ‖∑ n ∈ Icc p (q / 2), f n‖ + ‖∑ n ∈ Icc (q / 2 + 1) q, f n‖ := norm_add_le _ _
          _ ≤ 2 * C * (q / 2 : ℕ) + C * (q / 2 + 1 : ℕ) := add_le_add hleft hright
          _ ≤ _ := by push_cast; nlinarith
      · have hh := hlocal p q le_rfl hpq le_rfl (by omega)
        have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
        nlinarith [mul_le_mul_of_nonneg_left hpq' hC, mul_nonneg hC (show (0 : ℝ) ≤ q by positivity)]
    · have he : Icc p q = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      rw [he, Finset.sum_empty, norm_zero]
      positivity

theorem reciprocal_phase_long_interval (B : ℕ) (T Z : ℝ) (p q : ℕ)
    (hB : 4 ≤ B) (hT : 1 ≤ T) (hp : 1 ≤ p)
    (hlarge : (reciprocalConstantNat B : ℝ) * T ^ reciprocalPower B ≤ p)
    (hZlo : (q : ℝ) ^ 4 ≤ |Z|) (hZhi : |Z| ≤ (p : ℝ) ^ B) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 16 * q / T := by
  have hT0 : 0 < T := by linarith
  have hh := dyadic_interval_norm (fun n => phase (Z / n)) (8 / T) (by positivity) p q hp
    (by
      intro u v hpu huv hvq hvu
      rw [show (∑ n ∈ Icc u v, phase (Z / n)) =
          ∑ n ∈ Icc (u : ℤ) v, phase (Z / n) from sum_nat_int_Icc (fun n => phase (Z / n)) u v]
      have hu : (p : ℝ) ≤ u := by exact_mod_cast hpu
      have hv : (u : ℝ) ≤ q := by exact_mod_cast huv.trans hvq
      have hb := reciprocal_phase_power_bound B T u Z u v hB hT (hlarge.trans hu)
        ((pow_le_pow_left₀ (by positivity) hv 4).trans hZlo)
        (hZhi.trans (pow_le_pow_left₀ (by positivity) hu B))
        (by simp) (by exact_mod_cast hvu)
      convert hb using 1
      ring)
  convert hh using 1
  ring

theorem phase_second_moment {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α]
    (s : Finset β) (f : α → β → ℂ) (hnorm : ∀ i u, ‖f i u‖ = 1)
    (E : ℝ) (hE : 0 ≤ E)
    (hcorr : ∀ i j : α, i ≠ j →
      ‖∑ u ∈ s, f i u * (starRingEnd ℂ) (f j u)‖ ≤ E) :
    (∑ u ∈ s, ‖(∑ i, f i u) / (Fintype.card α : ℂ)‖ ^ 2) ≤
      (s.card : ℝ) / Fintype.card α + E := by
  classical
  let N := Fintype.card α
  have hN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  have hterm (i j : α) :
      (∑ u ∈ s, (f i u * (starRingEnd ℂ) (f j u)).re) ≤
        (if i = j then (s.card : ℝ) else 0) + E := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hnorm,
        one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
      linarith
    · rw [ite_eq_right hij, zero_add, ← Complex.re_sum]
      exact (Complex.re_le_norm _).trans (hcorr i j hij)
  have hsum : (∑ u ∈ s, ‖∑ i, f i u‖ ^ 2) ≤ (N : ℝ) * s.card + N ^ 2 * E := by
    simp_rw [complex_sum_norm_sq]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i : α, ∑ j : α, ∑ u ∈ s, (f i u * (starRingEnd ℂ) (f j u)).re := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ ≤ ∑ i : α, ∑ j : α, ((if i = j then (s.card : ℝ) else 0) + E) := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = _ := by simp [Finset.sum_add_distrib, N]; ring
  have heq : (∑ u ∈ s, ‖(∑ i, f i u) / (Fintype.card α : ℂ)‖ ^ 2) =
      (∑ u ∈ s, ‖∑ i, f i u‖ ^ 2) / (N : ℝ) ^ 2 := by
    change _ = _ / (Fintype.card α : ℝ) ^ 2
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    rw [norm_div, Complex.norm_natCast, div_pow]
  rw [heq]
  apply (div_le_iff₀ (sq_pos_of_pos hN)).mpr
  have halg : ((s.card : ℝ) / N + E) * (N : ℝ) ^ 2 = N * s.card + N ^ 2 * E := by
    field_simp
  rw [halg]
  exact hsum

end ShortEgyptian

end OAI
