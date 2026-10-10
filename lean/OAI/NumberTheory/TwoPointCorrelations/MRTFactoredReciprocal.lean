import OAI.NumberTheory.TwoPointCorrelations.MRTDivisorPairs
import OAI.NumberTheory.TwoPointCorrelations.MRTEulerProducts
import Mathlib.NumberTheory.EulerProduct.Basic

namespace OAI

/-! Finite reciprocal mass of integers supported on a prime band. Together
with the gcd-triple injection this supplies the divisor-square mean bound
in MR's mixed prime/cofactor moment without an additional sieve input. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtFactoredUpTo (P : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => n ∈ Nat.factoredNumbers P)

lemma mrtFactoredUpTo_pos (P : Finset ℕ) (N : ℕ)
    {d : ℕ} (hd : d ∈ mrtFactoredUpTo P N) : 0 < d :=
  (mem_Icc.mp (mem_filter.mp hd).1).1

lemma mrtFactoredUpTo_divisor_closed (P : Finset ℕ) (N : ℕ)
    {d : ℕ} (hd : d ∈ mrtFactoredUpTo P N)
    {e : ℕ} (he : 0 < e) (hed : e ∣ d) : e ∈ mrtFactoredUpTo P N := by
  obtain ⟨hdN, hdP⟩ := mem_filter.mp hd
  exact mem_filter.mpr ⟨mem_Icc.mpr
    ⟨he, (Nat.le_of_dvd (mem_Icc.mp hdN).1 hed).trans (mem_Icc.mp hdN).2⟩,
    Nat.mem_factoredNumbers_of_dvd hdP hed⟩

lemma mrt_reciprocal_prime_power_series {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => (1 : ℝ) / (p ^ k : ℕ)) (1 - (1 : ℝ) / p)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hi : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hp1
  simpa only [Nat.cast_pow, one_div, inv_pow] using
    hasSum_geometric_of_lt_one (by positivity : 0 ≤ (p : ℝ)⁻¹) hi

lemma mrt_reciprocal_prime_power_norm {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖(1 : ℝ) / (p ^ k : ℕ)‖) := by
  have he (k : ℕ) : ‖(1 : ℝ) / (p ^ k : ℕ)‖ = 1 / (p ^ k : ℕ) :=
    Real.norm_of_nonneg (by positivity)
  simpa only [he] using (mrt_reciprocal_prime_power_series hp).summable

lemma mrt_factored_reciprocal_series (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers P => (1 : ℝ) / (n.val : ℕ))
      (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) := by
  have h1 : (1 : ℝ) / (1 : ℕ) = 1 := by norm_num
  have hm {m n : ℕ} (_h : m.Coprime n) :
      (1 : ℝ) / (m * n : ℕ) = (1 / (m : ℝ)) * (1 / (n : ℝ)) := by
    simp only [Nat.cast_mul, one_div, mul_inv_rev]
    ring
  obtain ⟨_, he⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun n : ℕ => (1 : ℝ) / n) h1 (fun {_ _} h => hm h)
    (fun {_} h => mrt_reciprocal_prime_power_norm h) P
  have hf : P.filter Nat.Prime = P := filter_true_of_mem hP
  rw [hf] at he
  have hprod : (∏ p ∈ P, ∑' k : ℕ, (1 : ℝ) / (p ^ k : ℕ)) =
      ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_congr rfl (fun p hp => (mrt_reciprocal_prime_power_series (hP p hp)).tsum_eq)
  exact hprod ▸ he

theorem mrt_factored_reciprocal_sum (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ d ∈ mrtFactoredUpTo P N, 1 / (d : ℝ)) ≤
      ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
  have hi : HasSum ((Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n))
      (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) :=
    (hasSum_subtype_iff_indicator (s := Nat.factoredNumbers P)
      (f := fun n : ℕ => (1 : ℝ) / n)).mp (mrt_factored_reciprocal_series P hP)
  rw [← hi.tsum_eq]
  calc
    _ = ∑ d ∈ mrtFactoredUpTo P N,
        (Nat.factoredNumbers P).indicator (fun n : ℕ => (1 : ℝ) / n) d := by
      apply sum_congr rfl
      intro d hd
      exact (Set.indicator_of_mem (mem_filter.mp hd).2 (fun n : ℕ => (1 : ℝ) / n)).symm
    _ ≤ _ := hi.summable.sum_le_tsum _ (fun d _ =>
      Set.indicator_nonneg (fun n _ => by positivity) d)

theorem mrt_factored_divisor_second_moment (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N,
      (((mrtFactoredUpTo P N).filter (fun d => d ∣ n)).card : ℝ) ^ 2) ≤
      (N : ℝ) * (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ^ 3 := by
  apply (mrt_divisor_count_second_moment (mrtFactoredUpTo P N)
    (fun _ hd => mrtFactoredUpTo_pos P N hd)
    (fun _ hd _ he hed => mrtFactoredUpTo_divisor_closed P N hd he hed) N).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity))
    (mrt_factored_reciprocal_sum P hP N) 3

lemma mrt_prime_reciprocal_euler_bound {p : ℕ} (hp : p.Prime) :
    (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hnon : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hhalf : (1 : ℝ) / p ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hp2
  have hz : ‖(((1 : ℝ) / p : ℝ) : ℂ)‖ ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnon] using hhalf
  have he := mrt_local_euler_bound hz
  have hpos : 0 < 1 - (1 : ℝ) / p := by linarith
  have hn : ‖(1 - (((1 : ℝ) / p : ℝ) : ℂ))⁻¹‖ = (1 - (1 : ℝ) / p)⁻¹ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (1 - (1 : ℝ) / p)⁻¹)]
  simpa only [hn, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnon] using he

theorem mrt_factored_divisor_exponential_moment (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N,
      (((mrtFactoredUpTo P N).filter (fun d => d ∣ n)).card : ℝ) ^ 2) ≤
      (N : ℝ) * Real.exp (3 * ∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2)) := by
  apply (mrt_factored_divisor_second_moment P hP N).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  have hprod : (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) ≤
      Real.exp (∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2)) := by
    rw [Real.exp_sum]
    apply prod_le_prod₀
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
      have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
    · intro p hp
      exact mrt_prime_reciprocal_euler_bound (hP p hp)
  have hn : 0 ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hi : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    exact inv_nonneg.mpr (by linarith)
  calc
    _ ≤ (Real.exp (∑ p ∈ P, (1 / (p : ℝ) + (1 / (p : ℝ)) ^ 2))) ^ 3 :=
      pow_le_pow_left₀ hn hprod 3
    _ = _ := by rw [← Real.exp_nat_mul]; norm_num

end TwoPointCorrelations

end OAI
