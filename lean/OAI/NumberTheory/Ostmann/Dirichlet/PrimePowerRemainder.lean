import OAI.NumberTheory.Ostmann.Dirichlet.LogDerivativeRight
import PrimeNumberTheoremAnd.Erdos970.MertensClassical

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators
open ArithmeticFunction

noncomputable def higherPrimePowerWeight (n : ℕ) : ℝ :=
  if n.Prime then 0 else vonMangoldt n / (n : ℝ)

lemma higherPrimePowerWeight_nonneg (n : ℕ) : 0 ≤ higherPrimePowerWeight n := by
  unfold higherPrimePowerWeight
  split_ifs <;> positivity

@[simp] lemma higherPrimePowerWeight_zero : higherPrimePowerWeight 0 = 0 := by
  simp [higherPrimePowerWeight]

lemma sum_higherPrimePowerWeight_Ioc_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, higherPrimePowerWeight n ≤ Erdos970.Mertens.E₁ := by
  by_cases hN : N = 0
  · subst N
    simpa using (tsum_nonneg Erdos970.Mertens.E₁.summand_nonneg)
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have h := Erdos970.Mertens.E₁Λ.le_E₁p_add_E₁ hn
  simp only [Erdos970.Mertens.E₁Λ, Erdos970.Mertens.E₁p, Nat.floor_natCast] at h
  have he : ∑ n ∈ Finset.Ioc 0 N, higherPrimePowerWeight n =
      (∑ n ∈ Finset.Ioc 0 N, vonMangoldt n / (n : ℝ)) -
        ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log p / (p : ℝ) := by
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime
    · simp [higherPrimePowerWeight, hp, vonMangoldt_apply_prime hp]
    · simp [higherPrimePowerWeight, hp]
  rw [he]
  linarith

lemma sum_higherPrimePowerWeight_range_le (N : ℕ) :
    ∑ n ∈ Finset.range N, higherPrimePowerWeight n ≤ Erdos970.Mertens.E₁ := by
  have hset : Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), higherPrimePowerWeight n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun n _ _ => higherPrimePowerWeight_nonneg n)
    _ = ∑ n ∈ Finset.Ioc 0 N, higherPrimePowerWeight n := by
      rw [hset, Finset.sum_insert (by simp)]
      simp only [higherPrimePowerWeight_zero, zero_add]
    _ ≤ _ := sum_higherPrimePowerWeight_Ioc_le N

theorem summable_higherPrimePowerWeight : Summable higherPrimePowerWeight :=
  summable_of_sum_range_le higherPrimePowerWeight_nonneg sum_higherPrimePowerWeight_range_le

theorem tsum_higherPrimePowerWeight_le : ∑' n, higherPrimePowerWeight n ≤ Erdos970.Mertens.E₁ :=
  Real.tsum_le_of_sum_range_le higherPrimePowerWeight_nonneg sum_higherPrimePowerWeight_range_le

lemma higherPrimePower_rpow_le {sigma : ℝ} (hs : 1 ≤ sigma) (n : ℕ) :
    (if n.Prime then 0 else vonMangoldt n / (n : ℝ) ^ sigma) ≤ higherPrimePowerWeight n := by
  by_cases hp : n.Prime
  · simp [hp, higherPrimePowerWeight]
  by_cases hn : n = 0
  · subst n
    simp [higherPrimePowerWeight]
  simp only [hp, ite_false, higherPrimePowerWeight]
  apply div_le_div_of_nonneg_left vonMangoldt_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hn)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ n by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs

end Ostmann.Dirichlet

end OAI
