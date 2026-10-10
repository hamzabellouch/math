import OAI.NumberTheory.Ostmann.Construction.RepeatRemovalAsymptotics
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteWitnessProbability

namespace OAI

/-! # Numerical budgets for the original Fourier moments -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventual_two_pow_moment_budget :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (K : ℝ),
      1 ≤ k → (k : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K →
      (2 : ℝ) ^ k ≤ Real.exp (K / 10) := by
  filter_upwards [eventual_repeat_power_budget 1 (1 / 10) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with T hb hT k K hk hkU hK
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbase : (2 : ℝ) ≤ 16 * 1 * T * (k : ℝ) ^ 3 := by
    have hpow : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hk1
    nlinarith
  have hh := hb k K hkU hK
  norm_num only [one_pow, mul_one] at hh
  exact (pow_le_pow_left₀ (by norm_num) hbase k).trans (by simpa only [one_mul, mul_one, div_eq_mul_inv, mul_comm] using hh)

theorem original_outer_moment_budget (T K : ℝ) (k : ℕ)
    (hK : 3000 ≤ K) (hKT : K ≤ T) (hpow : (2 : ℝ) ^ k ≤ Real.exp (K / 10)) :
    (2 : ℝ) ^ k * (Real.exp ((-799 / 1000 : ℝ) * K) +
      Real.exp (-10 * T) + Real.exp (-113 * T)) ≤ 1 := by
  have hK0 : 0 ≤ K := by linarith
  have h₁ : Real.exp (K / 10) * Real.exp ((-799 / 1000 : ℝ) * K) ≤ Real.exp (-K / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h₂ : Real.exp (K / 10) * Real.exp (-10 * T) ≤ Real.exp (-K / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h₃ : Real.exp (K / 10) * Real.exp (-113 * T) ≤ Real.exp (-K / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have he : 3 * Real.exp (-K / 2) ≤ 1 := by
    have hh : (3 : ℝ) ≤ Real.exp (K / 2) := by linarith [Real.add_one_le_exp (K / 2)]
    rw [show -K / 2 = -(K / 2) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    simpa using hh
  calc
    _ ≤ Real.exp (K / 10) * (Real.exp ((-799 / 1000 : ℝ) * K) +
        Real.exp (-10 * T) + Real.exp (-113 * T)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ 3 * Real.exp (-K / 2) := by nlinarith only [h₁, h₂, h₃]
    _ ≤ 1 := he

/-- After subtracting the large, outer, and failed-witness contributions,
the second moment gives the manuscript's positive witness probability. -/
theorem original_moment_witness_probability {ι : Type*} (S : Finset ι) (E : ι → Prop)
    [DecidablePred E] (F f g o : ι → ℝ) (T K : ℝ)
    (hK : 3000 ≤ K) (hKT : K ≤ T)
    (hpoint : ∀ i ∈ S, F i ≤ f i + g i + o i)
    (hfirst : Real.exp ((3 / 200 : ℝ) * K) ≤ (S.card : ℝ)⁻¹ * (∑ i ∈ S, F i))
    (hsecond : (S.card : ℝ)⁻¹ * (∑ i ∈ S, f i ^ 2) ≤
      (Real.exp ((103 / 1000 : ℝ) * K) + Real.exp (-10 * T) + Real.exp (-113 * T)) ^ 2)
    (hlarge : (S.card : ℝ)⁻¹ * (∑ i ∈ S, g i) ≤
      Real.exp ((9 / 1000 : ℝ) * K) + Real.exp (-10 * T) + Real.exp (-113 * T))
    (houter : (S.card : ℝ)⁻¹ * (∑ i ∈ S, o i) ≤ 1)
    (hfail : (S.card : ℝ)⁻¹ * (∑ i ∈ S.filter (fun i => ¬E i), f i) ≤
      Real.exp ((-797 / 1000 : ℝ) * K) + Real.exp (-10 * T) + Real.exp (-113 * T)) :
    Real.exp (-K / 5) ≤ (S.card : ℝ)⁻¹ * (S.filter E).card := by
  have hK0 : 0 ≤ K := by linarith
  have hT0 : 0 ≤ T := hK0.trans hKT
  have he10 : Real.exp (-10 * T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he113 : Real.exp (-113 * T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hef : Real.exp ((-797 / 1000 : ℝ) * K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hA : 24 ≤ Real.exp ((3 / 200 : ℝ) * K) := by
    linarith [Real.add_one_le_exp ((3 / 200 : ℝ) * K)]
  have hratio : Real.exp ((9 / 1000 : ℝ) * K) ≤ Real.exp ((3 / 200 : ℝ) * K) / 4 := by
    have he : (4 : ℝ) ≤ Real.exp ((3 / 500 : ℝ) * K) := by
      linarith [Real.add_one_le_exp ((3 / 500 : ℝ) * K)]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    calc
      _ ≤ Real.exp ((9 / 1000 : ℝ) * K) * Real.exp ((3 / 500 : ℝ) * K) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint)
    (inv_nonneg.mpr (Nat.cast_nonneg S.card) : 0 ≤ (S.card : ℝ)⁻¹)
  simp only [Finset.sum_add_distrib, mul_add] at hsum
  have hsplit := Finset.sum_filter_add_sum_filter_not S E f
  have hsplit' := congrArg (fun x : ℝ => (S.card : ℝ)⁻¹ * x) hsplit
  rw [mul_add] at hsplit'
  apply finite_witness_probability S (S.filter E) (Finset.filter_subset _ _) f K (by linarith)
  · linarith
  · have hB : 2 ≤ Real.exp ((103 / 1000 : ℝ) * K) := by
      linarith [Real.add_one_le_exp ((103 / 1000 : ℝ) * K)]
    apply hsecond.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith

end Ostmann

end OAI
