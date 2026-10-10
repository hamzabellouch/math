import OAI.Analysis.MarkovType.FiniteWeightedHolder
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

theorem sum_le_of_sum_pow_le {n q : ℕ} (hq : 2 ≤ q)
    {D B : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hpow : ∑ i, r i ^ q ≤ D * B ^ q) :
    ∑ i, r i ≤ D ^ (1 / (q : ℝ)) *
      (n : ℝ) ^ (1 - 1 / (q : ℝ)) * B := by
  have hqR : (1 : ℝ) < (q : ℝ) :=
    Nat.one_lt_cast.mpr (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hq)
  have hqNat : q ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hq)
  have hroot_nonneg : (0 : ℝ) ≤ 1 / (q : ℝ) :=
    (one_div_pos.mpr (zero_lt_one.trans hqR)).le
  have hpq := Real.HolderConjugate.conjExponent hqR
  have hexponent : 1 / Real.conjExponent (q : ℝ) = 1 - 1 / (q : ℝ) := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hholder :
      (∑ i, r i) ≤ (∑ i, r i ^ q) ^ (1 / (q : ℝ)) *
        (n : ℝ) ^ (1 - 1 / (q : ℝ)) := by
    have hh := finite_weighted_holder_univ
      (w := fun _ : Fin n => (1 : ℝ)) (a := r) (b := fun _ => (1 : ℝ))
      hpq (fun _ => zero_le_one) hr (fun _ => zero_le_one)
    simpa only [one_mul, mul_one, Real.one_rpow, Real.rpow_natCast,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      hexponent] using hh
  have hsum_nonneg : 0 ≤ ∑ i, r i ^ q :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (hr i) q)
  have hroot : (∑ i, r i ^ q) ^ (1 / (q : ℝ)) ≤ D ^ (1 / (q : ℝ)) * B := by
    calc
      (∑ i, r i ^ q) ^ (1 / (q : ℝ)) ≤ (D * B ^ q) ^ (1 / (q : ℝ)) :=
        Real.rpow_le_rpow hsum_nonneg hpow hroot_nonneg
      _ = D ^ (1 / (q : ℝ)) * (B ^ q) ^ (1 / (q : ℝ)) :=
        Real.mul_rpow hD.le (pow_nonneg hB q)
      _ = D ^ (1 / (q : ℝ)) * B := by
        simp only [one_div, Real.pow_rpow_inv_natCast hB hqNat]
  calc
    (∑ i, r i) ≤ (∑ i, r i ^ q) ^ (1 / (q : ℝ)) *
        (n : ℝ) ^ (1 - 1 / (q : ℝ)) := hholder
    _ ≤ (D ^ (1 / (q : ℝ)) * B) * (n : ℝ) ^ (1 - 1 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = D ^ (1 / (q : ℝ)) * (n : ℝ) ^ (1 - 1 / (q : ℝ)) * B := by ring

end MarkovSuperreflexivity

end OAI
