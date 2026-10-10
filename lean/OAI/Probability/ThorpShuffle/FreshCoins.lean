import OAI.Probability.ThorpShuffle.WalshFlow

namespace OAI

universe uΩ uι uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def expectedBand (d : ℕ) (v : CenteredState (d + 1)) (t j : ℕ) : ℝ :=
  mean (fun ω : History (d + 1) t =>
    bandEnergy (d + 1) (iterateState d v t ω).weight j / 2 ^ (d + 1))

def expectedNoise (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) : ℝ :=
  mean (fun ω : History (d + 1) t =>
    oneFreeEnergy d (iterateState d v t ω).free (iterateState d v t ω).weight)

theorem mean_div_const {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    mean (fun ω => f ω / a) = mean f / a := by
  simpa only [div_eq_mul_inv] using mean_mul_const f a⁻¹

@[simp] theorem expectedBand_zero (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedBand d v t 0 = expectedEnergy d v t := by
  unfold expectedBand expectedEnergy
  apply mean_congr
  intro ω
  rw [bandEnergy_zero]
  simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]

@[simp] theorem expectedBand_full (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedBand d v t (d + 1) = 0 := by
  unfold expectedBand
  have hz (ω : History (d + 1) t) :
      bandEnergy (d + 1) (iterateState d v t ω).weight (d + 1) / 2 ^ (d + 1) = 0 := by
    rw [bandEnergy_full, (iterateState d v t ω).mass_zero]
    simp
  simp_rw [hz]
  exact mean_zero

theorem two_pow_ratio (d j : ℕ) (hj : j ≤ d) :
    (2 : ℝ) ^ (d - j) / 2 ^ (d + 1) = (1 / 2 : ℝ) ^ (j + 1) := by
  have hd : d + 1 = (d - j) + (j + 1) := by omega
  rw [hd, pow_add, div_mul_eq_div_div, div_self (by positivity), div_pow, one_pow]

theorem expectedBand_succ (d : ℕ) (v : CenteredState (d + 1)) (t j : ℕ)
    (hj : j < d + 1) :
    expectedBand d v (t + 1) j = expectedBand d v t (j + 1) +
      (1 / 2 : ℝ) ^ (j + 1) * expectedNoise d v t := by
  unfold expectedBand expectedNoise
  rw [mean_history_succ]
  have hstep (ω : History (d + 1) t) :
      mean (fun c : Coins (d + 1) =>
        bandEnergy (d + 1) (iterateState d v (t + 1) (Fin.snoc ω c)).weight j /
          2 ^ (d + 1)) =
      bandEnergy (d + 1) (iterateState d v t ω).weight (j + 1) / 2 ^ (d + 1) +
        (1 / 2 : ℝ) ^ (j + 1) *
          oneFreeEnergy d (iterateState d v t ω).free (iterateState d v t ω).weight := by
    simp only [iterateState, Fin.snoc_last, Fin.snoc_castSucc, nextState]
    rw [mean_div_const, mean_bandEnergy_physicalFlow d j (by omega)
      _ _ (iterateState d v t ω).supported, add_div]
    rw [← div_mul_eq_mul_div, two_pow_ratio d j (by omega)]
  simp_rw [hstep]
  rw [mean_add, mean_const_mul]

theorem expectedEnergy_recurrence (d : ℕ) (v : CenteredState (d + 1))
    (t : ℕ) (ht : d + 1 ≤ t) :
    expectedEnergy d v t = ∑ j ∈ Finset.range (d + 1),
      (1 / 2 : ℝ) ^ (j + 1) * expectedNoise d v (t - 1 - j) := by
  simpa only [expectedBand_zero] using
    energy_of_spectral_tracks (d + 1) (expectedBand d v) (expectedNoise d v)
      (expectedBand_succ d v) (expectedBand_full d v) t ht

end Conditional

namespace Conditional

theorem mean_product_bits {ι : Type uι} [Fintype ι] [DecidableEq ι] (f : ι → Bool → ℝ) :
    mean (fun c : ι → Bool => ∏ i, f i (c i)) =
      ∏ i, (f i false + f i true) / 2 := by
  classical
  unfold mean
  rw [← Fintype.prod_sum]
  simp only [Fintype.sum_bool, add_comm (f _ true)]
  rw [Finset.prod_div_distrib]
  simp [Fintype.card_pi, Fintype.card_bool]

def pairFreeCount {α : Type uα} [Fintype α] (B : Bool × α → Bool) : ℕ :=
  ∑ i, ((B (false, i)).toNat + (B (true, i)).toNat)

def pairHalfCount {α : Type uα} [Fintype α] (B : Bool × α → Bool)
    (c : α → Bool) (h : Bool) : ℕ :=
  ∑ i, (B (h ^^ c i, i)).toNat

theorem local_balance_factor (u v h : Bool) :
    mean (fun c : Bool => (5 / 4 : ℝ) ^ (u.toNat + v.toNat) *
      (4 / 5 : ℝ) ^ (4 * (if h ^^ c then v else u).toNat)) ≤
        (9 / 10 : ℝ) ^ (u.toNat + v.toNat) := by
  cases u <;> cases v <;> cases h <;> norm_num [mean, Fintype.sum_bool]

theorem balance_exponential_mean {α : Type uα} [Fintype α] [DecidableEq α]
    (B : Bool × α → Bool) (h : Bool) :
    mean (fun c : α → Bool => (5 / 4 : ℝ) ^ pairFreeCount B *
      (4 / 5 : ℝ) ^ (4 * pairHalfCount B c h)) ≤
        (9 / 10 : ℝ) ^ pairFreeCount B := by
  classical
  have hprod (c : α → Bool) :
      (5 / 4 : ℝ) ^ pairFreeCount B * (4 / 5 : ℝ) ^ (4 * pairHalfCount B c h) =
      ∏ i, ((5 / 4 : ℝ) ^ ((B (false, i)).toNat + (B (true, i)).toNat) *
        (4 / 5 : ℝ) ^ (4 * (B (h ^^ c i, i)).toNat)) := by
    simp only [pairFreeCount, pairHalfCount, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum,
      Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [mean_product_bits (fun i (c : Bool) =>
    (5 / 4 : ℝ) ^ ((B (false, i)).toNat + (B (true, i)).toNat) *
        (4 / 5 : ℝ) ^ (4 * (B (h ^^ c, i)).toNat))]
  rw [pairFreeCount, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro i _
    positivity
  · intro i _
    have hlocal := local_balance_factor (B (false, i)) (B (true, i)) h
    have hbit (c : Bool) : B (h ^^ c, i) = if h ^^ c then B (true, i) else B (false, i) := by
      cases (h ^^ c) <;> rfl
    simp only [hbit]
    cases h <;> simpa [mean, Fintype.sum_bool, add_comm] using hlocal

theorem pair_half_balance {α : Type uα} [Fintype α] [DecidableEq α]
    (B : Bool × α → Bool) (h : Bool) :
    mean (fun c : α → Bool =>
      if 4 * pairHalfCount B c h < pairFreeCount B then (1 : ℝ) else 0) ≤
        (9 / 10 : ℝ) ^ pairFreeCount B := by
  apply le_trans (mean_le_mean (fun c => ?_)) (balance_exponential_mean B h)
  by_cases hc : 4 * pairHalfCount B c h < pairFreeCount B
  · rw [ite_eq_left hc]
    have hp : (5 / 4 : ℝ) ^ (4 * pairHalfCount B c h) ≤
        (5 / 4 : ℝ) ^ pairFreeCount B :=
      pow_le_pow_right₀ (by norm_num) hc.le
    have hr : (4 / 5 : ℝ) = (5 / 4 : ℝ)⁻¹ := by norm_num
    rw [hr, inv_pow, ← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using hp)
  · rw [ite_eq_right hc]
    positivity

theorem pair_both_half_balance {α : Type uα} [Fintype α] [DecidableEq α]
    (B : Bool × α → Bool) :
    mean (fun c : α → Bool =>
      if (4 * pairHalfCount B c false < pairFreeCount B) ∨
        (4 * pairHalfCount B c true < pairFreeCount B) then (1 : ℝ) else 0) ≤
          2 * (9 / 10 : ℝ) ^ pairFreeCount B := by
  have hm : mean (fun c : α → Bool =>
      if (4 * pairHalfCount B c false < pairFreeCount B) ∨
        (4 * pairHalfCount B c true < pairFreeCount B) then (1 : ℝ) else 0) ≤
      mean (fun c : α → Bool =>
        (if 4 * pairHalfCount B c false < pairFreeCount B then (1 : ℝ) else 0) +
        (if 4 * pairHalfCount B c true < pairFreeCount B then (1 : ℝ) else 0)) := by
    apply mean_le_mean
    intro c
    split_ifs <;> norm_num at *
    all_goals omega
  rw [mean_add] at hm
  linarith [pair_half_balance B false, pair_half_balance B true]

end Conditional

end Thorp

end

end OAI
