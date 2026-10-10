import OAI.Probability.ThorpShuffle.PrefixTests

namespace OAI

universe uΩ uα uΩ'

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem fairMass_test {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Fintype α]
    (a : Ω → α) (f : α → ℝ) :
    (∑ x, fairMass a x * f x) = mean (fun ω => f (a ω)) := by
  classical
  unfold fairMass mean
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

theorem fairMass_tv_le_of_test {Ω : Type uΩ} {Ω' : Type uΩ'} {α : Type uα} [Fintype Ω] [Fintype Ω'] [Fintype α]
    (a : Ω → α) (b : Ω' → α) (δ : ℝ)
    (h : ∀ f : α → ℝ, (∀ x, |f x| ≤ 1) →
      |mean (fun ω => f (a ω)) - mean (fun ω => f (b ω))| ≤ δ) :
    tv (fairMass a) (fairMass b) ≤ δ / 2 := by
  classical
  let f : α → ℝ := fun x => if 0 ≤ fairMass a x - fairMass b x then 1 else -1
  have hf : ∀ x, |f x| ≤ 1 := by intro x; dsimp [f]; split_ifs <;> norm_num
  have hh := h f hf
  rw [← fairMass_test, ← fairMass_test, ← Finset.sum_sub_distrib] at hh
  have hid (x : α) : fairMass a x * f x - fairMass b x * f x = |fairMass a x - fairMass b x| := by
    dsimp [f]
    split_ifs with hx
    · rw [abs_of_nonneg hx]; ring
    · rw [abs_of_neg (lt_of_not_ge hx)]; ring
  simp_rw [hid] at hh
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at hh
  unfold tv
  linarith

theorem marginal_tv_200 (d m k : ℕ)
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * m)
    (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (e : Fin k → Position (d + 2)) (he : Function.Injective e) :
    tv (fairMass (fun ω : History (d + 2) (200 * (d + 2)) =>
          (run (d + 2) (200 * (d + 2)) ω) ∘ e))
      (fairMass (fun g : State (d + 2) => g ∘ e)) ≤
    ((k : ℝ) / 2) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ m)) := by
  have h := fairMass_tv_le_of_test
    (fun ω : History (d + 2) (200 * (d + 2)) => (run (d + 2) (200 * (d + 2)) ω) ∘ e)
    (fun g : State (d + 2) => g ∘ e)
    ((k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ m)))
    (prefix_test_bound d m hm k hk e he)
  convert h using 1; ring

end Conditional

namespace Conditional

def marginalRate (d : ℕ) : ℝ :=
  Real.sqrt (3136 * ((1 / 32 : ℝ) ^ d + (2 ^ d : ℝ) ^ 3 * (9 / 10 : ℝ) ^ (2 ^ d)))

theorem marginalRate_tendsto : Tendsto marginalRate atTop (nhds 0) := by
  have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)
  have h₂ := (tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0 : ℝ) ≤ 9 / 10) (by norm_num : (9 / 10 : ℝ) < 1)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hh := ((h₁.add h₂).const_mul 3136).sqrt
  unfold marginalRate
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Function.comp_def,
    add_zero, mul_zero, Real.sqrt_zero] using hh

theorem marginal_tv_rate (d : ℕ) (e : Fin (7 * 2 ^ d) → Position (d + 1 + 2))
    (he : Function.Injective e) :
    tv (fairMass (fun ω : History (d + 1 + 2) (200 * (d + 1 + 2)) =>
          (run (d + 1 + 2) (200 * (d + 1 + 2)) ω) ∘ e))
      (fairMass (fun g : State (d + 1 + 2) => g ∘ e)) ≤ marginalRate d := by
  have hc : Fintype.card (Position (d + 1 + 2)) = 8 * 2 ^ d := by
    simp only [card_position, pow_add]
    norm_num
    omega
  have hh := marginal_tv_200 (d + 1) (2 ^ d) (7 * 2 ^ d)
    (by rw [hc]) (by rw [hc]; omega) e he
  simp only [Nat.add_assoc] at hh
  have hbound :
      (((7 * 2 ^ d : ℕ) : ℝ) / 2) *
        Real.sqrt ((Fintype.card (Position (d + 1 + 2)) : ℝ) *
          ((1 / 2 : ℝ) ^ (8 * (d + 3)) + 32 * (9 / 10 : ℝ) ^ (2 ^ d))) ≤ marginalRate d := by
    unfold marginalRate
    apply Real.le_sqrt_of_sq_le
    have hp : (1 / 2 : ℝ) ^ (8 * (d + 3)) ≤ (1 / 2 : ℝ) ^ (8 * d) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hid : (2 ^ d : ℝ) ^ 3 * (1 / 2 : ℝ) ^ (8 * d) = (1 / 32 : ℝ) ^ d := by
      rw [← pow_mul, Nat.mul_comm d 3, pow_mul, pow_mul, ← mul_pow]
      norm_num
    have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ (2 ^ d : ℝ) ^ 3)
    rw [hid] at hp'
    have hsq :
        (((7 * 2 ^ d : ℕ) : ℝ) / 2 *
          Real.sqrt ((Fintype.card (Position (d + 1 + 2)) : ℝ) *
            ((1 / 2 : ℝ) ^ (8 * (d + 3)) + 32 * (9 / 10 : ℝ) ^ (2 ^ d)))) ^ 2 =
        98 * (2 ^ d : ℝ) ^ 3 *
          ((1 / 2 : ℝ) ^ (8 * (d + 3)) + 32 * (9 / 10 : ℝ) ^ (2 ^ d)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hc]
      push_cast
      ring
    rw [hsq]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 32) d]
  have hone := le_trans hh hbound
  exact hone

theorem marginal_tendsto (e : ∀ d : ℕ, Fin (7 * 2 ^ d) → Position (d + 1 + 2))
    (he : ∀ d, Function.Injective (e d)) :
    Tendsto (fun d : ℕ =>
      tv (fairMass (fun ω : History (d + 1 + 2) (200 * (d + 1 + 2)) =>
          (run (d + 1 + 2) (200 * (d + 1 + 2)) ω) ∘ e d))
        (fairMass (fun g : State (d + 1 + 2) => g ∘ e d))) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds marginalRate_tendsto
  · intro d
    unfold tv
    positivity
  · intro d
    exact marginal_tv_rate d (e d) (he d)

end Conditional

end Thorp

end

end OAI
