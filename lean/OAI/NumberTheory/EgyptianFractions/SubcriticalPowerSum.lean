import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.DivisorMoment

/-- Integral comparison for a subcritical power, beginning at the integer two. -/
theorem shifted_power_sum_le (n : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 2) ^ (α - 1)) ≤
      (((n : ℝ) + 1) ^ α - 1) / α := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (α - 1))
      (Set.Icc 1 (1 + (n : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hsum := hanti.sum_le_integral
  have hi : (∫ x in (1 : ℝ)..1 + (n : ℝ), x ^ (α - 1)) =
      (((n : ℝ) + 1) ^ α - 1) / α := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < α - 1))]
    simp only [sub_add_cancel, Real.one_rpow, add_comm 1 (n : ℝ)]
  rw [hi] at hsum
  simpa only [Nat.cast_add, Nat.cast_one, show ∀ j : ℕ,
    (1 : ℝ) + ((j : ℝ) + 1) = (j : ℝ) + 2 by intro j; ring] using hsum

/-- Convenient coarse form of the same estimate. -/
theorem shifted_power_sum_le_div (n : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 2) ^ (α - 1)) ≤
      ((n : ℝ) + 1) ^ α / α := by
  refine (shifted_power_sum_le n hα0 hα1).trans ?_
  exact div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hα0.le

/-- Any collection of integers in [2,T] obeys the same subcritical power bound. -/
theorem finite_power_sum_le (T : ℕ) (s : Finset ℕ)
    (hs : ∀ a ∈ s, 2 ≤ a ∧ a ≤ T)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ a ∈ s, (a : ℝ) ^ (α - 1)) ≤ ((T : ℝ) + 1) ^ α / α := by
  have hsub : s ⊆ Finset.Ico 2 (T + 2) := by
    intro a ha
    obtain ⟨ha2, haT⟩ := hs a ha
    exact Finset.mem_Ico.mpr ⟨ha2, by omega⟩
  calc
    (∑ a ∈ s, (a : ℝ) ^ (α - 1)) ≤
        ∑ a ∈ Finset.Ico 2 (T + 2), (a : ℝ) ^ (α - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro a _ _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ = ∑ j ∈ Finset.range T, ((j : ℝ) + 2) ^ (α - 1) := by
      simpa only [zero_add, Nat.Ico_zero_eq_range, Nat.cast_add, Nat.cast_ofNat,
        add_comm (2 : ℝ)] using
        (Finset.sum_Ico_add (fun a : ℕ => (a : ℝ) ^ (α - 1)) 0 T 2).symm
    _ ≤ ((T : ℝ) + 1) ^ α / α := shifted_power_sum_le_div T hα0 hα1

/-- A uniform elementary logarithmic bound for geometric Euler factors. -/
theorem log_inv_one_sub_le {x ρ : ℝ} (hx0 : 0 ≤ x) (hxρ : x ≤ ρ) (hρ : ρ < 1) :
    Real.log ((1 - x)⁻¹) ≤ x / (1 - ρ) := by
  have hx : 0 < 1 - x := by linarith
  have hρpos : 0 < 1 - ρ := by linarith
  calc
    Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    _ = x / (1 - x) := by field_simp; ring
    _ ≤ x / (1 - ρ) := div_le_div_of_nonneg_left hx0 hρpos (by linarith)

/-- Logarithm of a finite geometric Euler product, requiring only a≥2, not primality. -/
theorem log_geometric_product_le (T : ℕ) (s : Finset ℕ)
    (hs : ∀ a ∈ s, 2 ≤ a ∧ a ≤ T)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Real.log (∏ a ∈ s, (1 - (a : ℝ) ^ (α - 1))⁻¹) ≤
      ((T : ℝ) + 1) ^ α / (α * (1 - (2 : ℝ) ^ (α - 1))) := by
  let ρ : ℝ := (2 : ℝ) ^ (α - 1)
  have hρ : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρpos : 0 < 1 - ρ := by linarith
  have hx (a : ℕ) (ha : a ∈ s) : 0 ≤ (a : ℝ) ^ (α - 1) ∧
      (a : ℝ) ^ (α - 1) ≤ ρ := by
    refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast (hs a ha).1)
      (by linarith)
  have hfac (a : ℕ) (ha : a ∈ s) : 0 < (1 - (a : ℝ) ^ (α - 1))⁻¹ := by
    apply inv_pos.mpr
    have := (hx a ha).2
    linarith
  rw [Real.log_prod (fun a ha => (hfac a ha).ne')]
  calc
    (∑ a ∈ s, Real.log ((1 - (a : ℝ) ^ (α - 1))⁻¹)) ≤
        ∑ a ∈ s, (a : ℝ) ^ (α - 1) / (1 - ρ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact log_inv_one_sub_le (hx a ha).1 (hx a ha).2 hρ
    _ = (∑ a ∈ s, (a : ℝ) ^ (α - 1)) / (1 - ρ) := by rw [Finset.sum_div]
    _ ≤ (((T : ℝ) + 1) ^ α / α) / (1 - ρ) :=
      div_le_div_of_nonneg_right (finite_power_sum_le T s hs hα0 hα1.le) hρpos.le
    _ = _ := by dsimp [ρ]; rw [div_div]

/-- Real cutoff version of the geometric Euler-product estimate. -/
theorem log_geometric_product_le_real {U : ℝ} (hU : 1 ≤ U) (s : Finset ℕ)
    (hs : ∀ a ∈ s, 2 ≤ a ∧ (a : ℝ) ≤ U)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Real.log (∏ a ∈ s, (1 - (a : ℝ) ^ (α - 1))⁻¹) ≤
      ((2 : ℝ) ^ α / (α * (1 - (2 : ℝ) ^ (α - 1)))) * U ^ α := by
  have hU0 : 0 ≤ U := by linarith
  have hρ : (2 : ℝ) ^ (α - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < α * (1 - (2 : ℝ) ^ (α - 1)) := by positivity
  have hnat : ∀ a ∈ s, 2 ≤ a ∧ a ≤ ⌊U⌋₊ := by
    intro a ha
    exact ⟨(hs a ha).1, Nat.le_floor (hs a ha).2⟩
  refine (log_geometric_product_le ⌊U⌋₊ s hnat hα0 hα1).trans ?_
  have hfloor : (⌊U⌋₊ : ℝ) + 1 ≤ 2 * U := by
    have := Nat.floor_le hU0
    linarith
  have hp : ((⌊U⌋₊ : ℝ) + 1) ^ α ≤ (2 * U) ^ α :=
    Real.rpow_le_rpow (by positivity) hfloor hα0.le
  calc
    ((⌊U⌋₊ : ℝ) + 1) ^ α / (α * (1 - (2 : ℝ) ^ (α - 1))) ≤
        (2 * U) ^ α / (α * (1 - (2 : ℝ) ^ (α - 1))) :=
      div_le_div_of_nonneg_right hp hden.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) hU0]; ring

/-- The small-prime Rankin product grows at most exponentially in S^(2/5).
No primality hypothesis is needed, since summing over all integers is an upper bound. -/
theorem small_prime_rankin_product_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ℝ), 1 ≤ S → ∀ s : Finset ℕ,
      (∀ p ∈ s, 2 ≤ p ∧ (p : ℝ) ≤ S ^ (4 : ℕ)) →
      Real.log (∏ p ∈ s, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹) ≤
        C * S ^ (2 / 5 : ℝ) := by
  let C : ℝ := (2 : ℝ) ^ (1 / 10 : ℝ) /
    ((1 / 10 : ℝ) * (1 - (2 : ℝ) ^ (-(9 / 10 : ℝ))))
  have hρ : (2 : ℝ) ^ (-(9 / 10 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro S hS s hs
  have hS0 : 0 ≤ S := by linarith
  have hU : 1 ≤ S ^ (4 : ℕ) := one_le_pow₀ hS
  have h := log_geometric_product_le_real hU s hs
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (1 / 10 : ℝ) < 1)
  norm_num only [show (1 / 10 : ℝ) - 1 = -(9 / 10 : ℝ) by norm_num] at h
  change _ ≤ C * (S ^ (4 : ℕ)) ^ (1 / 10 : ℝ) at h
  have heq : (S ^ (4 : ℕ)) ^ (1 / 10 : ℝ) = S ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]
    norm_num
  simpa only [heq] using h

end Problem337.DivisorMoment

end

end OAI
