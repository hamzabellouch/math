import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic

namespace OAI

/-! # Simultaneous selection from second and fourth moments

This finite probability argument combines the graph-signal second and
fourth moments with a first-moment bound for the clipping cost. All
averages are over the actual nonempty finite probability space.
-/

namespace KadisonKastler

open scoped BigOperators

/-- A fourth-moment signal and a bounded mean cost have a simultaneous
realization. These are the constants used before spectral clipping. -/
theorem exists_signal_and_cost_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (Z B : ι → ℝ) {s : ℝ} (hs : 0 < s)
    (hZ : ∀ i, 0 ≤ Z i) (hB : ∀ i, 0 ≤ B i)
    (hmean : (𝔼 i, Z i) = s)
    (hfourth : (𝔼 i, Z i ^ 2) ≤ 3 * s ^ 2)
    (hcost : (𝔼 i, B i) ≤ 10) :
    ∃ i, s / 2 ≤ Z i ∧ B i ≤ 240 := by
  classical
  by_contra h
  push Not at h
  let χ : ι → ℝ := fun i => if 240 < B i then 1 else 0
  have hχ (i : ι) : 0 ≤ χ i := by dsimp [χ]; split <;> norm_num
  have hχsq (i : ι) : χ i ^ 2 = χ i := by dsimp [χ]; split <;> norm_num
  have hmass : (𝔼 i, χ i) ≤ 1 / 24 := by
    have hi (i : ι) : 240 * χ i ≤ B i := by
      dsimp [χ]
      split_ifs with hb
      · linarith
      · simpa using hB i
    have ht : 240 * (𝔼 i, χ i) ≤ 10 := calc
      _ = (𝔼 i, 240 * χ i) := Finset.mul_expect Finset.univ χ 240
      _ ≤ (𝔼 i, B i) := Finset.expect_le_expect (fun i _ => hi i)
      _ ≤ 10 := hcost
    linarith
  have hsplit (i : ι) : Z i ≤ s / 2 + χ i * Z i := by
    by_cases hb : 240 < B i
    · simp only [χ, hb, ite_true, one_mul]
      linarith
    · have hz : Z i < s / 2 := lt_of_not_ge (fun hz => hb (h i hz))
      simp only [χ, hb, ite_false, zero_mul, add_zero]
      exact hz.le
  have hsignal : s / 2 ≤ 𝔼 i, χ i * Z i := by
    have ht : s ≤ s / 2 + (𝔼 i, χ i * Z i) := calc
      _ = (𝔼 i, Z i) := hmean.symm
      _ ≤ (𝔼 i, (s / 2 + χ i * Z i)) := Finset.expect_le_expect (fun i _ => hsplit i)
      _ = s / 2 + (𝔼 i, χ i * Z i) := by rw [Finset.expect_add_distrib]; simp
    linarith
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ χ Z
  simp only [hχsq] at hcs
  have hZsq : 0 ≤ 𝔼 i, Z i ^ 2 := Finset.expect_nonneg (fun i _ => sq_nonneg (Z i))
  have hbound : (𝔼 i, χ i * Z i) ^ 2 ≤ s ^ 2 / 8 := calc
    _ ≤ (𝔼 i, χ i) * (𝔼 i, Z i ^ 2) := hcs
    _ ≤ (1 / 24) * (𝔼 i, Z i ^ 2) := mul_le_mul_of_nonneg_right hmass hZsq
    _ ≤ (1 / 24) * (3 * s ^ 2) := mul_le_mul_of_nonneg_left hfourth (by norm_num)
    _ = s ^ 2 / 8 := by ring
  have hsig0 : 0 ≤ 𝔼 i, χ i * Z i :=
    Finset.expect_nonneg (fun i _ => mul_nonneg (hχ i) (hZ i))
  have hsquare : (s / 2) ^ 2 ≤ (𝔼 i, χ i * Z i) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hsignal 2
  nlinarith [sq_pos_of_pos hs]

end KadisonKastler

end OAI
