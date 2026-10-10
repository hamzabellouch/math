import Mathlib
import OAI.Combinatorics.KMedian.PCP.Linearity

namespace OAI

section Inline_PCPFiniteTest

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

noncomputable def testRate {S : Type} [Fintype S] (reject : S → Prop) : ℝ := by
  classical
  exact 𝔼 s, if reject s then 1 else 0

section Rates
variable {S T : Type} [Fintype S] [Fintype T]

theorem testRate_nonneg (p : S → Prop) : 0 ≤ testRate p := by
  classical
  exact expect_nonneg (by intro s _; split_ifs <;> norm_num)

theorem testRate_le_one (p : S → Prop) [Nonempty S] : testRate p ≤ 1 := by
  classical
  exact expect_le univ_nonempty (by intro s _; split_ifs <;> norm_num)

theorem testRate_congr {p q : S → Prop} (h : ∀ s, p s ↔ q s) : testRate p = testRate q := by
  classical
  apply expect_congr rfl
  intro s _
  simp only [h s]

theorem testRate_mono {p q : S → Prop} (h : ∀ s, p s → q s) : testRate p ≤ testRate q := by
  classical
  apply expect_le_expect
  intro s _
  by_cases hp : p s
  · simp [hp, h s hp]
  · simp only [ite_eq_right hp]; split_ifs <;> norm_num

theorem testRate_or_le (p q : S → Prop) :
    testRate (fun s => p s ∨ q s) ≤ testRate p + testRate q := by
  classical
  unfold testRate
  rw [← expect_add_distrib]
  apply expect_le_expect
  intro s _
  by_cases hp : p s <;> by_cases hq : q s <;> simp [hp, hq]

theorem testRate_union_bound {p q r : S → Prop} (h : ∀ s, p s → q s ∨ r s) :
    testRate p ≤ testRate q + testRate r :=
  (testRate_mono h).trans (testRate_or_le q r)

theorem testRate_false : testRate (fun _ : S => False) = 0 := by
  classical
  simp [testRate]

theorem testRate_true [Nonempty S] : testRate (fun _ : S => True) = 1 := by
  classical
  simp [testRate]

theorem testRate_complement (p : S → Prop) [Nonempty S] :
    testRate p + testRate (fun s => ¬ p s) = 1 := by
  classical
  unfold testRate
  rw [← expect_add_distrib]
  convert Fintype.expect_one (ι := S) (M := ℝ) using 1
  apply expect_congr rfl
  intro s _
  by_cases hp : p s <;> simp [hp]

theorem testRate_equiv (e : S ≃ T) (p : T → Prop) :
    testRate (fun s => p (e s)) = testRate p := by
  classical
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem testRate_eq_count (p : S → Prop) [DecidablePred p] :
    testRate p = ((univ.filter p).card : ℝ) / Fintype.card S := by
  classical
  rw [testRate, Fintype.expect_eq_sum_div_card]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  apply sum_congr rfl
  intro s _
  split_ifs <;> rfl

theorem testRate_prod (p : S → T → Prop) :
    testRate (fun z : S × T => p z.1 z.2) = 𝔼 s, testRate (p s) := by
  classical
  unfold testRate
  rw [← univ_product_univ, expect_product]

theorem testRate_fst (p : S → Prop) [Nonempty T] :
    testRate (fun z : S × T => p z.1) = testRate p := by
  classical
  rw [testRate_prod (fun s (_ : T) => p s)]
  unfold testRate
  simp only [Fintype.expect_const]

theorem testRate_snd (p : T → Prop) [Nonempty S] :
    testRate (fun z : S × T => p z.2) = testRate p := by
  classical
  rw [testRate_prod (fun (_ : S) t => p t)]
  exact Fintype.expect_const _

theorem testRate_fibers_le (p : S → T → Prop) [Nonempty S] (c : ℝ)
    (h : ∀ s, testRate (p s) ≤ c) :
    testRate (fun z : S × T => p z.1 z.2) ≤ c := by
  rw [testRate_prod]
  exact expect_le univ_nonempty (fun s _ => h s)

end Rates

section LinearityRates
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H]
  [DecidableEq H]

noncomputable def linearityRate (f : G → H) : ℝ :=
  testRate (fun p : G × G => f (p.1 + p.2) ≠ f p.1 + f p.2)

theorem linearityRate_eq (f : G → H) :
    linearityRate f = (linearityRejects f : ℝ) / (Fintype.card G : ℝ)^2 := by
  classical
  rw [linearityRate, testRate_eq_count]
  simp only [linearityRejects, Fintype.card_prod, Nat.cast_mul, pow_two]

theorem linearityRate_small (f : G → H) (h : linearityRate f < 1/6) :
    6 * linearityRejects f < Fintype.card G * Fintype.card G := by
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [linearityRate_eq, div_lt_iff₀ (sq_pos_of_pos hn)] at h
  have hh : (6 : ℝ) * linearityRejects f < (Fintype.card G : ℝ) * Fintype.card G := by
    nlinarith
  exact_mod_cast hh

theorem corrective_query_error (f : G → H) (x : G) :
    testRate (fun y => derivative f x y ≠ corrected f x) ≤ 2 * linearityRate f := by
  classical
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [testRate_eq_count, linearityRate_eq]
  change (correctionErrors f x (corrected f x) : ℝ) / Fintype.card G ≤ _
  have hh : (Fintype.card G : ℝ) * correctionErrors f x (corrected f x) ≤
      2 * linearityRejects f := by exact_mod_cast correction_error_bound f x
  calc
    _ = ((Fintype.card G : ℝ) * _) / (Fintype.card G : ℝ)^2 := by
      field_simp
    _ ≤ (2 * linearityRejects f) / (Fintype.card G : ℝ)^2 :=
      div_le_div_of_nonneg_right hh (sq_nonneg _)
    _ = _ := by ring

theorem corrected_distance (f : G → H) (h : linearityRate f < 1/6) :
    testRate (fun x => f x ≠ corrected f x) ≤ 2 * linearityRate f := by
  classical
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [testRate_eq_count, linearityRate_eq]
  change (tableErrors f (corrected f) : ℝ) / Fintype.card G ≤ _
  have hh : (Fintype.card G : ℝ) * tableErrors f (corrected f) ≤
      2 * linearityRejects f := by exact_mod_cast corrected_close f (linearityRate_small f h)
  calc
    _ = ((Fintype.card G : ℝ) * _) / (Fintype.card G : ℝ)^2 := by
      field_simp
    _ ≤ (2 * linearityRejects f) / (Fintype.card G : ℝ)^2 :=
      div_le_div_of_nonneg_right hh (sq_nonneg _)
    _ = _ := by ring

end LinearityRates
end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
