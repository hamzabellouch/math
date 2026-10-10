import OAI.NumberTheory.Ostmann.ZeroDensity.InfiniteHighZeroBound

namespace OAI

/-! # Separating bounded-height and high-ordinate terms of the explicit formula -/

namespace Ostmann
open scoped Classical BigOperators

theorem nonnegative_tsum_finite_tail_bound {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hs : Summable f) (S : Finset ι) (P : ι → Prop)
    [DecidablePred P] (hcover : ∀ i ∉ S, P i) :
    (∑' i, f i) ≤ (∑ i ∈ S, f i) + ∑' i, if P i then f i else 0 := by
  let g := fun i => if i ∈ S then f i else 0
  let h := fun i => if P i then f i else 0
  have hg0 (i) : 0 ≤ g i := by dsimp [g]; split_ifs <;> simp_all
  have hh0 (i) : 0 ≤ h i := by dsimp [h]; split_ifs <;> simp_all
  have hg : Summable g := Summable.of_nonneg_of_le hg0
    (fun i => by dsimp [g]; split_ifs <;> simp_all) hs
  have hh : Summable h := Summable.of_nonneg_of_le hh0
    (fun i => by dsimp [h]; split_ifs <;> simp_all) hs
  have hpoint (i) : f i ≤ g i + h i := by
    by_cases hi : i ∈ S
    · simp only [g, hi, ite_true]
      exact le_add_of_nonneg_right (hh0 i)
    · simp only [g, hi, ite_false, zero_add, h, hcover i hi, ite_true, le_refl]
  have hsumg : (∑' i, g i) = ∑ i ∈ S, f i := by
    rw [tsum_eq_sum (s := S) (fun i hi => by simp [g, hi])]
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, hi]
  have hbound := hs.tsum_le_tsum hpoint (hg.add hh)
  rw [hg.tsum_add hh, hsumg] at hbound
  exact hbound

theorem smoothZeroTerm_norm_coarse {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter) (X : ℝ) (i : ℕ) :
    ‖smoothZeroTerm Z χ X i‖ ≤
      Real.exp (((Z χ).zeros i).re * Real.log X) * P.mellinConstant := by
  have hlog : 0 ≤ Real.log (1 + |((Z χ).zeros i).im|) :=
    Real.log_nonneg (by linarith [abs_nonneg ((Z χ).zeros i).im])
  have he : Real.exp (-8 * Real.log (1 + |((Z χ).zeros i).im|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  exact (smoothZeroTerm_norm_bound P χ X i).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (mul_nonneg (Real.exp_nonneg _) P.mellinConstant_pos.le))

theorem bounded_height_zero_norm_sum {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (χ : PrimitiveComplexCharacter)
    (T X : ℝ) (hX : 1 ≤ X) :
    (∑ i ∈ (Z χ).heightIndices T, ‖smoothZeroTerm Z χ X i‖) ≤
      (X * P.mellinConstant) *
        (∑ i ∈ ((Z χ).heightIndices T).filter (fun i => 1 / 2 ≤ ((Z χ).zeros i).re),
          Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re))) +
      (Real.exp ((1 / 2 : ℝ) * Real.log X) * P.mellinConstant) *
        ((Z χ).heightIndices T).card := by
  have hXp : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hpoint (i : ℕ) : ‖smoothZeroTerm Z χ X i‖ ≤
      (if 1 / 2 ≤ ((Z χ).zeros i).re then
        X * P.mellinConstant * Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re)) else 0) +
      Real.exp ((1 / 2 : ℝ) * Real.log X) * P.mellinConstant := by
    by_cases hi : 1 / 2 ≤ ((Z χ).zeros i).re
    · simp only [hi, ite_true]
      have he : Real.exp (((Z χ).zeros i).re * Real.log X) =
          X * Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re)) := by
        calc
          _ = Real.exp (Real.log X + (-Real.log X * (1 - ((Z χ).zeros i).re))) := by
            congr 1
            ring
          _ = Real.exp (Real.log X) * Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re)) :=
            Real.exp_add _ _
          _ = _ := by rw [Real.exp_log hXp]
      have hh := smoothZeroTerm_norm_coarse P χ X i
      rw [he] at hh
      have hh' : ‖smoothZeroTerm Z χ X i‖ ≤
          X * P.mellinConstant * Real.exp (-Real.log X * (1 - ((Z χ).zeros i).re)) := by
        convert hh using 1
        ring
      exact hh'.trans (le_add_of_nonneg_right (mul_nonneg (Real.exp_nonneg _) P.mellinConstant_pos.le))
    · simp only [hi, ite_false, zero_add]
      apply (smoothZeroTerm_norm_coarse P χ X i).trans
      apply mul_le_mul_of_nonneg_right _ P.mellinConstant_pos.le
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_of_not_ge hi) hlogX)
  have hh := Finset.sum_le_sum (s := (Z χ).heightIndices T) (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib] at hh
  simpa only [← Finset.sum_filter, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    mul_comm (((Z χ).heightIndices T).card : ℝ), mul_assoc] using hh

end Ostmann

end OAI
