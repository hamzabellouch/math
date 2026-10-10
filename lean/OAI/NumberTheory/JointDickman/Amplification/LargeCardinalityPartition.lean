import OAI.NumberTheory.JointDickman.Amplification.LargeAlternativeCount

namespace OAI

/-! # Partitioning all large high-endpoint alternatives by cardinality -/

namespace JointDickman
open Finset Classical

noncomputable def allLargeHighAlternativePairs (B L k j : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((regularSmallAlternatives B L k τ C A U).product
    (regularSmallAlternatives B L k τ C D V)).filter (fun XY =>
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (∏ p ∈ XY.1 \ A, p : ℕ) ∧
      (∏ p ∈ XY.1, p : ℕ) ≤ 2*(∏ p ∈ XY.2, p : ℕ) ∧
      ((∏ p ∈ XY.1, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ((∏ p ∈ XY.2, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ∃ c : ℕ, 0 < c ∧ (∏ p ∈ XY.1, p) = (∏ p ∈ XY.2, p)+j*c ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c))

theorem allLargeHighAlternativePairs_fiber (B L k j d f : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) :
    (allLargeHighAlternativePairs B L k j τ C Δ A U D V).filter
      (fun XY => ((XY.1 \ A).card,(XY.2 \ D).card) = (d,f)) =
        largeHighAlternativePairs B L k j d f τ C Δ A U D V := by
  ext XY
  simp only [allLargeHighAlternativePairs,largeHighAlternativePairs,mem_filter,Prod.mk.injEq]
  tauto

theorem regular_addition_card_le_logLength {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hk : k ∈ Icc 1 L) (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hU : RegularPrimeSet B L τ C U) (hX : X ∈ regularSmallAlternatives B L k τ C A U) :
    ((X \ A).card : ℝ) ≤ auxiliaryLogLength B := by
  have hkL := (mem_Icc.mp hk).2
  have hL : (0 : ℝ) < L := by exact_mod_cast (by have := (mem_Icc.mp hk).1; omega : 0 < L)
  have hg : (k : ℝ)/L ≤ 1 := (div_le_one hL).mpr (by exact_mod_cast hkL)
  have hsub := (mem_filter.mp hX).2.2.trans
    (primePrefix_mono B _ (alternative_additions_subset_remainder hX))
  have hc : ((X \ A).card : ℝ) ≤ (primePrefix B ((k : ℝ)/L) U).card := by
    exact_mod_cast card_le_card hsub
  have hbound := (hU.1 k hk).2
  have hh := mul_le_mul_of_nonneg_right (show ((k : ℝ)/L)/2+τ ≤ 1 by linarith) hℓ
  linarith

theorem allLargeHighAlternativePairs_card {B L k j : ℕ} {τ C Δ : ℝ}
    (A U D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hU : RegularPrimeSet B L τ C U) (hV : RegularPrimeSet B L τ C V) :
    (allLargeHighAlternativePairs B L k j τ C Δ A U D V).card =
      ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
        (largeHighAlternativePairs B L k j d f τ C Δ A U D V).card := by
  let N := ⌊auxiliaryLogLength B⌋₊+1
  have hmap (XY : Finset ℕ × Finset ℕ)
      (hXY : XY ∈ allLargeHighAlternativePairs B L k j τ C Δ A U D V) :
      ((XY.1 \ A).card,(XY.2 \ D).card) ∈ (range N).product (range N) := by
    obtain ⟨hX,hY⟩ := mem_product.mp (mem_filter.mp hXY).1
    apply mem_product.mpr
    constructor
    · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor
        (regular_addition_card_le_logLength hk hτ hℓ hU hX)))
    · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor
        (regular_addition_card_le_logLength hk hτ hℓ hV hY)))
  have hh := card_eq_sum_card_fiberwise hmap
  rw [Finset.product_eq_sprod,sum_product] at hh
  simpa only [allLargeHighAlternativePairs_fiber] using hh

end JointDickman

end OAI
