import OAI.NumberTheory.JointDickman.Amplification.LowAlternativeCount
import OAI.NumberTheory.JointDickman.Amplification.LargeCardinalityPartition

namespace OAI

/-! # Partitioning all large low-endpoint alternatives by cardinality -/

namespace JointDickman
open Finset Classical

noncomputable def allLargeLowAlternativePairs (B L k j : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((regularSmallAlternatives B L k τ C A U).product
    (regularSmallAlternatives B L k τ C D V)).filter (fun XY =>
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (∏ p ∈ XY.1 \ A, p : ℕ) ∧
      (∏ p ∈ XY.2, p : ℕ) ≤ 2*(∏ p ∈ XY.1, p : ℕ) ∧
      ((∏ p ∈ XY.1, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ((∏ p ∈ XY.2, p : ℕ) : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      ∃ c : ℕ, 0 < c ∧ (∏ p ∈ XY.1, p)+j*c = (∏ p ∈ XY.2, p) ∧
        RegularPrimeSet B L τ C (coefficientPrimeSet B c))

theorem allLargeLowAlternativePairs_fiber (B L k j d f : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) :
    (allLargeLowAlternativePairs B L k j τ C Δ A U D V).filter
      (fun XY => ((XY.1 \ A).card,(XY.2 \ D).card) = (d,f)) =
        largeLowAlternativePairs B L k j d f τ C Δ A U D V := by
  ext XY
  simp only [allLargeLowAlternativePairs,largeLowAlternativePairs,mem_filter,Prod.mk.injEq]
  tauto

theorem allLargeLowAlternativePairs_card {B L k j : ℕ} {τ C Δ : ℝ}
    (A U D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hU : RegularPrimeSet B L τ C U) (hV : RegularPrimeSet B L τ C V) :
    (allLargeLowAlternativePairs B L k j τ C Δ A U D V).card =
      ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
        (largeLowAlternativePairs B L k j d f τ C Δ A U D V).card := by
  let N := ⌊auxiliaryLogLength B⌋₊+1
  have hmap (XY : Finset ℕ × Finset ℕ)
      (hXY : XY ∈ allLargeLowAlternativePairs B L k j τ C Δ A U D V) :
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
  simpa only [allLargeLowAlternativePairs_fiber] using hh

end JointDickman

end OAI
