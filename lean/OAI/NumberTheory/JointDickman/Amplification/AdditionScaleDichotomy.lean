import OAI.NumberTheory.JointDickman.Amplification.LargeCardinalityPartition
import OAI.NumberTheory.JointDickman.Amplification.NumericAdditionClass

namespace OAI

/-! # The finite grid dichotomy for the two addition products -/

namespace JointDickman
open Finset Classical

theorem addition_product_large_of_not_prefix {B : ℕ} {g : ℝ} {Z : Finset ℕ}
    (hg : g < 1) (hZ : Z ⊆ auxiliaryPrimes B) (hnot : ¬ Z ⊆ primePrefix B g Z) :
    Real.exp ((B : ℝ)^g) ≤ (∏ p ∈ Z, p : ℕ) := by
  obtain ⟨p,hp,hout⟩ := Finset.not_subset.mp hnot
  have hprime := auxiliaryPrimes_prime B p (hZ hp)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlog : (B : ℝ)^g < Real.log p := by
    apply lt_of_not_ge
    intro hh
    exact hout (by simpa only [primePrefix,ite_eq_left hg] using mem_filter.mpr ⟨hp,hh⟩)
  have hprodpos : 0 < (∏ q ∈ Z, q : ℕ) :=
    prod_pos (fun q hq => (auxiliaryPrimes_prime B q (hZ hq)).pos)
  have hpProd : p ≤ ∏ q ∈ Z, q := Nat.le_of_dvd hprodpos (dvd_prod_of_mem id hp)
  calc
    _ ≤ Real.exp (Real.log p) := (Real.exp_le_exp.mpr hlog.le)
    _ = (p : ℝ) := Real.exp_log hp0
    _ ≤ _ := by exact_mod_cast hpProd

/-- Either both additions stay in the first three grid cells, or at their
first common grid cell one of the products is at least exp(B^(g-1/L)). -/
theorem addition_scale_dichotomy {B L : ℕ} (hL : 3 ≤ L) {Z Y : Finset ℕ}
    (hZ : Z ⊆ auxiliaryPrimes B) (hY : Y ⊆ auxiliaryPrimes B) :
    (Z ⊆ primePrefix B ((3 : ℝ)/L) Z ∧ Y ⊆ primePrefix B ((3 : ℝ)/L) Y) ∨
      ∃ k ∈ Icc 4 L,
        Z ⊆ primePrefix B ((k : ℝ)/L) Z ∧ Y ⊆ primePrefix B ((k : ℝ)/L) Y ∧
          (Real.exp ((B : ℝ)^(((k : ℝ)-1)/L)) ≤ (∏ p ∈ Z, p : ℕ) ∨
            Real.exp ((B : ℝ)^(((k : ℝ)-1)/L)) ≤ (∏ p ∈ Y, p : ℕ)) := by
  by_cases hsmall : Z ⊆ primePrefix B ((3 : ℝ)/L) Z ∧ Y ⊆ primePrefix B ((3 : ℝ)/L) Y
  · exact Or.inl hsmall
  · right
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    let P := fun k : ℕ => 3 ≤ k ∧ k ≤ L ∧
      Z ⊆ primePrefix B ((k : ℝ)/L) Z ∧ Y ⊆ primePrefix B ((k : ℝ)/L) Y
    have hex : ∃ k, P k := by
      refine ⟨L,hL,le_rfl,?_,?_⟩ <;> simp [primePrefix,div_self hL0]
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    change 3 ≤ k ∧ k ≤ L ∧ Z ⊆ primePrefix B ((k : ℝ)/L) Z ∧
      Y ⊆ primePrefix B ((k : ℝ)/L) Y at hk
    have hk4 : 4 ≤ k := by
      by_contra hn
      have hkeq : k = 3 := by omega
      rw [hkeq] at hk
      exact hsmall ⟨hk.2.2.1,hk.2.2.2⟩
    have hprev : ¬ (Z ⊆ primePrefix B (((k-1 : ℕ) : ℝ)/L) Z ∧
        Y ⊆ primePrefix B (((k-1 : ℕ) : ℝ)/L) Y) := by
      intro hh
      have hn := Nat.find_min hex (show k-1 < k by omega)
      apply hn
      exact ⟨by omega,by omega,hh⟩
    have hprevlt : (((k-1 : ℕ) : ℝ)/L) < 1 := by
      have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      apply (div_lt_one hLpos).mpr
      exact_mod_cast (by omega : k-1 < L)
    refine ⟨k,mem_Icc.mpr ⟨hk4,hk.2.1⟩,hk.2.2.1,hk.2.2.2,?_⟩
    have heq : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    by_cases hz : Z ⊆ primePrefix B (((k-1 : ℕ) : ℝ)/L) Z
    · right
      have hy : ¬ Y ⊆ primePrefix B (((k-1 : ℕ) : ℝ)/L) Y := fun hh => hprev ⟨hz,hh⟩
      simpa only [heq] using addition_product_large_of_not_prefix hprevlt hY hy
    · left
      simpa only [heq] using addition_product_large_of_not_prefix hprevlt hZ hz

end JointDickman

end OAI
