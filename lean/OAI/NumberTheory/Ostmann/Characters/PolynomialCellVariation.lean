import OAI.NumberTheory.Ostmann.Characters.PolynomialRootCells
import OAI.NumberTheory.Ostmann.Construction.FiniteIntervalPartition
import OAI.NumberTheory.Ostmann.Characters.ProductWeightVariation

namespace OAI

/-! # Actual interval pieces and smooth polynomial weights -/

namespace Ostmann

open scoped BigOperators Classical

/-- Root comparisons give an exact interval decomposition of any increasing
integer sampling grid. Equality endpoints retain their own code. -/
theorem exists_rootCell_partition (S : Finset ℝ) (N : ℕ) (u : ℕ → ℝ)
    (hu : Monotone u) :
    ∃ (a K : (S → Ordering) → ℕ) (e : Fin N ≃ Σ i, Fin (K i)),
      (∀ i (j : Fin (K i)), (e.symm ⟨i, j⟩).val = a i + j.val) ∧
      (∀ i (j : Fin (K i)), rootCellCode S (u (a i + j.val)) = i) := by
  apply exists_finite_interval_partition N (fun j => rootCellCode S (u j))
  intro x y z _ _ hxz hzy he
  exact rootCellCode_convex S (hu hxz) (hu hzy) he

/-- Including derivative roots among the cuts proves the required variation
bound for a compactly supported smooth factor evaluated on the polynomial. -/
theorem discreteVariation_polynomial_cell (P : Polynomial ℝ) (S : Finset ℝ)
    (hroots : ∀ r ∈ P.derivative.roots, r ∈ S)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hcode : rootCellCode S (u 0) = rootCellCode S (u (N - 1)))
    (Φ : ℝ → ℂ) (lo hi B D : ℝ) (hlohi : lo ≤ hi) (hD : 0 ≤ D)
    (hbound : ∀ x, ‖Φ x‖ ≤ B)
    (hlip : ∀ x y, ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hlo : Φ lo = 0) (hhi : Φ hi = 0)
    (hout : ∀ x, x < lo ∨ hi < x → Φ x = 0) :
    discreteVariation (fun j => Φ (P.eval (u j))) N ≤ B + D * (hi - lo) := by
  have hrange (j : ℕ) (hj : j ≤ N - 1) : u j ∈ Set.Icc (u 0) (u (N - 1)) :=
    ⟨hu (Nat.zero_le _), hu hj⟩
  rcases polynomial_monotoneOn_of_root_cell P S hroots hcode with hmono | hanti
  · apply discreteVariation_comp_compact_monotone Φ _ lo hi B D N hlohi hD
      hbound hlip hlo hhi hout
    intro j hj
    exact hmono (hrange j hj.le) (hrange (j + 1) (by omega)) (hu (by omega))
  · apply discreteVariation_comp_compact_antitone Φ _ lo hi B D N hlohi hD
      hbound hlip hlo hhi hout
    intro j hj
    exact hanti (hrange j hj.le) (hrange (j + 1) (by omega)) (hu (by omega))

/-- The same explicit root set works simultaneously for all smooth factors. -/
theorem discreteVariation_polynomial_product_cell (n : ℕ) (P : Fin n → Polynomial ℝ)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (P i).derivative.roots → r ∈ S)
    (u : ℕ → ℝ) (hu : Monotone u) (N : ℕ)
    (hcode : rootCellCode S (u 0) = rootCellCode S (u (N - 1)))
    (Φ : Fin n → ℝ → ℂ) (lo hi B D : Fin n → ℝ)
    (hlohi : ∀ i, lo i ≤ hi i) (hB : ∀ i, 0 ≤ B i) (hD : ∀ i, 0 ≤ D i)
    (hbound : ∀ i x, ‖Φ i x‖ ≤ B i)
    (hlip : ∀ i x y, ‖Φ i x - Φ i y‖ ≤ D i * |x - y|)
    (hlo : ∀ i, Φ i (lo i) = 0) (hhi : ∀ i, Φ i (hi i) = 0)
    (hout : ∀ i x, x < lo i ∨ hi i < x → Φ i x = 0) :
    discreteVariation (fun j => ∏ i, Φ i ((P i).eval (u j))) N ≤
      ∏ i, (2 * B i + D i * (hi i - lo i)) := by
  have hb (i : Fin n) : 0 ≤ B i + D i * (hi i - lo i) :=
    add_nonneg (hB i) (mul_nonneg (hD i) (sub_nonneg.mpr (hlohi i)))
  have hv (i : Fin n) := discreteVariation_polynomial_cell (P i) S (hroots i) u hu N
    hcode (Φ i) (lo i) (hi i) (B i) (D i) (hlohi i) (hD i) (hbound i) (hlip i)
    (hlo i) (hhi i) (hout i)
  have ht := discreteVariation_prod n (fun i j => Φ i ((P i).eval (u j))) B
    (fun i => B i + D i * (hi i - lo i)) N hB hb (fun i j => hbound i _) hv
  convert ht using 1
  congr 1
  funext i
  ring

/-- On a root cell, polynomial inequality supports really are constant. -/
theorem polynomial_nonneg_iff_of_root_cell (P : Polynomial ℝ) (S : Finset ℝ)
    (hroots : ∀ r ∈ P.roots, r ∈ S) {x y : ℝ}
    (hcode : rootCellCode S x = rootCellCode S y) :
    0 ≤ P.eval x ↔ 0 ≤ P.eval y := by
  by_cases hp : P = 0
  · simp [hp]
  have hordered (a b : ℝ) (hab : a < b)
      (hc : rootCellCode S a = rootCellCode S b) : 0 ≤ P.eval a ↔ 0 ≤ P.eval b := by
    have hn (z : ℝ) (hz : z ∈ Set.Icc a b) : P.eval z ≠ 0 := by
      intro he
      have hm : z ∈ P.roots := (Polynomial.mem_roots hp).mpr he
      exact rootCellCode_no_root_between S hab hc z (hroots z hm) hz
    constructor
    · intro ha
      by_contra hb
      have hb' : P.eval b < 0 := lt_of_not_ge hb
      obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hab.le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (P.eval b) (P.eval a) from ⟨hb'.le, ha⟩)
      exact hn z hz he
    · intro hb
      by_contra ha
      have ha' : P.eval a < 0 := lt_of_not_ge ha
      obtain ⟨z, hz, he⟩ := intermediate_value_Icc hab.le P.continuous.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (P.eval a) (P.eval b) from ⟨ha'.le, hb⟩)
      exact hn z hz he
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact hordered x y hxy hcode
  · rfl
  · exact (hordered y x hyx hcode.symm).symm

end Ostmann

end OAI
