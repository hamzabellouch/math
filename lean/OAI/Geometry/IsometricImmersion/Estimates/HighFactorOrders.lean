import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

noncomputable section
open scoped BigOperators

namespace SmoothLocal.HighEquation

theorem ordered_partSize_sum {ell : ℕ} (c : OrderedFinpartition ell) :
    ∑ j, c.partSize j = ell := by
  have hh := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hh

theorem ordered_two_partSizes_le {ell : ℕ} (c : OrderedFinpartition ell)
    {i j : Fin c.length} (hij : i ≠ j) :
    c.partSize i + c.partSize j ≤ ell := by
  have hh : ∑ k ∈ ({i, j} : Finset (Fin c.length)), c.partSize k ≤
      ∑ k, c.partSize k :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simpa only [Finset.sum_pair hij, ordered_partSize_sum] using hh

theorem high_factor_spends {ell block base : ℕ}
    (hbase : base ≤ 2) (hhigh : ell - 1 ≤ block + base) :
    ell - 3 ≤ block := by omega

theorem ordered_high_factor_unique {ell : ℕ} (hell : 8 ≤ ell)
    (c : OrderedFinpartition ell) (base : Fin c.length → ℕ)
    (hbase : ∀ j, base j ≤ 2)
    {i j : Fin c.length}
    (hi : ell - 1 ≤ c.partSize i + base i)
    (hj : ell - 1 ≤ c.partSize j + base j) : i = j := by
  by_contra hij
  have hsum := ordered_two_partSizes_le c hij
  have hispend := high_factor_spends (hbase i) hi
  have hjspend := high_factor_spends (hbase j) hj
  omega

theorem ordered_high_factor_card_le_one {ell : ℕ} (hell : 8 ≤ ell)
    (c : OrderedFinpartition ell) (base : Fin c.length → ℕ)
    (hbase : ∀ j, base j ≤ 2) :
    (Finset.univ.filter (fun j => ell - 1 ≤ c.partSize j + base j)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact ordered_high_factor_unique hell c base hbase
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem ordered_other_factor_order_le {ell : ℕ} (hell : 8 ≤ ell)
    (c : OrderedFinpartition ell) (base : Fin c.length → ℕ)
    (hbase : ∀ j, base j ≤ 2) {i : Fin c.length}
    (hi : ell - 1 ≤ c.partSize i + base i)
    {j : Fin c.length} (hji : j ≠ i) : c.partSize j + base j ≤ ell - 2 := by
  by_contra hlarge
  have hj : ell - 1 ≤ c.partSize j + base j := by omega
  exact hji (ordered_high_factor_unique hell c base hbase hj hi)

theorem remaining_factor_order_le {ell block base : ℕ}
    (hell : 2 ≤ ell) (hblock : block ≤ ell - 2) (hbase : base ≤ 2) :
    block + base ≤ ell := by omega

theorem ordered_top_factor_classes {ell : ℕ} (c : OrderedFinpartition ell)
    (base : Fin c.length → ℕ) (hbase : ∀ j, base j ≤ 2)
    {i : Fin c.length} (hhigh : ell < c.partSize i + base i) :
    c.partSize i = ell ∨ (c.partSize i = ell - 1 ∧ base i = 2) := by
  have hsize := c.partSize_le i
  have hb := hbase i
  omega

theorem ordered_penultimate_other_singleton {ell : ℕ}
    (c : OrderedFinpartition ell) {i j : Fin c.length}
    (hi : c.partSize i = ell - 1) (hij : i ≠ j) : c.partSize j = 1 := by
  have hi0 := c.partSize_pos i
  have hj0 := c.partSize_pos j
  have hsum := ordered_two_partSizes_le c hij
  omega

theorem ordered_remainder_factor_orders {ell : ℕ} (hell : 8 ≤ ell)
    (c : OrderedFinpartition ell) (base : Fin c.length → ℕ)
    (hbase : ∀ j, base j ≤ 2) (hblocks : ∀ j, c.partSize j ≤ ell - 2) :
    (∀ j, c.partSize j + base j ≤ ell) ∧
      (Finset.univ.filter (fun j => ell - 1 ≤ c.partSize j + base j)).card ≤ 1 := by
  exact ⟨fun j => remaining_factor_order_le (by omega) (hblocks j) (hbase j),
    ordered_high_factor_card_le_one hell c base hbase⟩

theorem ordered_extracted_factor_orders {ell : ℕ} (hell : 8 ≤ ell)
    (c : OrderedFinpartition ell) (base : Fin c.length → ℕ)
    (hbase : ∀ j, base j ≤ 2)
    (hremaining : ∀ j, c.partSize j ≤ ell - 2 ∨
      (c.partSize j = ell - 1 ∧ base j ≤ 1)) :
    (∀ j, c.partSize j + base j ≤ ell) ∧
      (Finset.univ.filter (fun j => ell - 1 ≤ c.partSize j + base j)).card ≤ 1 := by
  constructor
  · intro j
    rcases hremaining j with hj | ⟨hj, hb⟩
    · exact remaining_factor_order_le (by omega) hj (hbase j)
    · omega
  · exact ordered_high_factor_card_le_one hell c base hbase

end SmoothLocal.HighEquation

end

end OAI
