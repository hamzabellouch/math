import OAI.MeasureTheory.Falconer.Geometry.ScalarGridGrouping

namespace OAI

/-! Simultaneous grouping for two separated child sets. Separation of
 their union is not required; the dense group may come from either side. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem scalar_pair_grid_grouping {h μ z : ℝ} (hh : 0 < h) (hhμ : h ≤ μ)
    (X Y : Finset ℝ)
    (hXbound : ∀ x ∈ X, 0 ≤ x-z ∧ x-z ≤ 2)
    (hYbound : ∀ y ∈ Y, 0 ≤ y-z ∧ y-z ≤ 2)
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → μ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → μ ≤ |x-y|)
    (M : ℕ) (hM : 2 ≤ M) (hcard : 2*M ≤ X.card) :
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℤ,
      (M ≤ (scalarGridFiber ((2:ℝ)^n*h) z X k).card ∨
       M ≤ (scalarGridFiber ((2:ℝ)^n*h) z Y k).card) ∧
      ∀ j : ℤ, (scalarGridFiber ((2:ℝ)^n*h) z X j).card ≤ 4*M ∧
        (scalarGridFiber ((2:ℝ)^n*h) z Y j).card ≤ 4*M := by
  have hEbound : ∀ x ∈ X ∪ Y, 0 ≤ x-z ∧ x-z ≤ 2 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hXbound x hx
    · exact hYbound x hx
  have hEcard : 2*M ≤ (X ∪ Y).card := hcard.trans (Finset.card_le_card (Finset.subset_union_left))
  have hunion (η : ℝ) (k : ℤ) : scalarGridFiber η z (X ∪ Y) k =
      scalarGridFiber η z X k ∪ scalarGridFiber η z Y k := by
    exact Finset.filter_union _ _ _
  have hsmall (k : ℤ) : (scalarGridFiber h z (X ∪ Y) k).card < 2*M := by
    rw [hunion]
    have hu := Finset.card_union_le (scalarGridFiber h z X k) (scalarGridFiber h z Y k)
    have hx := scalarGridFiber_small (z := z) hh hhμ X hXsep k
    have hy := scalarGridFiber_small (z := z) hh hhμ Y hYsep k
    omega
  obtain ⟨n,hn,k,hk,hall⟩ := scalar_grid_grouping_of_small_cells hh (X ∪ Y) hEbound M hEcard hsmall
  refine ⟨n,hn,k,?_,?_⟩
  · rw [hunion] at hk
    have hu := Finset.card_union_le (scalarGridFiber ((2:ℝ)^n*h) z X k)
      (scalarGridFiber ((2:ℝ)^n*h) z Y k)
    omega
  · intro j
    constructor
    · exact (Finset.card_le_card (scalarGridFiber_mono _ _ Finset.subset_union_left _)).trans (hall j)
    · exact (Finset.card_le_card (scalarGridFiber_mono _ _ Finset.subset_union_right _)).trans (hall j)

end Falconer

end OAI
