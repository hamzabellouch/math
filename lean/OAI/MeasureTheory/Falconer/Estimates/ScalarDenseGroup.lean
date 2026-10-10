import OAI.MeasureTheory.Falconer.Estimates.ScalarPairGrouping

namespace OAI

/-! Selecting an exact-size dense group at a scale large enough to
 control projected overlap. The dense group can lie in either child set. -/
namespace Falconer

 theorem scalar_pair_dense_group {μ r z : ℝ} (hμ : 0 < μ) (hr : 10*r ≤ μ)
    (X Y : Finset ℝ)
    (hXbound : ∀ x ∈ X, 0 ≤ x-z ∧ x-z ≤ 2)
    (hYbound : ∀ y ∈ Y, 0 ≤ y-z ∧ y-z ≤ 2)
    (hXsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → μ ≤ |x-y|)
    (hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → μ ≤ |x-y|)
    (M : ℕ) (hM : 2 ≤ M) (hcard : 2*M ≤ X.card) :
    ∃ η : ℝ, 0 < η ∧ 10*r ≤ η ∧ ∃ k : ℤ,
      (∀ j : ℤ, (scalarGridFiber η z X j).card ≤ 4*M ∧
        (scalarGridFiber η z Y j).card ≤ 4*M) ∧
      ((∃ F ⊆ scalarGridFiber η z X k, F.card = M) ∨
       (∃ F ⊆ scalarGridFiber η z Y k, F.card = M)) := by
  obtain ⟨n,hn,k,hk,hall⟩ := scalar_pair_grid_grouping (half_pos hμ) (by linarith : μ/2 ≤ μ)
    X Y hXbound hYbound hXsep hYsep M hM hcard
  have hp : (2:ℝ) ≤ (2:ℝ)^n := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) (show 1 ≤ n by omega)
    simpa only [pow_one] using h
  have hη : μ ≤ (2:ℝ)^n*(μ/2) := by nlinarith
  refine ⟨(2:ℝ)^n*(μ/2),by positivity,hr.trans hη,k,hall,?_⟩
  rcases hk with hk | hk
  · exact Or.inl (Finset.exists_subset_card_eq hk)
  · exact Or.inr (Finset.exists_subset_card_eq hk)

end Falconer

end OAI
