import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Literal `eq:raw-pattern-count` (transfer.tex:282--285), before the
exponential relaxation. The family is the actual fixed labeled residual family,
not a replacement cardinality expression. The empty-group case is included. -/

namespace MatroidProphet

open Set Finset Pivots

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

theorem integerResidualFamily_card_raw (M : Matroid α) (hE : M.E = Set.univ)
    (d : α) (U : Finset α) (q : ℕ) (F : ℤ → Set α) (a : ℤ) (ε : Fin 2)
    (K : ParityWindow a ε → Set α) (test : Fin n → α) :
    (integerResidualFamily M U q F a ε K test).card ≤
      (binomialSum U.card q)^2 * (4^(2*q) * binomialSum n (2*q))^2 := by
  exact card_residualFamily_le M d U q _ _ _ _ test
    (by simp [hE]) (by simp [hE]) (by simp [hE])

/-- Both subset choices and both marked-sequence counts are retained exactly.
No lower bound on the group size or density threshold is needed. -/
theorem labeledResidualFamily_card_raw (M : Matroid α) (hE : M.E = Set.univ)
    (U : Finset α) (κ : ℕ) (F : ℤ → Set α) (a : ℤ) (ε : Fin 2)
    (K : ParityWindow a ε → Set α) :
    (labeledResidualFamily M U κ F a ε K).card ≤
      (binomialSum U.card (U.card / κ))^2 *
        (4^(2*(U.card / κ)) * binomialSum U.card (2*(U.card / κ)))^2 := by
  classical
  by_cases hU : U.Nonempty
  · obtain ⟨d, _⟩ := hU
    exact Finset.card_image_le.trans
      (integerResidualFamily_card_raw M hE d U (U.card / κ) F a ε K (groupLabel U))
  · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    have hsub : labeledResidualFamily M ∅ κ F a ε K ⊆ ({∅} : Finset (Finset α)) := by
      intro R hR
      have hR0 := labeledResidualFamily_subsets M ∅ κ F a ε K R hR
      simpa only [Finset.mem_singleton] using Finset.subset_empty.mp hR0
    have hc := Finset.card_le_card hsub
    have hzero : Finset.Iic (0 : ℕ) = {0} := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_singleton, Nat.le_zero]
    simpa [binomialSum, hzero] using hc

end MatroidProphet

end OAI
