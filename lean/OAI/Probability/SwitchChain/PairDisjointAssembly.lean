import OAI.Probability.SwitchChain.PairDisjointBudget
import OAI.Probability.SwitchChain.CrossToggleGain
import OAI.Probability.SwitchChain.PairEqualityUnordered

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem interaction_on_pairs_of_named {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (hlocal : ∀ (i j k l : Fin n) (h : FourDistinct i j k l),
      2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖PairEquality.projection i j k l f‖ ^ 2 -
        ‖PairEquality.projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫)
    (a : Finset (Fin n)) (ha : a ∈ pairs n)
    (b : Finset (Fin n)) (hb : b ∈ pairs n) (hab : Disjoint a b) :
    2 * ‖CrossToggle.gain a b f‖ ^ 2 - ‖PairEquality.pairProjection a b f‖ ^ 2 -
      ‖PairEquality.pairProjection b a f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  have hca : a.card = 2 := (Finset.mem_powersetCard.mp ha).2
  have hcb : b.card = 2 := (Finset.mem_powersetCard.mp hb).2
  let A : CrossToggle.VertexPair n := ⟨a, hca⟩
  let B : CrossToggle.VertexPair n := ⟨b, hcb⟩
  have hA : a = {CrossToggle.first A, CrossToggle.second A} := CrossToggle.pair_eq A
  have hB : b = {CrossToggle.first B, CrossToggle.second B} := CrossToggle.pair_eq B
  have hfour := CrossToggle.endpoints_distinct A B hab
  have hg : CrossToggle.gain (d := d) a b =
      SwitchFlip.projection (CrossToggle.crossProposal
        (CrossToggle.first A) (CrossToggle.second A)
        (CrossToggle.first B) (CrossToggle.second B) hfour) := by
    rw [CrossToggle.gain_of_pairs a b hca hcb]
    exact CrossToggle.pairProjection_of_disjoint A B hab
  rw [hg,
    PairEquality.pairProjection_eq a b _ _ _ _
      (CrossToggle.first_ne_second A) (CrossToggle.first_ne_second B) hA hB,
    PairEquality.pairProjection_eq b a _ _ _ _
      (CrossToggle.first_ne_second B) (CrossToggle.first_ne_second A) hB hA]
  simpa only [← hA, ← hB] using hlocal _ _ _ _ hfour

theorem disjoint_sum_nonneg_of_named_interaction_budget {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (hlocal : ∀ (i j k l : Fin n) (h : FourDistinct i j k l),
      2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖PairEquality.projection i j k l f‖ ^ 2 -
        ‖PairEquality.projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫)
    (hbudget : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, ‖PairEquality.pairProjection a b f‖ ^ 2) ≤
        ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2) :
    0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0 := by
  apply disjoint_sum_nonneg_of_interaction_budget f
    (fun a b => CrossToggle.gain a b) (fun a b => PairEquality.pairProjection a b)
    (interaction_on_pairs_of_named f hlocal)
  intro a ha
  rw [PairEquality.sum_pairProjection_norm_sq]
  have hg : (∑ b ∈ pairs n, if Disjoint a b then ‖CrossToggle.gain a b f‖ ^ 2 else 0) =
      ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : Disjoint a b
    · rw [ite_eq_left hab]
    · rw [ite_eq_right hab, CrossToggle.gain_eq_zero_of_not_disjoint a b hab]
      simp
  rw [hg]
  exact hbudget a ha

end Problem315.PairResampling

end

end OAI
