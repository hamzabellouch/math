import OAI.NumberTheory.Ostmann.Characters.QuartetIndexCoordinates
import OAI.NumberTheory.Ostmann.Characters.QuartetSignClassification
import OAI.NumberTheory.Ostmann.Characters.CycleMovingPair

namespace OAI

/-! # The graph cycle supplies genuine quartet coordinate signs -/

namespace Ostmann

open scoped BigOperators

theorem sum_zero_indicator_eq_card {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ℤ) :
    (∑ i ∈ s, if f i = 0 then (0 : ℕ) else 1) = (s.filter fun i => f i ≠ 0).card := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : f i = 0 <;> simp [h]

theorem balanced_quartet_coordinates (n : ℕ) (sign : TreeLeafIndex (n + 2) → ℤ)
    (hvalues : ∀ j, sign j = 0 ∨ sign j = 1 ∨ sign j = -1)
    (hbalance : ∀ q, (∑ j ∈ Finset.univ.filter (fun j => bottomQuartet n j = q), sign j) = 0)
    (hsupport : ∀ q,
      (Finset.univ.filter (fun j => bottomQuartet n j = q ∧ sign j ≠ 0)).card ≤ 2) :
    ∃ choice : TreeLeafIndex n → QuartetMovingCase, ∃ δ : TreeLeafIndex n → ℤ,
      (∀ q, δ q = 0 ∨ δ q = 1 ∨ δ q = -1) ∧
      ∀ q j, sign (quartetLeafIndex n q j) =
        treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j := by
  classical
  have hlocal (q : TreeLeafIndex n) :
      ∃ choice : QuartetMovingCase, ∃ δ : ℤ, (δ = 0 ∨ δ = 1 ∨ δ = -1) ∧
        ∀ j, sign (quartetLeafIndex n q j) =
          treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ * s) 2 (quartetMovingSign choice)) j := by
    let f : TreeLeafIndex 2 → ℤ := fun j => sign (quartetLeafIndex n q j)
    have hsum : (∑ j : TreeLeafIndex 2, f j) = 0 := by
      rw [← sum_bottomQuartet_fiber]
      exact hbalance q
    have hcard : (∑ j : TreeLeafIndex 2, if f j = 0 then (0 : ℕ) else 1) ≤ 2 := by
      rw [← sum_bottomQuartet_fiber n q (fun j => if sign j = 0 then (0 : ℕ) else 1),
        sum_zero_indicator_eq_card, Finset.filter_filter]
      exact hsupport q
    rw [sum_four_treeLeaves] at hsum hcard
    obtain ⟨moving, δ, hδ, heq⟩ := quartetSign_classification
      (f (.inl (.inl ()))) (f (.inl (.inr ())))
      (f (.inr (.inl ()))) (f (.inr (.inr ())))
      (hvalues _) (hvalues _) (hvalues _) (hvalues _) (by omega) (by simpa only [Nat.add_assoc] using hcard)
    refine ⟨moving, δ, hδ, ?_⟩
    intro j
    have h := congrArg (fun m : TreeLeafTuple ℤ 2 => treeLeafTupleEquiv ℤ 2 m j) heq
    rcases j with (⟨⟩ | ⟨⟩) | (⟨⟩ | ⟨⟩) <;> exact h
  choose choice δ hδ hcoord using hlocal
  exact ⟨choice, δ, hδ, hcoord⟩

theorem BalancedIncidenceCycle.quartet_coordinates {C : Type*} [DecidableEq C]
    (n : ℕ) {component : TreeLeafIndex (n + 2) → C}
    (cycle : BalancedIncidenceCycle component (bottomQuartet n)) :
    ∃ choice : TreeLeafIndex n → QuartetMovingCase, ∃ δ : TreeLeafIndex n → ℤ,
      (∀ q, δ q = 0 ∨ δ q = 1 ∨ δ q = -1) ∧
      (∀ q j, cycle.sign (quartetLeafIndex n q j) =
        treeLeafTupleEquiv ℤ 2 (treeLeafMap (fun s : ℤ => δ q * s) 2 (quartetMovingSign (choice q))) j) ∧
      ∃ q, δ q = 1 ∨ δ q = -1 := by
  obtain ⟨choice, δ, hδ, hcoord⟩ := balanced_quartet_coordinates n cycle.sign
    cycle.values cycle.quartet_balanced cycle.quartet_support
  refine ⟨choice, δ, hδ, hcoord, ?_⟩
  obtain ⟨j, hj⟩ := cycle.nonzero
  let q := (quartetLeafCoordinates n j).1
  have hn : δ q ≠ 0 := by
    intro hz
    have h := hcoord q (quartetLeafCoordinates n j).2
    rw [treeLeafTupleEquiv_map, hz, zero_mul] at h
    have hi := quartetLeafIndex_coordinates n j
    change quartetLeafIndex n q (quartetLeafCoordinates n j).2 = j at hi
    rw [hi] at h
    rcases hj with hj | hj <;> omega
  exact ⟨q, (hδ q).resolve_left hn⟩

end Ostmann

end OAI
