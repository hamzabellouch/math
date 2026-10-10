import OAI.Combinatorics.ProgressionColoring.OuterPatternColoring

namespace OAI

/-! Elementary case selection for the geometric dichotomy. Lightness refers
to full-word multiplicities throughout; restriction to a block never changes it. -/

universe uLabel

namespace QuantitativeVanDerWaerden

theorem exists_heavy_label_of_few_light {Label : Type uLabel} [DecidableEq Label]
    {k M : ℕ} (word : Fin k → Label)
    (hfew : ¬ k ≤ 10 * (OuterWordTests.lightPositions M word).card) :
    ∃ i : Fin k, k < M * OuterWordTests.multiplicity word (word i) := by
  classical
  have hc : (OuterWordTests.lightPositions M word).card <
      (Finset.univ : Finset (Fin k)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨i, Nat.lt_of_not_ge ?_⟩
  intro h
  exact hi ((OuterWordTests.mem_lightPositions M word i).mpr h)

theorem heavy_label_has_two_visits {Label : Type uLabel} [DecidableEq Label]
    {k M : ℕ} (word : Fin k → Label) (beta : Label) (hMk : M ≤ k)
    (hheavy : k < M * OuterWordTests.multiplicity word beta) :
    ∃ a b : Fin k, a ≠ b ∧ word a = beta ∧ word b = beta := by
  classical
  have hm : 1 < OuterWordTests.multiplicity word beta := by
    by_contra h
    have hle : OuterWordTests.multiplicity word beta ≤ 1 := Nat.le_of_not_gt h
    have hmul := Nat.mul_le_mul_left M hle
    simp only [Nat.mul_one] at hmul
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hm
  exact ⟨a, b, hab, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩

theorem rich_or_heavy_word {Label : Type uLabel} [DecidableEq Label]
    {k M : ℕ} (word : Fin k → Label) (color : Label → Bool)
    (hbalance : k ≤ 10 * (OuterWordTests.lightPositions M word).card →
      ∀ b, (OuterWordTests.lightPositions M word).card ≤
        4 * ((OuterWordTests.lightPositions M word).filter fun j => color (word j) = b).card) :
    (∀ b, k ≤ 100 * (Finset.univ.filter fun j => color (word j) = b).card) ∨
      ((¬ k ≤ 10 * (OuterWordTests.lightPositions M word).card) ∧
        ∃ i : Fin k, k < M * OuterWordTests.multiplicity word (word i)) := by
  classical
  by_cases hlight : k ≤ 10 * (OuterWordTests.lightPositions M word).card
  · exact Or.inl (rich_of_light_balanced word color hlight (hbalance hlight))
  · exact Or.inr ⟨hlight, exists_heavy_label_of_few_light word hlight⟩

end QuantitativeVanDerWaerden

end OAI
