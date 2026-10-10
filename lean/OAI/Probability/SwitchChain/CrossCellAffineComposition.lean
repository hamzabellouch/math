import OAI.Probability.SwitchChain.CrossCellConditionalExpectation
import OAI.Probability.SwitchChain.CrossIndependent

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossCellMoments
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

include sectionFintypeα sectionFintypeβ in
theorem count_pos_of_state (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell s r c) : 0 < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold CrossBlock.count
  apply Finset.card_pos.mpr
  exact ⟨z.val.1, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact z.property⟩

theorem conditionalRight_constant_of_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3) (g : β → ℝ) (z : Cell s r c) :
    conditionalRight s r c z.val.2.1 g =
      (∑ y, CrossBlock.independentMargin s (c y) * g y) /
        (∑ y, CrossBlock.independentMargin s (c y)) := by
  have hp : (0 : ℝ) < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) :=
    by exact_mod_cast count_pos_of_state s r c z
  rw [CrossBlock.count_eq_independent_product s hs] at hp
  have ha : CrossBlock.independentMargin s (r z.val.2.1) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hp
    exact (lt_irrefl 0 hp)
  rw [conditionalRight_eq_table]
  simp_rw [CrossBlock.count_eq_independent_product s hs, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ ha

theorem conditionalLeft_constant_of_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3) (g : α → ℝ) (z : Cell s r c) :
    conditionalLeft s r c z.val.2.2 g =
      (∑ x, CrossBlock.independentMargin s (r x) * g x) /
        (∑ x, CrossBlock.independentMargin s (r x)) := by
  have hp : (0 : ℝ) < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) :=
    by exact_mod_cast count_pos_of_state s r c z
  rw [CrossBlock.count_eq_independent_product s hs] at hp
  have hb : CrossBlock.independentMargin s (c z.val.2.2) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp
    exact (lt_irrefl 0 hp)
  rw [conditionalLeft_eq_table]
  simp_rw [CrossBlock.count_eq_independent_product s hs]
  have hn : (∑ x, CrossBlock.independentMargin s (r x) *
      CrossBlock.independentMargin s (c z.val.2.2) * g x) =
      (∑ x, CrossBlock.independentMargin s (r x) * g x) *
        CrossBlock.independentMargin s (c z.val.2.2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hn, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ hb

theorem expectation_first_second_affine (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (f : EuclideanSpace ℝ (Cell s r c)) :
    ∃ a b : ℝ, (s ≠ 2 → b = 0) ∧ ∀ z : Cell s r c,
      PairFibers.expectation (firstPartition s r c)
        (PairFibers.expectation (secondPartition s r c) f) z =
          a + b * offCenter r z.val.2.1 := by
  obtain ⟨g,hg⟩ := expectation_factors_key (fun z : Cell s r c => z.val.2.2) f
  by_cases hs : s = 2
  · subst s
    obtain ⟨a,b,hab⟩ := conditionalRight_two_span r c g
    refine ⟨a,b,fun h => (h rfl).elim, ?_⟩
    intro z
    change PairFibers.expectation (firstPartition 2 r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell 2 r c => z.val.2.2)) f) z = _
    rw [hg, expectation_first_right_apply]
    exact hab z.val.2.1
  · refine ⟨(∑ y, CrossBlock.independentMargin s (c y) * g y) /
      (∑ y, CrossBlock.independentMargin s (c y)), 0, fun _ => rfl, ?_⟩
    intro z
    change PairFibers.expectation (firstPartition s r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.2)) f) z = _
    rw [hg, expectation_first_right_apply, zero_mul, add_zero]
    exact conditionalRight_constant_of_ne_two s hs r c g z

theorem expectation_second_first_affine (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (f : EuclideanSpace ℝ (Cell s r c)) :
    ∃ a b : ℝ, (s ≠ 2 → b = 0) ∧ ∀ z : Cell s r c,
      PairFibers.expectation (secondPartition s r c)
        (PairFibers.expectation (firstPartition s r c) f) z =
          a + b * offCenter c z.val.2.2 := by
  obtain ⟨g,hg⟩ := expectation_factors_key (fun z : Cell s r c => z.val.2.1) f
  by_cases hs : s = 2
  · subst s
    obtain ⟨a,b,hab⟩ := conditionalLeft_two_span r c g
    refine ⟨a,b,fun h => (h rfl).elim, ?_⟩
    intro z
    change PairFibers.expectation (secondPartition 2 r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell 2 r c => z.val.2.1)) f) z = _
    rw [hg, expectation_second_left_apply]
    exact hab z.val.2.2
  · refine ⟨(∑ x, CrossBlock.independentMargin s (r x) * g x) /
      (∑ x, CrossBlock.independentMargin s (r x)), 0, fun _ => rfl, ?_⟩
    intro z
    change PairFibers.expectation (secondPartition s r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f) z = _
    rw [hg, expectation_second_left_apply, zero_mul, add_zero]
    exact conditionalLeft_constant_of_ne_two s hs r c g z

end Problem315.CrossCellMoments

end

end OAI
