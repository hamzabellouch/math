import OAI.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem weight_le_finiteImageMass {X Z : Type*} [Fintype X] [DecidableEq Z]
    (p : FiniteProbabilityWeights X) (F : X → Z) (x : X) :
    p.weight x ≤ finiteImageMass p F (F x) := by
  classical
  unfold finiteImageMass FiniteProbabilityWeights.mean
  have h := Finset.single_le_sum
    (f := fun y => p.weight y * if F y = F x then (1 : ℝ) else 0)
    (s := Finset.univ) (fun y _ => mul_nonneg (p.nonneg y) (by split_ifs <;> norm_num)) (Finset.mem_univ x)
  simpa only [ite_true, mul_one] using h

theorem finiteImageMass_eq_zero_of_no_preimage {X Z : Type*} [Fintype X] [DecidableEq Z]
    (p : FiniteProbabilityWeights X) (F : X → Z) (z : Z)
    (h : ∀ x, p.weight x ≠ 0 → F x ≠ z) : finiteImageMass p F z = 0 := by
  unfold finiteImageMass FiniteProbabilityWeights.mean
  apply Finset.sum_eq_zero
  intro x _
  dsimp only
  by_cases hx : p.weight x = 0
  · simp only [hx, zero_mul]
  · rw [ite_eq_right (h x hx), mul_zero]

theorem finiteImageMass_support_transport {X Y Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Z]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (F : X → Z) (G : Y → Z)
    (hmass : ∀ z, finiteImageMass p F z = finiteImageMass q G z)
    (P : Z → Prop) (hP : ∀ x, p.weight x ≠ 0 → P (F x))
    (y : Y) (hy : q.weight y ≠ 0) : P (G y) := by
  by_contra hn
  have he : finiteImageMass p F (G y) = 0 := by
    apply finiteImageMass_eq_zero_of_no_preimage
    intro x hx hxy
    apply hn
    rw [← hxy]
    exact hP x hx
  rw [hmass] at he
  have hle := weight_le_finiteImageMass q G y
  rw [he] at hle
  exact hy (le_antisymm hle (q.nonneg y))

end Erdos3

end

end OAI
