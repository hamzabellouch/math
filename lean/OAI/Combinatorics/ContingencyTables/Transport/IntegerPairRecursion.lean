import OAI.Combinatorics.ContingencyTables.Transport.IntegerFutureSquare

namespace OAI

/-! # Balanced coefficients and the actual integer child potentials -/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def oneHole (F : (I → ℕ) → ℝ) (z : I → ℕ) (i : I) : ℝ :=
  if 0 < z i then F (removeOne z i) else 0

omit [Fintype I] in
lemma profile_removeOne_old (z : I → ℕ) (a b : ℕ) (i : I) :
    removeOne (profile z a b) (.inl i) = profile (removeOne z i) a b := by
  funext t
  rcases t with k | (_ | _) <;> simp [profile, removeOne]

omit [Fintype I] in
lemma profile_removeOne_a (z : I → ℕ) (a b : ℕ) :
    removeOne (profile z a b) (.inr false) = profile z (a-1) b := by
  funext t
  rcases t with k | (_ | _) <;> simp [profile, removeOne]

omit [Fintype I] in
lemma profile_removeOne_b (z : I → ℕ) (a b : ℕ) :
    removeOne (profile z a b) (.inr true) = profile z a (b-1) := by
  funext t
  rcases t with k | (_ | _) <;> simp [profile, removeOne]

omit [Fintype I] in
lemma old_hole_sum (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U : ℕ) (i : I) :
    (∑ j ∈ Finset.range (U+1), oneHole F (profile z j (U-j)) (.inl i)) =
      oneHole (marginal F U) z i := by
  simp only [oneHole, profile_removeOne_old]
  change (∑ j ∈ Finset.range (U+1), if 0 < z i then
    F (profile (removeOne z i) j (U-j)) else 0) =
      if 0 < z i then marginal F U (removeOne z i) else 0
  by_cases hp : 0 < z i <;> simp [hp, marginal]

omit [Fintype I] in
lemma child_hole_a (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U j : ℕ) (hj : j ≤ U) :
    oneHole F (profile z j (U-j)) (.inr false) = innerWeight F (U+1) z j := by
  unfold oneHole
  rw [profile_removeOne_a]
  change (if 0 < j then F (profile z (j-1) (U-j)) else 0) = _
  unfold innerWeight
  by_cases hp : 0 < j
  · rw [ite_eq_left hp, ite_eq_left (by omega)]
    congr 1
  · rw [ite_eq_right hp, ite_eq_right (by omega)]

omit [Fintype I] in
lemma child_hole_b (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U j : ℕ) (hj : j ≤ U) :
    oneHole F (profile z j (U-j)) (.inr true) = innerWeight F (U+1) z (j+1) := by
  unfold oneHole
  rw [profile_removeOne_b]
  change (if 0 < U-j then F (profile z j (U-j-1)) else 0) = _
  unfold innerWeight
  by_cases hp : j < U
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    simp only [Nat.add_sub_cancel]
    congr 1
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma child_old_signed_mass (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U j : ℕ) (hj : j ≤ U) (h : I → ℝ) :
    (∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i) = cross F (U+1) z (j+1) h := by
  rw [← cross_a F (U+1) z (j+1) (by omega), old_single]
  apply Finset.sum_congr rfl
  intro i _
  have hv : ValidPair (profile z (j+1) (U+1-(j+1))) (.inl i) (.inr false) ↔ 0 < z i := by
    simp [ValidPair, profile]
  unfold IntegerMarginal.pairMatrix integerRemovalMatrix
  rw [if_congr hv rfl rfl, profile_removeOldA]
  unfold oneHole
  rw [profile_removeOne_old]
  simp only [Nat.add_sub_cancel, Nat.add_sub_add_right]
  change (if 0 < z i then F (profile (removeOne z i) j (U-j)) else 0) * h i =
    h i * (if 0 < z i then F (profile (removeOne z i) j (U-j)) else 0)
  exact mul_comm _ _

/-- The cumulative coefficients balance every integer child, including
zero-capacity endpoint removals. -/
theorem integer_child_balance
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U j : ℕ) (hj : j ≤ U)
    (h : I → ℝ)
    (hpos : ∀ k, 0 < k → k < U+1 → 0 < innerWeight F (U+1) z k)
    (hbal : pairCumulative (cross F (U+1) z) h (U+1) = 0) :
    let g := pairCoefficient (cross F (U+1) z) (innerWeight F (U+1) z) h
    ∑ i : I ⊕ Bool, oneHole F (profile z j (U-j)) i *
      extendCoefficients h (g j) (g (j+1)) i = 0 := by
  dsimp only
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, extendCoefficients_inl,
    extendCoefficients_a, extendCoefficients_b, mul_neg]
  rw [child_old_signed_mass F z U j hj, child_hole_a F z U j hj, child_hole_b F z U j hj]
  rw [pairCoefficient_represents_le _ _ (U+1) h hpos hbal (by omega),
    pairCoefficient_represents_le _ _ (U+1) h hpos hbal (by omega)]
  rw [pairCumulative_succ]
  ring


noncomputable def holePotential (F : (I → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ) : ℝ :=
  ∑ i, oneHole F z i * h i ^ 2

lemma child_potential (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ)
    (U j : ℕ) (hj : j ≤ U) (h : I → ℝ) (g : ℕ → ℝ) :
    holePotential F (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1))) =
      (∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i ^ 2) +
      (innerWeight F (U+1) z j * g j ^ 2 + innerWeight F (U+1) z (j+1) * g (j+1) ^ 2) := by
  simp only [holePotential, Fintype.sum_sum_type, Fintype.sum_bool,
    extendCoefficients_inl, extendCoefficients_a, extendCoefficients_b, neg_sq]
  rw [child_hole_a F z U j hj, child_hole_b F z U j hj]
  ring

/-- The old potential partitions and the two fresh-hole contributions
have identical sums, including both invalid endpoint holes. -/
theorem integer_potential_increment
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (U+1),
      holePotential F (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1)))) =
      holePotential (marginal F U) z h +
        2 * ∑ j ∈ Finset.range (U+2), innerWeight F (U+1) z j * g j ^ 2 := by
  have hold : (∑ j ∈ Finset.range (U+1),
      ∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i ^ 2) =
      holePotential (marginal F U) z h := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, old_hole_sum]
    rfl
  have hshift := Finset.sum_range_sub'
    (fun j => innerWeight F (U+1) z j * g j ^ 2) (U+1)
  rw [Finset.sum_sub_distrib] at hshift
  have hz0 : innerWeight F (U+1) z 0 = 0 := by simp [innerWeight]
  have hzM : innerWeight F (U+1) z (U+1) = 0 := by simp [innerWeight]
  rw [hz0, hzM, zero_mul, zero_mul, sub_self] at hshift
  have hend : (∑ j ∈ Finset.range (U+2), innerWeight F (U+1) z j * g j ^ 2) =
      ∑ j ∈ Finset.range (U+1), innerWeight F (U+1) z j * g j ^ 2 := by
    rw [show U+2 = (U+1)+1 by omega, Finset.sum_range_succ]
    simp [innerWeight]
  calc
    _ = (∑ j ∈ Finset.range (U+1),
        ((∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i ^ 2) +
        (innerWeight F (U+1) z j * g j ^ 2 + innerWeight F (U+1) z (j+1) * g (j+1) ^ 2))) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact child_potential F z U j (by have := Finset.mem_range.mp hj; omega) h g
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hold, hend]
      linarith

/-- A split is controlled by the actual D'=U+1 integer removal forms.
These are precisely the interior signatures available in the manuscript. -/
theorem integer_split_potential_bound
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U : ℕ) (h : I → ℝ)
    (hsig : ∀ j, 0 < j → j < U+1 →
      OnePositiveDirection (integerRemovalMatrix F (profile z j (U+1-j))).toBilin')
    (hpos : ∀ j, 0 < j → j < U+1 → 0 < F (profile z (j-1) (U-j)))
    (hbalance : pairCumulative (cross F (U+1) z) h (U+1) = 0) :
    let g := pairCoefficient (cross F (U+1) z) (innerWeight F (U+1) z) h
    (∑ j ∈ Finset.range (U+1),
      holePotential F (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1)))) ≤
      holePotential (marginal F U) z h -
        ∑ j ∈ Finset.range (U+2), (j:ℝ)*(((U+1:ℕ):ℝ)-(j:ℝ)) *
          (pairMatrix F (U+1) z j).toBilin' (old h) (old h) := by
  dsimp only
  rw [integer_potential_increment]
  have hp := weighted_pair_potential F (U+1) z h hsig (by
    intro j hj0 hjU
    simpa only [Nat.add_sub_cancel] using hpos j hj0 hjU) hbalance
  linarith


noncomputable def holeLinear (G : (I → ℕ) → ℝ) (z : I → ℕ) (h : I → ℝ) : ℝ :=
  ∑ i, oneHole G z i * h i

/-- Equal resulting one-hole states cancel across adjacent branches.
The numerator family G may already include the arbitrary test function H. -/
theorem integer_demand_conservation
    (G : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U : ℕ)
    (h : I → ℝ) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (U+1),
      holeLinear G (profile z j (U-j)) (extendCoefficients h (g j) (g (j+1)))) =
      holeLinear (marginal G U) z h := by
  have hold : (∑ j ∈ Finset.range (U+1),
      ∑ i, oneHole G (profile z j (U-j)) (.inl i) * h i) =
      holeLinear (marginal G U) z h := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, old_hole_sum]
    rfl
  have hshift := Finset.sum_range_sub'
    (fun j => innerWeight G (U+1) z j * g j) (U+1)
  rw [Finset.sum_sub_distrib] at hshift
  have hzero0 : innerWeight G (U+1) z 0 = 0 := by simp [innerWeight]
  have hzeroM : innerWeight G (U+1) z (U+1) = 0 := by simp [innerWeight]
  rw [hzero0, hzeroM, zero_mul, zero_mul, sub_self] at hshift
  calc
    _ = ∑ j ∈ Finset.range (U+1),
        ((∑ i, oneHole G (profile z j (U-j)) (.inl i) * h i) +
        (innerWeight G (U+1) z j * g j - innerWeight G (U+1) z (j+1) * g (j+1))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjU : j ≤ U := by have := Finset.mem_range.mp hj; omega
      simp only [holeLinear, Fintype.sum_sum_type, Fintype.sum_bool,
        extendCoefficients_inl, extendCoefficients_a, extendCoefficients_b, mul_neg]
      rw [child_hole_a G z U j hjU, child_hole_b G z U j hjU]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hold, hshift, add_zero]

/-- Parent balance is exactly the zero cumulative cross mass required
by the weighted pair theorem. -/
theorem cumulative_eq_parent_demand
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (z : I → ℕ) (U : ℕ) (h : I → ℝ) :
    pairCumulative (cross F (U+1) z) h (U+1) =
      holeLinear (marginal F U) z h := by
  unfold pairCumulative
  calc
    _ = ∑ j ∈ Finset.range (U+1), ∑ i, oneHole F (profile z j (U-j)) (.inl i) * h i := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (child_old_signed_mass F z U j (by have := Finset.mem_range.mp hj; omega) h).symm
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, old_hole_sum]
      rfl

end ContingencyTables.IntegerWeightedTransport

end OAI
