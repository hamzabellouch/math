import Mathlib
import OAI.Probability.BinarySweep.Trajectories.Trajectory

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma weighted_entry_bound (n : ℕ) {p C a : ℝ} (hp : 0 ≤ p)
    (hbound : 0 < p → p ≤ Real.exp (C + a)) :
    p * Real.exp (-C / (n+1 : ℝ)) ≤
      Real.exp (a / (n+1 : ℝ)) * p ^ ((n : ℝ) / (n+1 : ℝ)) := by
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simp only [zero_mul]
    positivity
  have hn : (0 : ℝ) < n+1 := by positivity
  have hl : Real.log p ≤ C + a := (Real.log_le_iff_le_exp hp).mpr (hbound hp)
  have he : Real.log p + -C / (n+1 : ℝ) ≤
      a / (n+1 : ℝ) + Real.log p * ((n : ℝ) / (n+1 : ℝ)) := by
    apply (mul_le_mul_iff_left₀ hn).mp
    field_simp
    nlinarith [hl]
  calc
    _ = Real.exp (Real.log p + -C / (n+1 : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hp]
    _ ≤ Real.exp (a / (n+1 : ℝ) + Real.log p * ((n : ℝ) / (n+1 : ℝ))) :=
      Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos hp]

theorem weighted_cycle_le_card {A : Type*} [Fintype A] (n : ℕ)
    (p C : Fin (n+1) → A → A → ℝ) (a : ℝ)
    (hp : ∀ i x y, 0 ≤ p i x y)
    (hsum : ∀ i y, ∑ x, p i x y = 1)
    (hbound : ∀ i x y, 0 < p i x y → p i x y ≤ Real.exp (C i x y + a)) :
    (∑ x : Fin (n+1) → A,
      ∏ i, p i (x i) (x (finRotate (n+1) i)) *
        Real.exp (-C i (x i) (x (finRotate (n+1) i)) / (n+1 : ℝ))) ≤
      Real.exp a * (Fintype.card A : ℝ) := by
  have hconstant : (∏ _i : Fin (n+1), Real.exp (a / (n+1 : ℝ))) = Real.exp a := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  calc
    _ ≤ ∑ x : Fin (n+1) → A,
      ∏ i, Real.exp (a / (n+1 : ℝ)) *
        (p i (x i) (x (finRotate (n+1) i))) ^ ((n : ℝ) / (n+1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.prod_le_prod₀
      · intro i _; exact mul_nonneg (hp _ _ _) (Real.exp_pos _).le
      · intro i _; exact weighted_entry_bound n (hp _ _ _) (hbound _ _ _)
    _ = Real.exp a * (∑ x : Fin (n+1) → A,
      ∏ i, (p i (x i) (x (finRotate (n+1) i))) ^ ((n : ℝ) / (n+1 : ℝ))) := by
      simp_rw [Finset.prod_mul_distrib, hconstant]
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Cyclic.sum_cycle_rpow_le_card n p hp hsum)
      (Real.exp_pos a).le

def placementEdgeCost {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (reverse : Bool) {k : ℕ} (x y : Placement H k 0) : ℝ :=
  if reverse then placementTransitionCost H z y (placementIdentification H k x)
  else placementTransitionCost H z x (placementIdentification H k y)

lemma placementEdge_bound {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (reverse : Bool) {k : ℕ} (x y : Placement H k 0)
    (hp : 0 < placementEdge H z reverse x y) :
    placementEdge H z reverse x y ≤
      Real.exp (placementEdgeCost H z reverse x y +
        (-(k : ℝ) * Real.log (gridSize bits) - pathCost H + Real.log 4 * k * b)) := by
  have hsingle (x y : Placement H k 0) (hp : 0 < placementKernel H z x y) :
      placementKernel H z x y ≤ Real.exp (
        placementTransitionCost H z x (placementIdentification H k y) +
        (-(k : ℝ) * Real.log (gridSize bits) - pathCost H + Real.log 4 * k * b)) := by
    have hc := placement_probability_cost_of_pos H hd hz hzr x
      (placementIdentification H k y) hp
    have hs : (0 : ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
    rw [Real.rpow_def_of_pos hs, ← Real.exp_add] at hc
    convert hc using 1 <;> congr 1
    ring
  cases reverse with
  | false => exact hsingle x y hp
  | true => exact hsingle y x hp

lemma linePerturbationRadius_lt_one (r : ℕ) : linePerturbationRadius r < 1 := by
  have hf : (1 : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 ^ (2 * r))
  unfold linePerturbationRadius
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem placement_weighted_cycle_bound {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (k n : ℕ) (reverse : Fin (n+1) → Bool) :
    (∑ x : Fin (n+1) → Placement H k 0,
      ∏ i, placementEdge H z (reverse i) (x i) (x (finRotate (n+1) i)) *
        Real.exp (-placementEdgeCost H z (reverse i) (x i) (x (finRotate (n+1) i)) /
          (n+1 : ℝ))) ≤ Real.exp (-pathCost H + Real.log 4 * k * b) := by
  have hz1 := hzr.trans_lt (linePerturbationRadius_lt_one r)
  have hc := weighted_cycle_le_card (A := Placement H k 0) n
    (fun i => placementEdge H z (reverse i))
    (fun i => placementEdgeCost H z (reverse i))
    (-(k : ℝ) * Real.log (gridSize bits) - pathCost H + Real.log 4 * k * b)
    (by
      intro i x y
      unfold placementEdge
      split_ifs <;> exact placementKernel_nonneg H hz hz1 _ _)
    (by
      intro i y
      unfold placementEdge
      cases reverse i with
      | false => exact placementKernel_colSum H hz hz1 y
      | true => exact placementKernel_rowSum H hz hz1 y)
    (by intro i x y hp; exact placementEdge_bound H hd hz hzr (reverse i) x y hp)
  rw [card_placement] at hc
  apply hc.trans
  have hcard : ((gridSize bits - h).descFactorial k : ℝ) ≤ (gridSize bits : ℝ) ^ k := by
    exact_mod_cast (Nat.descFactorial_le_pow (gridSize bits - h) k).trans
      (Nat.pow_le_pow_left (Nat.sub_le (gridSize bits) h) k)
  have hs : (0 : ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  calc
    _ ≤ Real.exp (-(k : ℝ) * Real.log (gridSize bits) - pathCost H + Real.log 4 * k * b) *
          (gridSize bits : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hcard (Real.exp_pos _).le
    _ = _ := by
      have he : (gridSize bits : ℝ) ^ k =
          Real.exp ((k : ℝ) * Real.log (gridSize bits)) := by
        rw [Real.exp_nat_mul, Real.exp_log hs]
      rw [he, ← Real.exp_add]
      congr 1
      ring

end BinaryCoordinateSweeps

end

end OAI
