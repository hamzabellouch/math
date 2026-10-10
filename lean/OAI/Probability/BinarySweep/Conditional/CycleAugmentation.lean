import Mathlib
import OAI.Probability.BinarySweep.Conditional.PlacementCycleMoment
import OAI.Probability.BinarySweep.Conditional.WeightedCycle

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

lemma placement_weighted_cycle_bound_pos (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r)
    {N : ℕ} (hN : 0<N) (reverse : Fin N → Bool) :
    (∑x : Fin N → Placement H k 0, ∏i,
      placementEdge H z (reverse i) (x i) (x (finRotate N i))*
      Real.exp (-placementEdgeCost H z (reverse i) (x i) (x (finRotate N i))/(N:ℝ))) ≤
      Real.exp (-pathCost H+Real.log 4*k*b) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simpa only [Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one] using
    placement_weighted_cycle_bound H hd hz hzr k n reverse

omit [Fintype A] in
lemma placementFiberMoment_nonneg (z : ℝ) (q : ℕ) (x y : Placement H k 0) :
    0≤placementFiberMoment H e σ z q x y := by
  unfold placementFiberMoment
  split_ifs
  · exact evenMoment_nonneg _ _
  · rfl

theorem induced_placement_of_hook_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r)
    (hσ : ∀g v, ‖σ g v‖=‖v‖) {q : ℕ} (hq : 0<q) (B : ℝ)
    (hf : ∀x y : Placement H k 0, 0<placementKernel H z x y →
      placementFiberMoment H e σ z q x y ≤
        Real.exp (B-placementTransitionCost H z x (placementIdentification H k y))) :
    evenMoment q (inducedPlacementAverage H e σ z) ≤
      Real.exp (B-pathCost H+Real.log 4*k*b) := by
  have hz1 := hzr.trans_lt (linePerturbationRadius_lt_one r)
  have hqR : (0:ℝ)<(2*q:ℕ) := by positivity
  have hf' (x y : Placement H k 0) :
      (placementFiberMoment H e σ z q x y)^(((2*q:ℕ):ℝ)⁻¹) ≤
        Real.exp (B/((2*q:ℕ):ℝ))*
          Real.exp (-placementTransitionCost H z x (placementIdentification H k y)/((2*q:ℕ):ℝ)) := by
    have hle : placementFiberMoment H e σ z q x y ≤
        Real.exp (B-placementTransitionCost H z x (placementIdentification H k y)) := by
      by_cases hp : 0<placementKernel H z x y
      · exact hf x y hp
      · simp only [placementFiberMoment,dite_eq_right hp]
        exact (Real.exp_pos _).le
    refine (Real.rpow_le_rpow (placementFiberMoment_nonneg H e σ z q x y) hle
      (inv_nonneg.mpr hqR.le)).trans_eq ?_
    rw [←Real.exp_mul,←Real.exp_add]
    congr 1
    ring
  have hconst : (∏_j : Fin (2*q), Real.exp (B/((2*q:ℕ):ℝ)))=Real.exp B := by
    rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.exp_nat_mul]
    congr 1
    field_simp
  let rev (j : Fin (2*q)) := decide (j.val%2≠0)
  have hedge (x : Fin (2*q) → Placement H k 0) (j : Fin (2*q)) :
      (if j.val%2=0 then placementFiberMoment H e σ z q (x j) (x (finRotate (2*q) j))
        else placementFiberMoment H e σ z q (x (finRotate (2*q) j)) (x j))^(((2*q:ℕ):ℝ)⁻¹) ≤
        Real.exp (B/((2*q:ℕ):ℝ))*
          Real.exp (-placementEdgeCost H z (rev j) (x j) (x (finRotate (2*q) j))/((2*q:ℕ):ℝ)) := by
    by_cases hj : j.val%2=0
    · simpa only [rev,placementEdgeCost,decide_eq_true_eq,ne_eq,hj,not_false_eq_true,not_true_eq_false,
        ite_true,ite_false] using hf' (x j) (x (finRotate (2*q) j))
    · simpa only [rev,placementEdgeCost,decide_eq_true_eq,ne_eq,hj,not_false_eq_true,not_true_eq_false,
        ite_true,ite_false] using hf' (x (finRotate (2*q) j)) (x j)
  have hs := induced_placement_cycle_bound H e σ hz hz1 hσ hq
  refine hs.trans ?_
  calc
    _ ≤ ∑x : Fin (2*q) → Placement H k 0,
      (∏j, placementEdge H z (rev j) (x j) (x (finRotate (2*q) j)))*
        ∏j, (Real.exp (B/((2*q:ℕ):ℝ))*
          Real.exp (-placementEdgeCost H z (rev j) (x j) (x (finRotate (2*q) j))/((2*q:ℕ):ℝ))) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left
      · apply Finset.prod_le_prod₀
        · intro j _
          apply Real.rpow_nonneg
          split_ifs <;> exact placementFiberMoment_nonneg H e σ z q _ _
        · intro j _; exact hedge x j
      · apply Finset.prod_nonneg
        intro j _
        unfold placementEdge
        split_ifs <;> exact placementKernel_nonneg H hz hz1 _ _
    _ = Real.exp B * (∑x : Fin (2*q) → Placement H k 0, ∏j,
      placementEdge H z (rev j) (x j) (x (finRotate (2*q) j))*
        Real.exp (-placementEdgeCost H z (rev j) (x j) (x (finRotate (2*q) j))/((2*q:ℕ):ℝ))) := by
      simp_rw [Finset.prod_mul_distrib,hconst]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ Real.exp B * Real.exp (-pathCost H+Real.log 4*k*b) :=
      mul_le_mul_of_nonneg_left (placement_weighted_cycle_bound_pos H hd hz hzr
        (by omega) rev) (Real.exp_pos B).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end BinaryCoordinateSweeps

end

end OAI
