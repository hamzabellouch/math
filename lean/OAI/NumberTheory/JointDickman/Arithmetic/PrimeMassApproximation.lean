import OAI.NumberTheory.JointDickman.Arithmetic.PrimeNormalizer
import OAI.NumberTheory.JointDickman.Amplification.ReciprocalTail

namespace OAI

/-!
# Removing the local odds correction from prime-product masses

For every event, the independent-subset mass differs from the uncorrected
Euler weight by at most the sum of squared selection probabilities.
The resulting prime-tail error is uniform over events.
-/

namespace JointDickman

open Finset

noncomputable def uncorrectedSubsetMass (P : Finset ℕ) (q : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  (∏ p ∈ P, (1 - q p)) * ∏ p ∈ S, q p

theorem uncorrectedSubsetMass_identity {P S : Finset ℕ} (q : ℕ → ℝ) (hS : S ⊆ P) :
    uncorrectedSubsetMass P q S = bernoulliSubsetMass P q S * ∏ p ∈ S, (1 - q p) := by
  unfold uncorrectedSubsetMass bernoulliSubsetMass
  rw [← prod_sdiff hS (f := fun p => 1 - q p)]
  ring

theorem uncorrectedSubsetMass_le {P S : Finset ℕ} {q : ℕ → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    uncorrectedSubsetMass P q S ≤ bernoulliSubsetMass P q S := by
  rw [uncorrectedSubsetMass_identity q hS]
  have hp : (∏ p ∈ S, (1 - q p)) ≤ 1 := prod_le_one₀
    (fun p hp => sub_nonneg.mpr (hq p (hS hp)).2)
    (fun p hp => by linarith [(hq p (hS hp)).1])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (bernoulliSubsetMass_nonneg hS hq)

theorem uncorrectedSubsetMass_sum (P : Finset ℕ) (q : ℕ → ℝ) :
    (∑ S ∈ P.powerset, uncorrectedSubsetMass P q S) = ∏ p ∈ P, (1 - (q p) ^ 2) := by
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * ∏ p ∈ S, (1 - q p) := by
      apply sum_congr rfl
      intro S hS
      exact uncorrectedSubsetMass_identity q (mem_powerset.mp hS)
    _ = ∏ p ∈ P, (1 - q p + q p * (1 - q p)) := bernoulliSubsetMass_tilt P q _
    _ = _ := prod_congr rfl (fun p _ => by ring)

theorem one_sub_prod_le_sum (P : Finset ℕ) {f : ℕ → ℝ}
    (hf : ∀ p ∈ P, 0 ≤ f p ∧ f p ≤ 1) :
    1 - ∏ p ∈ P, (1 - f p) ≤ ∑ p ∈ P, f p := by
  rw [prod_one_sub_ordered, sub_sub_cancel]
  apply sum_le_sum
  intro p hp
  have hprod : (∏ q ∈ P with q < p, (1 - f q)) ≤ 1 := prod_le_one₀
    (fun q hq => sub_nonneg.mpr (hf q (mem_filter.mp hq).1).2)
    (fun q hq => by linarith [(hf q (mem_filter.mp hq).1).1])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (hf p hp).1

open Classical in
theorem uncorrectedSubsetMass_event_error (P : Finset ℕ) (q : ℕ → ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (E : Finset ℕ → Prop) :
    |(∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P q S else 0) -
      (∑ S ∈ P.powerset, if E S then uncorrectedSubsetMass P q S else 0)| ≤
      ∑ p ∈ P, (q p) ^ 2 := by
  have hδ (S : Finset ℕ) (hS : S ∈ P.powerset) :
      0 ≤ bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S :=
    sub_nonneg.mpr (uncorrectedSubsetMass_le (mem_powerset.mp hS) hq)
  calc
    _ = |∑ S ∈ P.powerset, if E S then
        bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S else 0| := by
      congr 1
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro S _
      split_ifs <;> ring
    _ = ∑ S ∈ P.powerset, if E S then
        bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S else 0 :=
      abs_of_nonneg (sum_nonneg (fun S hS => by split_ifs <;> first | exact hδ S hS | rfl))
    _ ≤ ∑ S ∈ P.powerset, (bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S) := by
      apply sum_le_sum
      intro S hS
      split_ifs <;> first | exact le_refl _ | exact hδ S hS
    _ = 1 - ∏ p ∈ P, (1 - (q p) ^ 2) := by
      rw [sum_sub_distrib, bernoulliSubsetMass_sum, uncorrectedSubsetMass_sum]
    _ ≤ _ := one_sub_prod_le_sum P (fun p hp => ⟨sq_nonneg _, by nlinarith [(hq p hp).1, (hq p hp).2]⟩)

open Classical in
/-- The local mass correction is uniformly small without any restriction
on the event or on the size of the selected prime product. -/
theorem primeSubsetMass_event_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (E : Finset ℕ → Prop) :
    |(∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P (fun p => z / p) S else 0) -
      (∑ S ∈ P.powerset, if E S then uncorrectedSubsetMass P (fun p => z / p) S else 0)| ≤
      z ^ 2 / (N : ℝ) := by
  have hq : ∀ p ∈ P, 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨div_nonneg hz hp0.le, (div_le_one hp0).mpr (hz1.trans hp1)⟩
  calc
    _ ≤ ∑ p ∈ P, (z / (p : ℝ)) ^ 2 := uncorrectedSubsetMass_event_error P _ hq E
    _ = z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ z ^ 2 * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (sq_nonneg z)
    _ = _ := by ring

end JointDickman

end OAI
