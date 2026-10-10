import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSetWeights

namespace OAI

/-!
# Reducing local weights by random forbidding

The upper sieve is applied to deterministic forbidden congruences. Randomly
forbidding each form converts that bound to the product of its local weights,
without changing the remainder. The transfer below is exact on finite sets;
the deterministic upper-sieve estimate is a separate published input.
-/

namespace JointDickman

open Finset

/-- A point survives if none of its vanishing forms is selected. -/
noncomputable def avoidsSelected {ι : Type*} [DecidableEq ι]
    (S E : Finset ι) : ℝ := if Disjoint S E then 1 else 0

private theorem avoidsSelected_eq_product {ι : Type*} [DecidableEq ι]
    (S E : Finset ι) : avoidsSelected S E = ∏ i ∈ S, if i ∈ E then (0 : ℝ) else 1 := by
  classical
  by_cases h : Disjoint S E
  · rw [avoidsSelected, ite_eq_left h]
    symm
    apply prod_eq_one
    intro i hi
    have hn : i ∉ E := fun he => Finset.disjoint_left.mp h hi he
    simp [hn]
  · rw [avoidsSelected, ite_eq_right h]
    symm
    obtain ⟨i, hi, he⟩ := Finset.not_disjoint_iff.mp h
    exact prod_eq_zero hi (by simp [he])

/-- Average survival is exactly the product of the retained local weights. -/
theorem bernoulliSubsetMass_avoids {ι : Type*} [DecidableEq ι]
    (P E : Finset ι) (hE : E ⊆ P) (θ : ι → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S * avoidsSelected S E) =
      ∏ i ∈ E, θ i := by
  simp_rw [avoidsSelected_eq_product]
  rw [bernoulliSubsetMass_tilt]
  calc
    (∏ i ∈ P, (1 - (1 - θ i) + (1 - θ i) * if i ∈ E then (0 : ℝ) else 1)) =
        ∏ i ∈ P, if i ∈ E then θ i else 1 := by
      apply prod_congr rfl
      intro i _
      split_ifs <;> ring
    _ = ∏ i ∈ E, θ i := by
      rw [← prod_subset hE]
      · apply prod_congr rfl
        intro i hi
        simp [hi]
      · intro i _ hi
        simp [hi]

/-- Exact finite expectation identity for a population of points. -/
theorem randomized_sifted_mass {ι X : Type*} [DecidableEq ι] [Fintype X]
    (P : Finset ι) (E : X → Finset ι) (hE : ∀ x, E x ⊆ P)
    (w : X → ℝ) (θ : ι → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
      ∑ x, w x * avoidsSelected S (E x)) = ∑ x, w x * ∏ i ∈ E x, θ i := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  calc
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        (w x * avoidsSelected S (E x))) =
      w x * ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        avoidsSelected S (E x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      ring
    _ = _ := by rw [bernoulliSubsetMass_avoids P (E x) (hE x)]

/-- A deterministic upper-sieve estimate for every choice of forbidden
forms transfers to reducing weights with the same remainder and constant.
The second population can be the product of the local residue spaces. -/
theorem upper_sieve_reducing_weights {ι X Y : Type*} [DecidableEq ι]
    [Fintype X] [Fintype Y] (P : Finset ι)
    (E : X → Finset ι) (F : Y → Finset ι)
    (hE : ∀ x, E x ⊆ P) (hF : ∀ y, F y ⊆ P)
    (w : X → ℝ) (v : Y → ℝ) (θ : ι → ℝ)
    (hθ : ∀ i ∈ P, 0 ≤ θ i ∧ θ i ≤ 1) (C R : ℝ)
    (hupper : ∀ S ⊆ P, (∑ x, w x * avoidsSelected S (E x)) ≤
      C * (∑ y, v y * avoidsSelected S (F y)) + R) :
    (∑ x, w x * ∏ i ∈ E x, θ i) ≤
      C * (∑ y, v y * ∏ i ∈ F y, θ i) + R := by
  have hq : ∀ i ∈ P, 0 ≤ 1 - θ i ∧ 1 - θ i ≤ 1 := by
    intro i hi
    constructor <;> linarith [(hθ i hi).1, (hθ i hi).2]
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        ∑ x, w x * avoidsSelected S (E x) :=
      (randomized_sifted_mass P E hE w θ).symm
    _ ≤ ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        (C * (∑ y, v y * avoidsSelected S (F y)) + R) := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left (hupper S (mem_powerset.mp hS))
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq)
    _ = C * (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        ∑ y, v y * avoidsSelected S (F y)) +
        R * (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S) := by
      simp_rw [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro S _ <;> ring_nf
    _ = _ := by rw [randomized_sifted_mass P F hF v θ, bernoulliSubsetMass_sum]; ring

end JointDickman

end OAI
