import OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionLaw
import OAI.NumberTheory.TwoPoint.Circuits.CircuitGateFailure

namespace OAI

/-! The three-valued restriction law is exactly the experiment that first
chooses live bits and then independent uniform values for the fixed bits. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.independent_average_pair {n : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] (μ : Fin n → FiniteLaw α) (ν : Fin n → FiniteLaw β)
    (f : (Fin n → α) → (Fin n → β) → ℝ) :
    (independent (fun i => (μ i).product (ν i))).average
      (fun z => f (fun i => (z i).1) (fun i => (z i).2)) =
      (independent μ).average (fun x => (independent ν).average (f x)) := by
  let e : (Fin n → α × β) ≃ ((Fin n → α) × (Fin n → β)) :=
    { toFun := fun z => (fun i => (z i).1, fun i => (z i).2)
      invFun := fun z i => (z.1 i, z.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ z : (Fin n → α) × (Fin n → β),
        (independent (fun i => (μ i).product (ν i))).weight (fun i => (z.1 i, z.2 i)) *
          f z.1 z.2 := by
      exact (e.symm.sum_comp (fun z =>
        (independent (fun i => (μ i).product (ν i))).weight z *
          f (fun i => (z i).1) (fun i => (z i).2))).symm
    _ = _ := by
      simp only [average, independent, product, prod_mul_distrib, Fintype.sum_prod_type,
        mul_sum, mul_assoc]

lemma bernoulli_half_average {n : ℕ} (f : BooleanCube n → ℝ) :
    (bernoulliCubeLaw n (1 / 2) (by norm_num) (by norm_num)).average f = cubeAverage f := by
  have hw (x : BooleanCube n) :
      (bernoulliCubeLaw n (1 / 2) (by norm_num) (by norm_num)).weight x =
        (1 / 2 : ℝ) ^ n := by
    norm_num [bernoulliCubeLaw, FiniteLaw.independent, booleanLaw, one_div]
    simp only [one_div, inv_pow]
  simp only [FiniteLaw.average, hw, ← mul_sum]
  simp [cubeAverage, BooleanCube, div_eq_mul_inv, mul_comm]

def partialAssignmentOfMask {n : ℕ} (mask y : BooleanCube n) : PartialAssignment n :=
  fun i => if mask i then none else some (y i)

lemma partialAssignmentOfMask_apply {n : ℕ} (mask y x : BooleanCube n) :
    (partialAssignmentOfMask mask y).apply x = restrictCube (sampledCoordinates mask) y x := by
  funext i
  cases hi : mask i <;> simp [partialAssignmentOfMask, PartialAssignment.apply,
    restrictCube, sampledCoordinates, hi]

lemma restriction_pair_atom (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (z : Option Bool) :
    ((booleanLaw p hp hp1).product (booleanLaw (1 / 2) (by norm_num) (by norm_num))).probability
      (fun b => (if b.1 then none else some b.2) = z) =
        (restrictionBitLaw p hp hp1).weight z := by
  cases z with
  | none => simp [FiniteLaw.probability, FiniteLaw.average, FiniteLaw.product,
      booleanLaw, restrictionBitLaw, Fintype.sum_prod_type]; ring
  | some b => cases b <;>
      simp [FiniteLaw.probability, FiniteLaw.average, FiniteLaw.product,
        booleanLaw, restrictionBitLaw, Fintype.sum_prod_type] <;> ring

theorem restrictionLaw_average {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : PartialAssignment n → ℝ) :
    (restrictionLaw n p hp hp1).average f =
      (bernoulliCubeLaw n p hp hp1).average (fun mask =>
        cubeAverage (fun y => f (partialAssignmentOfMask mask y))) := by
  have hm := FiniteLaw.independent_average_map
    (fun _ : Fin n => (booleanLaw p hp hp1).product
      (booleanLaw (1 / 2) (by norm_num) (by norm_num)))
    (fun _ : Fin n => restrictionBitLaw p hp hp1)
    (fun _ b => if b.1 then none else some b.2)
    (fun _ z => restriction_pair_atom p hp hp1 z) f
  unfold restrictionLaw
  rw [← hm]
  change (FiniteLaw.independent (fun _ : Fin n => (booleanLaw p hp hp1).product
    (booleanLaw (1 / 2) (by norm_num) (by norm_num)))).average
      (fun z => f (partialAssignmentOfMask (fun i => (z i).1) (fun i => (z i).2))) = _
  refine (FiniteLaw.independent_average_pair (fun _ : Fin n => booleanLaw p hp hp1)
    (fun _ : Fin n => booleanLaw (1 / 2) (by norm_num) (by norm_num))
    (fun mask y => f (partialAssignmentOfMask mask y))).trans ?_
  apply congrArg (bernoulliCubeLaw n p hp hp1).average
  funext mask
  exact bernoulli_half_average _

end TwoPointCorrelations

end OAI
