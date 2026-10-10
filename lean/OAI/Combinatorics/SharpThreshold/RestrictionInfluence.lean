import Mathlib

namespace OAI

universe u

/-! Finite-product averaging for pivotal influences under restrictions. -/
noncomputable section
open scoped BigOperators

namespace Problem313.RestrictionInfluence

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Bernoulli weight on an arbitrary finite set of coordinates. -/
def weight (p : ℝ) (x : ι → Bool) : ℝ :=
  ∏ i, if x i = true then p else 1 - p

/-- The pivotal influence, with the redundant pivotal coordinate included in the sum. -/
def influence (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) : ℝ := by
  classical
  exact ∑ x, if f (Function.update x i true) ≠ f (Function.update x i false)
    then weight p x else 0

variable (P : ι → Prop) [DecidablePred P]

/-- Glue a free and an exterior configuration into a full configuration. -/
def join (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool) : ι → Bool :=
  fun i => if h : P i then x ⟨i, h⟩ else y ⟨i, h⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem join_pos (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // P i}) : join P x y i = x i := by
  simp [join, i.property]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem join_neg (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // ¬ P i}) : join P x y i = y i := by
  simp [join, i.property]

omit [DecidableEq ι] in
/-- Product weights factor across any coordinate partition. -/
theorem weight_join (p : ℝ) (x : {i // P i} → Bool)
    (y : {i // ¬ P i} → Bool) :
    weight p (join P x y) = weight p x * weight p y := by
  unfold weight
  rw [← Fintype.prod_subtype_mul_prod_subtype P]
  simp only [join_pos, join_neg]

/-- Fubini for a coordinate restriction, with the exterior sum outermost. -/
theorem sum_weight_join (p : ℝ) (g : (ι → Bool) → ℝ) :
    (∑ z, weight p z * g z) =
      ∑ y : {i // ¬ P i} → Bool, weight p y *
        ∑ x : {i // P i} → Bool, weight p x * g (join P x y) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => Bool)
  rw [← e.symm.sum_comp (fun z => weight p z * g z)]
  change (∑ z : ({i // P i} → Bool) × ({i // ¬ P i} → Bool),
    weight p (join P z.1 z.2) * g (join P z.1 z.2)) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [weight_join]
  ring

omit [Fintype ι] in
/-- Updating a free coordinate commutes with gluing an exterior configuration. -/
theorem join_update (x : {i // P i} → Bool) (y : {i // ¬ P i} → Bool)
    (i : {i // P i}) (b : Bool) :
    join P (Function.update x i b) y = Function.update (join P x y) i.val b := by
  classical
  funext j
  by_cases hji : j = i.val
  · subst j
    simp [join, i.property]
  · by_cases hj : P j
    · have hsub : (⟨j, hj⟩ : {i // P i}) ≠ i := by
        intro h
        exact hji (congrArg Subtype.val h)
      simp [join, hj, hji, hsub]
    · simp [join, hj, hji]

/-- Averaging one pivotal influence over the exterior recovers the full influence. -/
theorem average_influence (p : ℝ) (f : (ι → Bool) → Bool) (i : {i // P i}) :
    (∑ y : {i // ¬ P i} → Bool,
      weight p y * influence p (fun x => f (join P x y)) i) =
        influence p f i.val := by
  classical
  unfold influence
  have h := sum_weight_join P p (fun z =>
    if f (Function.update z i.val true) ≠ f (Function.update z i.val false)
      then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp only [join_update]

/-- Averaging total influence on the free coordinates gives the sum of their original influences. -/
theorem average_totalInfluence (p : ℝ) (f : (ι → Bool) → Bool) :
    (∑ y : {i // ¬ P i} → Bool, weight p y *
      ∑ i : {i // P i}, influence p (fun x => f (join P x y)) i) =
        ∑ i : {i // P i}, influence p f i.val := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => average_influence P p f i)

end Problem313.RestrictionInfluence

end

end OAI
