import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

theorem choose_card_le_sum (s : Finset ℕ) :
    s.card.choose 2 ≤ ∑ d ∈ s, d := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := by
      intro h
      exact (lt_irrefl a) (hmax a h)
    have hsub : s ⊆ Finset.range a := by
      intro x hx
      exact Finset.mem_range.mpr (hmax x hx)
    have hcard : s.card ≤ a := by
      simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    rw [show s.card + 1 = s.card.succ from rfl,
      Nat.choose_succ_succ s.card 1, Nat.choose_one_right]
    exact Nat.add_le_add hcard ih

theorem choose_card_le_sum_of_injOn {ι : Type*} (s : Finset ι)
    (degree : ι → ℕ) (hinj : Set.InjOn degree (s : Set ι)) :
    s.card.choose 2 ≤ ∑ i ∈ s, degree i := by
  have h := choose_card_le_sum (s.image degree)
  rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj] at h
  exact h

def multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (a : κ) : ℕ :=
  (rows.filter fun i => group i = a).card

theorem sum_multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ)
    (hgroups : ∀ i ∈ rows, group i ∈ groups) :
    ∑ a ∈ groups, multiplicity rows group a = rows.card := by
  simpa only [multiplicity, Finset.sum_const, smul_eq_mul, mul_one]
    using Finset.sum_fiberwise_of_maps_to hgroups (fun _ => (1 : ℕ))

theorem sum_choose_multiplicity_le_sum_degree {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) (degree : ι → ℕ)
    (hgroups : ∀ i ∈ rows, group i ∈ groups)
    (hinj : Set.InjOn (fun i => (group i, degree i)) (rows : Set ι)) :
    (∑ a ∈ groups, (multiplicity rows group a).choose 2) ≤
      ∑ i ∈ rows, degree i := by
  calc
    (∑ a ∈ groups, (multiplicity rows group a).choose 2) ≤
        ∑ a ∈ groups, ∑ i ∈ rows.filter (fun i => group i = a), degree i := by
      apply Finset.sum_le_sum
      intro a _
      apply choose_card_le_sum_of_injOn
      intro i hi j hj hdegree
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      apply hinj hi'.1 hj'.1
      exact Prod.ext (hi'.2.trans hj'.2.symm) hdegree
    _ = ∑ i ∈ rows, degree i :=
      Finset.sum_fiberwise_of_maps_to hgroups degree

theorem sum_choose_multiplicity_le_sum_degree_univ
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (degree : ι → ℕ)
    (hinj : Function.Injective (fun i => (group i, degree i))) :
    (∑ a, (multiplicity Finset.univ group a).choose 2) ≤ ∑ i, degree i := by
  exact sum_choose_multiplicity_le_sum_degree Finset.univ Finset.univ group degree
    (by simp) hinj.injOn

theorem sum_multiplicity_univ
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) :
    ∑ a, multiplicity Finset.univ group a = Fintype.card ι := by
  exact sum_multiplicity Finset.univ Finset.univ group (by simp)

theorem sum_sq_multiplicity_sub_card_le_twice_sum_degree
    {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) (degree : ι → ℕ)
    (hgroups : ∀ i ∈ rows, group i ∈ groups)
    (hinj : Set.InjOn (fun i => (group i, degree i)) (rows : Set ι)) :
    (∑ a ∈ groups, (multiplicity rows group a : ℝ) ^ 2) - rows.card ≤
      2 * ∑ i ∈ rows, (degree i : ℝ) := by
  have hnat := sum_choose_multiplicity_le_sum_degree rows groups group degree hgroups hinj
  have hreal : (∑ a ∈ groups, ((multiplicity rows group a).choose 2 : ℝ)) ≤
      ∑ i ∈ rows, (degree i : ℝ) := by exact_mod_cast hnat
  have hsum : (∑ a ∈ groups, (multiplicity rows group a : ℝ)) = rows.card := by
    exact_mod_cast sum_multiplicity rows groups group hgroups
  have hid : 2 * (∑ a ∈ groups, ((multiplicity rows group a).choose 2 : ℝ)) =
      (∑ a ∈ groups, (multiplicity rows group a : ℝ) ^ 2) - rows.card := by
    calc
      _ = ∑ a ∈ groups, ((multiplicity rows group a : ℝ) ^ 2 -
          (multiplicity rows group a : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Nat.cast_choose_two]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, hsum]
  linarith

theorem sum_sq_multiplicity_sub_card_le_twice_sum_degree_univ
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (degree : ι → ℕ)
    (hinj : Function.Injective (fun i => (group i, degree i))) :
    (∑ a, (multiplicity Finset.univ group a : ℝ) ^ 2) - Fintype.card ι ≤
      2 * ∑ i, (degree i : ℝ) := by
  exact sum_sq_multiplicity_sub_card_le_twice_sum_degree Finset.univ Finset.univ
    group degree (by simp) hinj.injOn

theorem sum_multiplicity_eq_card_filter {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) :
    ∑ a ∈ groups, multiplicity rows group a =
      (rows.filter fun i => group i ∈ groups).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter rows groups group

theorem cutoff_mul_high_count_le_sum {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) (cutoff : ℝ)
    (hnonneg : ∀ i ∈ rows, 0 ≤ weight i) :
    cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) ≤
      ∑ i ∈ rows, weight i := by
  classical
  calc
    _ = ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), cutoff := by
      simp [mul_comm]
    _ ≤ ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), weight i := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ rows, weight i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ rows)
      intro i hi _
      exact hnonneg i hi

theorem sum_weight_ge_of_low_count_le {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) {cutoff η : ℝ}
    (hcutoff : 0 ≤ cutoff) (hnonneg : ∀ i ∈ rows, 0 ≤ weight i)
    (hlow : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) ≤
      η * rows.card) :
    cutoff * (1 - η) * rows.card ≤ ∑ i ∈ rows, weight i := by
  classical
  have hcard : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) +
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) = rows.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := rows)
      (fun i => weight i ≤ cutoff))
  have hhigh : (1 - η) * rows.card ≤
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) := by nlinarith
  calc
    _ = cutoff * ((1 - η) * rows.card) := by ring
    _ ≤ cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) :=
      mul_le_mul_of_nonneg_left hhigh hcutoff
    _ ≤ ∑ i ∈ rows, weight i := cutoff_mul_high_count_le_sum rows weight cutoff hnonneg

end PiExponent.Collision

end OAI
