import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.PartitionLocalConnectivity
import OAI.Combinatorics.ThinTrees.Continuation.Ramp

namespace OAI

/-! Continuation gains. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Finset
open scoped Classical

variable {m : ℕ}

def booleanResponse (good : Fin m → Prop) : Fin m → ℝ :=
  fun e => if good e then 1 else 0

lemma booleanResponse_bounds (good : Fin m → Prop) (e : Fin m) :
    0 ≤ booleanResponse good e ∧ booleanResponse good e ≤ 1 := by
  unfold booleanResponse
  split_ifs <;> norm_num

lemma good_capacity_nondecreasing {κ t u : ℝ} (ht : 0 ≤ t) (hu : u ≤ 1) (hu0 : 0 ≤ u) :
    u+κ ≤ lowerCapacity κ t u 1 := by
  by_cases he : 0 < u
  · simp only [lowerCapacity,ite_eq_left he]
    have hh : u ≤ min 1 (u+t*(5*(1:ℝ)-4)) := le_min hu (by linarith)
    linarith only [hh]
  · have hz : u=0 := le_antisymm (le_of_not_gt he) hu0
    simp [hz,lowerCapacity]

lemma good_capacity_unsaturated {κ t u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1/2) (ht : t ≤ 1/2) :
    lowerCapacity κ t u 1=u+κ+t := by
  rw [lowerCapacity,ite_eq_left hu,min_eq_right (by linarith : u+t*(5*(1:ℝ)-4) ≤ 1)]
  ring

lemma bad_capacity_loss {κ t u : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (hu1 : u ≤ 1) :
    lowerCapacity κ t u 0=u+κ-4*t := by
  rw [lowerCapacity,ite_eq_left hu,min_eq_right (by linarith : u+t*(5*(0:ℝ)-4) ≤ 1)]
  ring

lemma inactive_capacity {κ t u y : ℝ} (hu : 0 ≤ u) (ha : ¬0 < u) :
    lowerCapacity κ t u y=u+κ := by
  have hz : u=0 := le_antisymm (le_of_not_gt ha) hu
  simp [lowerCapacity,hz]

lemma capacity_change_active (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu : ∀e, 0 ≤ u e) (κ t : ℝ) (y : Fin m → ℝ) :
    (∑e ∈ F, lowerCapacity κ t (u e) (y e))-(∑e ∈ F, (u e+κ)) =
      ∑e ∈ F ∩ Partitions.active u, (lowerCapacity κ t (u e) (y e)-(u e+κ)) := by
  rw [←sum_sub_distrib]
  symm
  apply sum_subset inter_subset_left
  intro e _ he
  have hne : ¬0 < u e := by
    intro hg
    exact he (mem_inter.mpr ⟨by assumption,(Partitions.mem_active u e).mpr hg⟩)
  rw [inactive_capacity (hu e) hne,sub_self]

lemma capacity_change_loss (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t : ℝ} (ht : 0 ≤ t) :
    -4*t*(((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ) ≤
      (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-(∑e ∈ F, (u e+κ)) := by
  rw [capacity_change_active F u hu0]
  have hb (e : Fin m) (he : e ∈ F ∩ Partitions.active u) :
      (if ¬good e then -4*t else 0) ≤
        lowerCapacity κ t (u e) (booleanResponse good e)-(u e+κ) := by
    have ha : 0 < u e := (Partitions.mem_active u e).mp (mem_inter.mp he).2
    by_cases hg : good e
    · simp only [booleanResponse,hg,not_true_eq_false,ite_false,ite_true]
      linarith only [good_capacity_nondecreasing (κ:=κ) ht (hu1 e) (hu0 e)]
    · simp only [booleanResponse,hg,not_false_eq_true,ite_true,ite_false,
        bad_capacity_loss ht ha (hu1 e)]
      ring_nf
      exact le_rfl
  have hs := sum_le_sum hb
  rw [←sum_filter] at hs
  simpa only [sum_const,nsmul_eq_mul,mul_comm] using hs

lemma capacity_change_gain (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/2) :
    t*((F ∩ Partitions.active u).card-
        (((F ∩ Partitions.active u).filter (fun e => 1/2<u e)).card:ℝ)-
        5*(((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ)) ≤
      (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-(∑e ∈ F, (u e+κ)) := by
  rw [capacity_change_active F u hu0]
  have hb (e : Fin m) (he : e ∈ F ∩ Partitions.active u) :
      t-(if 1/2<u e then t else 0)-(if ¬good e then 5*t else 0) ≤
        lowerCapacity κ t (u e) (booleanResponse good e)-(u e+κ) := by
    have ha : 0 < u e := (Partitions.mem_active u e).mp (mem_inter.mp he).2
    by_cases hg : good e
    · simp only [booleanResponse,hg,not_true_eq_false,ite_false,ite_true,sub_zero]
      by_cases hl : 1/2<u e
      · rw [ite_eq_left hl,sub_self]
        linarith only [good_capacity_nondecreasing (κ:=κ) ht (hu1 e) (hu0 e)]
      · rw [ite_eq_right hl,sub_zero,good_capacity_unsaturated ha (le_of_not_gt hl) ht1]
        linarith
    · simp only [booleanResponse,hg,not_false_eq_true,ite_true,ite_false,
        bad_capacity_loss ht ha (hu1 e)]
      split_ifs <;> linarith
  have hs := sum_le_sum hb
  simp only [sum_sub_distrib,←sum_filter,sum_const,nsmul_eq_mul] at hs
  rw [sum_sub_distrib]
  nlinarith only [hs]

lemma large_count_bound (A : Finset (Fin m)) (u : Fin m → ℝ) (hu : ∀e, 0 ≤ u e) :
    (((A.filter (fun e => 1/2<u e)).card:ℝ)) ≤ 2*∑e ∈ A, u e := by
  have hb (e : Fin m) (_ : e ∈ A) : (if 1/2<u e then (1:ℝ) else 0) ≤ 2*u e := by
    split_ifs with hh <;> linarith [hu e]
  have hs := sum_le_sum hb
  rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one,←mul_sum] at hs
  exact hs

lemma active_capacity_sum_le (F : Finset (Fin m)) (u : Fin m → ℝ) (hu : ∀e, 0 ≤ u e)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    (∑e ∈ F ∩ Partitions.active u, u e) ≤ ∑e ∈ F, (u e+κ) := by
  calc
    _ ≤ ∑e ∈ F, u e := sum_le_sum_of_subset_of_nonneg inter_subset_left (fun e _ _ => hu e)
    _ ≤ _ := sum_le_sum (fun e _ => le_add_of_nonneg_right hκ)

lemma many_edges_half_unsaturated (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) {κ r d Q : ℝ} (hκ : 0 ≤ κ) (hr : 1 ≤ r) (hd : 2 ≤ d)
    (hQ : Q ≤ r) (hnear : (∑e ∈ F, (u e+κ)) ≤ Q*(d-1)+1)
    (hmany : 8*r*(d-1) < ((F ∩ Partitions.active u).card:ℝ)) :
    (((F ∩ Partitions.active u).filter (fun e => 1/2<u e)).card:ℝ) ≤
      ((F ∩ Partitions.active u).card:ℝ)/2 := by
  have h1 := large_count_bound (F ∩ Partitions.active u) u hu0
  have h2 := active_capacity_sum_le F u hu0 hκ
  have h3 := mul_le_mul_of_nonneg_right hQ (by linarith : 0 ≤ d-1)
  have hprod : 1 ≤ r*(d-1) := by nlinarith only [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ d-2),hr,hd]
  nlinarith only [h1,h2,h3,hnear,hmany,hprod]

lemma few_edges_loss_bound (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t r d ε g : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hεg : 32*ε ≤ g)
    (hr : 0 ≤ r) (hd : 1 ≤ d)
    (hbad : (((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ) ≤
      ε*(F ∩ Partitions.active u).card)
    (hfew : ((F ∩ Partitions.active u).card:ℝ) ≤ 8*r*(d-1)) :
    -g*r*t*(d-1) ≤ (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-
      (∑e ∈ F, (u e+κ)) := by
  have h1 := capacity_change_loss F u hu0 hu1 good (κ:=κ) ht
  have h2 := mul_le_mul_of_nonneg_left hfew hε
  have h3 := mul_le_mul_of_nonneg_left (hbad.trans h2) (by linarith : 0 ≤ 4*t)
  have h4 := mul_le_mul_of_nonneg_right hεg (mul_nonneg (mul_nonneg hr ht) (by linarith : 0 ≤ d-1))
  nlinarith only [h1,h3,h4]

lemma many_edges_gain_bound (F : Finset (Fin m)) (u : Fin m → ℝ)
    (hu0 : ∀e, 0 ≤ u e) (hu1 : ∀e, u e ≤ 1) (good : Fin m → Prop)
    {κ t r d Q ε : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hκ : 0 ≤ κ)
    (hr : 1 ≤ r) (hd : 2 ≤ d) (hQ : Q ≤ r) (hε : ε ≤ 1/10)
    (hnear : (∑e ∈ F, (u e+κ)) ≤ Q*(d-1)+1)
    (hbad : (((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ) ≤
      ε*(F ∩ Partitions.active u).card)
    (hmany : 8*r*(d-1) < ((F ∩ Partitions.active u).card:ℝ)) :
    0 ≤ (∑e ∈ F, lowerCapacity κ t (u e) (booleanResponse good e))-
      (∑e ∈ F, (u e+κ)) := by
  have h1 := capacity_change_gain F u hu0 hu1 good (κ:=κ) ht ht1
  have h2 := many_edges_half_unsaturated F u hu0 hκ hr hd hQ hnear hmany
  have h3 := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (F ∩ Partitions.active u).card)
  have h4 : 0 ≤ ((F ∩ Partitions.active u).card:ℝ)-
      (((F ∩ Partitions.active u).filter (fun e => 1/2<u e)).card:ℝ)-
      5*(((F ∩ Partitions.active u).filter (fun e => ¬good e)).card:ℝ) := by
    linarith only [h2,h3,hbad]
  exact (mul_nonneg ht h4).trans h1

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
