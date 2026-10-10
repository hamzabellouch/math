import Mathlib
import OAI.Combinatorics.KMedian.Process.QuadraticCount

namespace OAI

section
section
namespace MetricKMedian.CountGeometry
open Finset
variable {E U : Type*} [Fintype E] [DecidableEq E] [DecidableEq U]

def overlap (S : E → Finset U) (e f : E) : ℕ :=
  if e=f then 0 else (S e ∩ S f).card

omit [Fintype E] in
theorem overlap_self (S : E → Finset U) (e : E) : overlap S e e=0 := by simp [overlap]
omit [Fintype E] in
theorem overlap_symm (S : E → Finset U) (e f : E) : overlap S e f=overlap S f e := by
  by_cases h : e=f
  · subst f; rfl
  · simp only [overlap, ite_eq_right h, ite_eq_right (Ne.symm h), inter_comm]

omit [Fintype E] in
                                                                                
theorem truncated_union (S : E → Finset U) (T : Finset E) :
    2*(∑ e ∈ T, (S e).card) ≤ 2*(T.biUnion S).card+∑ e ∈ T, ∑ f ∈ T, overlap S e f := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    have hrow : ∑ f ∈ T, overlap S a f = ∑ f ∈ T, (S a ∩ S f).card := by
      apply sum_congr rfl
      intro f hf
      have haf : a ≠ f := by intro h; subst f; exact ha hf
      simp only [overlap, ite_eq_right haf]
    have hcol : ∑ e ∈ T, overlap S e a = ∑ f ∈ T, (S a ∩ S f).card := by
      simp_rw [overlap_symm S _ a]
      exact hrow
    have hint : (S a ∩ T.biUnion S).card ≤ ∑ f ∈ T, (S a ∩ S f).card := by
      rw [inter_biUnion]
      exact card_biUnion_le
    have hcard := card_union_add_card_inter (S a) (T.biUnion S)
    simp only [sum_insert ha, biUnion_insert, overlap_self, zero_add, sum_add_distrib]
    rw [hrow, hcol]
    omega

theorem overlap_row_bound (S : E → Finset U) {D : ℕ}
    (hdegree : ∀ u, (univ.filter (fun e => u ∈ S e)).card ≤ D) (e : E) :
    (∑ f, overlap S e f) ≤ (D-1)*(S e).card := by
  have hpoint : ∀ f, overlap S e f = ∑ u ∈ S e, if f ≠ e ∧ u ∈ S f then (1:ℕ) else 0 := by
    intro f
    rw [sum_boole]
    by_cases h : e=f
    · subst f; simp [overlap]
    · simp only [overlap, ite_eq_right h]
      congr 1
      ext u
      simp only [mem_inter, mem_filter]
      constructor
      · intro hu; exact ⟨hu.1, Ne.symm h, hu.2⟩
      · intro hu; exact ⟨hu.1, hu.2.2⟩
  simp_rw [hpoint]
  rw [sum_comm]
  calc
    (∑ u ∈ S e, ∑ f, if f ≠ e ∧ u ∈ S f then (1:ℕ) else 0) ≤ ∑ _u ∈ S e, (D-1) := by
      apply sum_le_sum
      intro u hu
      rw [sum_boole]
      have he : e ∈ univ.filter (fun f => u ∈ S f) := by simp [hu]
      have hfilter : univ.filter (fun f => f ≠ e ∧ u ∈ S f) =
          (univ.filter (fun f => u ∈ S f)).erase e := by
        ext f
        simp only [mem_filter, mem_univ, true_and, mem_erase]
      rw [hfilter, card_erase_of_mem he]
      exact Nat.sub_le_sub_right (hdegree u) 1
    _ = _ := by simp only [sum_const, smul_eq_mul]; exact Nat.mul_comm _ _

theorem scaled_overlap_row_bound (S : E → Finset U) {D : ℕ} {g : ℝ}
    (hg : 0 ≤ g) (hD : 1 ≤ D)
    (hdegree : ∀ u, (univ.filter (fun e => u ∈ S e)).card ≤ D) (e : E) :
    (∑ f, g*(overlap S e f : ℝ)) ≤ ((D:ℝ)-1)*(g*(S e).card) := by
  rw [← mul_sum]
  have h := overlap_row_bound S hdegree e
  have hr : (∑ f, (overlap S e f:ℝ)) ≤ ((D:ℝ)-1)*(S e).card := by
    have hh : (∑ f, (overlap S e f:ℝ)) ≤ ((D-1:ℕ):ℝ)*(S e).card := by exact_mod_cast h
    simpa only [Nat.cast_sub hD, Nat.cast_one] using hh
  nlinarith only [mul_le_mul_of_nonneg_left hr hg]

theorem selected_mass_bound (S : E → Finset U) (a : E → ℝ) {g : ℝ} (hg : 0 ≤ g)
    (ω : E → Bool) :
    (∑ e, a e*CountStatistic.bit ω e)-g*((univ.filter (fun e => ω e=true)).biUnion S).card ≤
      CountStatistic.statistic (fun e => a e-g*(S e).card)
        (fun e f => g*(overlap S e f:ℝ)) ω := by
  let T := univ.filter (fun e => ω e=true)
  have heq : ∀ (f : E → ℝ), (∑ e, f e*CountStatistic.bit ω e)=∑ e ∈ T, f e := by
    intro f
    dsimp only [T]
    rw [sum_filter]
    apply sum_congr rfl
    intro e _
    unfold CountStatistic.bit
    split_ifs <;> simp
  have hquad : (∑ e, ∑ f, g*(overlap S e f:ℝ)*CountStatistic.bit ω e*CountStatistic.bit ω f)=
      g*∑ e ∈ T, ∑ f ∈ T, (overlap S e f:ℝ) := by
    simp_rw [heq]
    simp only [← sum_mul]
    rw [heq]
    simp only [mul_sum]
  have hbase : 2*(∑ e ∈ T, ((S e).card:ℝ)) ≤
      2*((T.biUnion S).card:ℝ)+(∑ e ∈ T, ∑ f ∈ T, (overlap S e f:ℝ)) := by
    exact_mod_cast truncated_union S T
  unfold CountStatistic.statistic
  rw [hquad, heq, heq]
  simp only [sum_sub_distrib, ← mul_sum]
  nlinarith only [mul_le_mul_of_nonneg_left hbase hg]

end MetricKMedian.CountGeometry
end
end

end OAI
