import OAI.NumberTheory.JointDickman.Counting.LagSquareSum

namespace OAI

/-! # Summing a nonnegative error over lags in a finite block -/
namespace JointDickman
open Finset Classical

private theorem forward_lag_sum {M : ℕ} (i : Fin M) (T : ℕ) (E : ℕ → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ k : Fin M, if i < k ∧ k.val-i.val < T then E (k.val-i.val) else 0) ≤
      ∑ j ∈ Ioc 0 T, E j := by
  let I : Finset (Fin M) := univ.filter (fun k => i < k ∧ k.val-i.val < T)
  have hinj : Set.InjOn (fun k : Fin M => k.val-i.val) I := by
    intro k hk l hl he
    have hk' : i.val < k.val := (mem_filter.mp hk).2.1
    have hl' : i.val < l.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    dsimp only at he
    omega
  have hsub : I.image (fun k => k.val-i.val) ⊆ Ioc 0 T := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk := (mem_filter.mp hk).2
    have hik : i.val < k.val := hk.1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ I, E (k.val-i.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => k.val-i.val), E j := (sum_image (f := E) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hE j)

private theorem backward_lag_sum {M : ℕ} (i : Fin M) (T : ℕ) (E : ℕ → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ k : Fin M, if k < i ∧ i.val-k.val < T then E (i.val-k.val) else 0) ≤
      ∑ j ∈ Ioc 0 T, E j := by
  let I : Finset (Fin M) := univ.filter (fun k => k < i ∧ i.val-k.val < T)
  have hinj : Set.InjOn (fun k : Fin M => i.val-k.val) I := by
    intro k hk l hl he
    have hk' : k.val < i.val := (mem_filter.mp hk).2.1
    have hl' : l.val < i.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    dsimp only at he
    omega
  have hsub : I.image (fun k => i.val-k.val) ⊆ Ioc 0 T := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk := (mem_filter.mp hk).2
    have hik : k.val < i.val := hk.1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ I, E (i.val-k.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => i.val-k.val), E j := (sum_image (f := E) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hE j)

theorem distance_lag_sum {M : ℕ} (i : Fin M) (T : ℕ) (E : ℕ → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
      E (Nat.dist i.val k.val) else 0) ≤ 2*∑ j ∈ Ioc 0 T, E j := by
  have he (k : Fin M) :
      (if i ≠ k ∧ Nat.dist i.val k.val < T then E (Nat.dist i.val k.val) else 0) =
      (if i < k ∧ k.val-i.val < T then E (k.val-i.val) else 0) +
      (if k < i ∧ i.val-k.val < T then E (i.val-k.val) else 0) := by
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le,Nat.dist_eq_sub_of_le h.le]
    · simp
    · simp [h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le,Nat.dist_eq_sub_of_le_right h.le]
  simp_rw [he]
  rw [sum_add_distrib]
  linarith [forward_lag_sum i T E hE,backward_lag_sum i T E hE]

end JointDickman

end OAI
