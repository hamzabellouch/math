import OAI.NumberTheory.JointDickman.Probability.CandidateSiteMean

namespace OAI

/-! # The square-moment lag sum for the finite-feature envelope -/
namespace JointDickman
open Finset Classical

private theorem forward_lag_square_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i < k ∧ k.val-i.val < T then (singularFactor 24 (k.val-i.val))^2 else 0) ≤
      Real.exp 1200*(T : ℝ) := by
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
    _ = ∑ k ∈ I, (singularFactor 24 (k.val-i.val))^2 := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => k.val-i.val), (singularFactor 24 j)^2 := (sum_image (f := fun j : ℕ => (singularFactor 24 j)^2) hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, (singularFactor 24 j)^2 := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => sq_nonneg _)
    _ ≤ _ := by
      convert singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 2 T using 1
      norm_num

private theorem backward_lag_square_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if k < i ∧ i.val-k.val < T then (singularFactor 24 (i.val-k.val))^2 else 0) ≤
      Real.exp 1200*(T : ℝ) := by
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
    _ = ∑ k ∈ I, (singularFactor 24 (i.val-k.val))^2 := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => i.val-k.val), (singularFactor 24 j)^2 := (sum_image (f := fun j : ℕ => (singularFactor 24 j)^2) hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, (singularFactor 24 j)^2 := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => sq_nonneg _)
    _ ≤ _ := by
      convert singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 2 T using 1
      norm_num

theorem distance_lag_square_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
      (singularFactor 24 (Nat.dist i.val k.val))^2 else 0) ≤ 2*Real.exp 1200*(T : ℝ) := by
  have he (k : Fin M) :
      (if i ≠ k ∧ Nat.dist i.val k.val < T then (singularFactor 24 (Nat.dist i.val k.val))^2 else 0) =
      (if i < k ∧ k.val-i.val < T then (singularFactor 24 (k.val-i.val))^2 else 0) +
      (if k < i ∧ i.val-k.val < T then (singularFactor 24 (i.val-k.val))^2 else 0) := by
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le,Nat.dist_eq_sub_of_le h.le]
    · simp
    · simp [h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le,Nat.dist_eq_sub_of_le_right h.le]
  simp_rw [he]
  rw [sum_add_distrib]
  have hf := forward_lag_square_sum i T
  have hb := backward_lag_square_sum i T
  linarith

end JointDickman

end OAI
