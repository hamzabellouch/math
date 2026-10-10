import OAI.Analysis.TriangularHilbert.IntMax

namespace OAI

universe uκ

section
namespace TriangularHilbert
open scoped BigOperators

lemma descending_layer_identity (g : ℕ → ℝ) (k N : ℕ) (hk : k ≤ N) :
    g k = g N + ∑ r ∈ Finset.range N, if k ≤ r then g r-g (r+1) else 0 := by
  induction N with
  | zero =>
    have he : k = 0 := by omega
    subst k
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hkN : k ≤ N
    · rw [ite_eq_left hkN]
      linarith [ih hkN]
    · have he : k = N+1 := by omega
      subst k
      have hs : (∑ r ∈ Finset.range N, if N+1 ≤ r then g r-g (r+1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        rw [ite_eq_right (by have := Finset.mem_range.mp hr; omega)]
      rw [hs,ite_eq_right (by omega)]
      ring

lemma weighted_prefix_identity {κ : Type uκ} (s : Finset κ) (d : κ → ℕ) (a : κ → ℝ)
    (g : ℕ → ℝ) (N : ℕ) (hd : ∀ i ∈ s, d i ≤ N) :
    (∑ i ∈ s, a i*g (d i)) = g N*(∑ i ∈ s, a i) +
      ∑ r ∈ Finset.range N, (g r-g (r+1)) * ∑ i ∈ s.filter (fun i => d i ≤ r), a i := by
  classical
  calc
    _ = ∑ i ∈ s, a i*(g N+∑ r ∈ Finset.range N, if d i ≤ r then g r-g (r+1) else 0) :=
      Finset.sum_congr rfl (fun i hi => congrArg (a i*·) (descending_layer_identity g (d i) N (hd i hi)))
    _ = g N*(∑ i ∈ s, a i) + ∑ r ∈ Finset.range N, ∑ i ∈ s, a i*(if d i ≤ r then g r-g (r+1) else 0) := by
      simp_rw [mul_add,Finset.mul_sum]
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      congr 1
      simp_rw [mul_comm (g N)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring

lemma weighted_prefix_le {κ : Type uκ} (s : Finset κ) (d : κ → ℕ) (a b : κ → ℝ)
    (g : ℕ → ℝ) (N : ℕ) (hd : ∀ i ∈ s, d i ≤ N) (hg : 0 ≤ g N)
    (hdec : ∀ r < N, g (r+1) ≤ g r)
    (hp : ∀ r ≤ N, (∑ i ∈ s.filter (fun i => d i ≤ r), a i) ≤ ∑ i ∈ s.filter (fun i => d i ≤ r), b i) :
    (∑ i ∈ s, a i*g (d i)) ≤ ∑ i ∈ s, b i*g (d i) := by
  classical
  rw [weighted_prefix_identity s d a g N hd,weighted_prefix_identity s d b g N hd]
  apply add_le_add
  · have he : s.filter (fun i => d i ≤ N) = s := Finset.filter_eq_self.mpr hd
    have ht := hp N le_rfl
    rw [he] at ht
    exact mul_le_mul_of_nonneg_left ht hg
  · exact Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left
      (hp r (Finset.mem_range.mp hr).le) (sub_nonneg.mpr (hdec r (Finset.mem_range.mp hr))))
end TriangularHilbert
end

end OAI
