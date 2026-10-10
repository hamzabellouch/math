import OAI.Analysis.Laughlin.FourBody.WeightedReadout

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

private theorem symmetric_pair_sum {I M : Type*} [Fintype I] [LinearOrder I]
    [AddCommGroup M] (F : I → I → M) (hF : ∀ i j, F j i=F i j) (h0 : ∀ i, F i i=0) :
    (∑ i, ∑ j, F i j) = (∑ i, ∑ j, if i < j then F i j else 0) +
      (∑ i, ∑ j, if i < j then F i j else 0) := by
  have he (i j : I) : F i j = (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [h0]
    · simp [h,not_lt_of_gt h,hF]
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : I => if j < i then F j i else 0)]

theorem limitFourEnd_swap (Q p : ℕ) (j k : Fin (Q+1)) (x : Space Q) :
    limitFourEnd Q p k j x = -limitFourEnd Q p j k x := by
  have h := LinearMap.congr_fun (annihilate_anticommute j k) (limitPairEnd Q p x)
  simpa only [limitFourEnd,Module.End.mul_apply,LinearMap.add_apply,LinearMap.zero_apply,
    add_eq_zero_iff_eq_neg] using h

theorem weightedFourEnd_ordered (Q p : ℕ) (S : ℕ → ℕ → ℝ)
    (hS : ∀ j k, S k j = -S j k) (x : Space Q) :
    weightedFourEnd Q p (fun j k => S j.val k.val) x = ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
      if j<k then (S j.val k.val : ℂ) • limitFourEnd Q p j k x else 0 := by
  let F := fun j k : Fin (Q+1) => ((S j.val k.val / 2 : ℝ) : ℂ) • limitFourEnd Q p j k x
  have hf : ∀ j k, F k j=F j k := by
    intro j k
    simp [F,hS j.val k.val,limitFourEnd_swap Q p j k x,neg_div]
  have h0 : ∀ j, F j j=0 := by
    intro j
    have hs := hS j.val j.val
    have hz : S j.val j.val=0 := by linarith
    simp [F,hz]
  have h := symmetric_pair_sum F hf h0
  simp only [weightedFourEnd,LinearMap.sum_apply,LinearMap.smul_apply]
  change (∑ j, ∑ k, F j k) = _
  rw [h,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j hj
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k hk
  split_ifs
  · simp only [F,← add_smul]
    congr 1
    push_cast
    ring
  · simp

end Laughlin.Fock

end OAI
