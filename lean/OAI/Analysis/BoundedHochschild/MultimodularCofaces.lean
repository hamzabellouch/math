import OAI.Analysis.BoundedHochschild.MultimodularMergeBalance

namespace OAI

/-! The elementary Hochschild cofaces preserve module identities. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma MultimodularAt.add {n : ℕ} {f g : Cochain M (n + 1)} {r : M}
    (hf : MultimodularAt f r) (hg : MultimodularAt g r) : MultimodularAt (f + g) r := by
  constructor
  · intro x
    simp only [add_apply, hf.left, hg.left, mul_add]
  · intro x
    simp only [add_apply, hf.right, hg.right, add_mul]
  · intro x j
    simp only [add_apply, hf.balance x j, hg.balance x j]

lemma MultimodularAt.smul {n : ℕ} {f : Cochain M (n + 1)} {r : M}
    (hf : MultimodularAt f r) (z : ℂ) : MultimodularAt (z • f) r := by
  constructor
  · intro x
    simp only [smul_apply, hf.left, mul_smul_comm]
  · intro x
    simp only [smul_apply, hf.right, smul_mul_assoc]
  · intro x j
    simp only [smul_apply, hf.balance x j]

lemma MultimodularAt.zero {n : ℕ} (r : M) : MultimodularAt (0 : Cochain M (n + 1)) r := by
  constructor <;> intros <;> simp

lemma MultimodularAt.sum {I : Type*} {n : ℕ} (s : Finset I) (f : I → Cochain M (n + 1)) (r : M)
    (hf : ∀ i ∈ s, MultimodularAt (f i) r) : MultimodularAt (∑ i ∈ s, f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MultimodularAt.zero (n := n) r
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma multimodularAt_middleCoboundary {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) (k : Fin (n + 1)) : MultimodularAt (middleCoboundary f k) r := by
  constructor
  · intro x
    simp only [middleCoboundary_apply, mergeInputs_left_module]
    exact hf.left _
  · intro x
    simp only [middleCoboundary_apply, mergeInputs_right_module]
    exact hf.right _
  · intro x j
    simp only [middleCoboundary_apply]
    by_cases hkj : k = j
    · subst k
      rw [mergeInputs_balance_at]
    · rcases lt_or_gt_of_ne hkj with hk | hk
      · let p : Fin n := ⟨j.val - 1, by omega⟩
        have hp : p.val + 1 = j.val := by dsimp [p]; omega
        rw [merge_balance_before_left x k j p hk hp,
          merge_balance_before_right x k j p hk hp]
        exact hf.balance _ p
      · let p : Fin n := ⟨j.val, by omega⟩
        have hp : p.val = j.val := rfl
        rw [merge_balance_after_left x k j p hk hp,
          merge_balance_after_right x k j p hk hp]
        exact hf.balance _ p

end BoundedHochschild.KadisonRingrose

end

end OAI
